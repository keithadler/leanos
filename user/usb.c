/* The USB driver: keyboards and mice on the Pi 4's DWC2 host controller (the USB-C port;
   on QEMU, where `-device usb-kbd` and `usb-mouse` plug in).

   It holds the controller (capability 6), its interrupt (5), and may send to the display
   server with badge 17, as the input driver does with the UART: keys, and a mouse pointer
   it keeps itself from the mouse's movements. It never touches the controller's registers
   directly. Every read and write goes through the kernel (`usb`), which lets a transfer
   start only when its whole DMA range is in this driver's own memory (LeanOS/Proofs.lean:
   `usb_dma_own_memory`). A driver bug, or a hostile one, cannot aim the controller at
   anyone else's memory.

   What it knows: the controller in host mode with buffer DMA; control transfers; hubs
   (their ports powered, reset and enumerated, no hot-plug after that); HID keyboards and
   mice in the boot protocol, read by interrupt transfers. */
#include "lib.h"

#define EP 4
#define IRQ 5
#define USB 6
#define SPARE 3
#define DMA_PAGE 64
/* The spare run's first frame, physically: the frame pool starts at 0x04000000 and slot 17's
   frames at 256 x 17; its spare run is frames 28 on. The kernel checks every transfer
   against the frames this driver holds, so a wrong address here is refused, not obeyed. */
#define DMA_PA (0x04000000UL + (256UL * 17 + 28) * 4096)

enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4 };

/* Registers */
#define GAHBCFG 0x008
#define GUSBCFG 0x00C
#define GRSTCTL 0x010
#define GINTSTS 0x014
#define GINTMSK 0x018
#define GRXFSIZ 0x024
#define GNPTXFSIZ 0x028
#define GSNPSID 0x040
#define HPTXFSIZ 0x100
#define HAINT 0x414
#define HAINTMSK 0x418
#define HPRT0 0x440
#define HCCHAR(n) (0x500 + 0x20 * (n))
#define HCINT(n) (0x508 + 0x20 * (n))
#define HCINTMSK(n) (0x50C + 0x20 * (n))
#define HCTSIZ(n) (0x510 + 0x20 * (n))
#define HCDMA(n) (0x514 + 0x20 * (n))
#define PCGCCTL 0xE00

#define HPRT0_W1C 0x2E        /* connect detected, enabled, enable changed, overcurrent changed */
enum { XFERCOMPL = 1, CHHLTD = 2, STALL = 8, NAK = 16, XACTERR = 128, BBLERR = 256, DATATGLERR = 1024 };
enum { PID_DATA0 = 0, PID_DATA1 = 2, PID_SETUP = 3 };
enum { CONTROL = 0, INTERRUPT = 3 };

#define MAX_DEV 8
#define MAX_HID 4

struct dev { int addr, mps0, ls; };
struct hid { struct dev d; int kind, ep, mps, ch, pid, idle; unsigned char *buf; };  /* kind 1 keyboard, 2 mouse */

struct usb {
    struct line l;
    unsigned char *dma;          /* the DMA area: the spare run, mapped */
    int next_addr, nhid, keyboards, mice;
    struct hid hid[MAX_HID];
    unsigned char prev[8];       /* the keyboard's last report */
    int mx, my, buttons;
};

static u64 rd(u64 reg) { return sys(SYS_USB, USB, 0, reg, 0, 0).x[1]; }
static u64 wr(u64 reg, u64 v) { return sys(SYS_USB, USB, 1, reg, v, 0).status; }
static u64 pa(const void *va) { return DMA_PA + ((u64)va - PAGE(DMA_PAGE)); }
static void event(u64 type, u64 a, u64 b) { sys(SYS_SEND, ENDPOINT, type, a, b, 0); }
static void say(struct usb *u) { put_s(&u->l, "\n"); flush(&u->l); }

/* Start one transfer on channel `ch` (the kernel checks `buf` .. `buf + len` is ours). */
static u64 start(int ch, const struct dev *d, int ep, int in, int type, int mps, int pid, void *buf, int len) {
    int pkts = len ? (len + mps - 1) / mps : 1;
    wr(HCINT(ch), 0x7ff);
    wr(HCINTMSK(ch), XFERCOMPL | CHHLTD | STALL | XACTERR | BBLERR | DATATGLERR);
    wr(HCDMA(ch), pa(buf));
    wr(HCTSIZ(ch), (u64)len | (u64)pkts << 19 | (u64)pid << 29);
    u64 chr = (u64)mps | (u64)ep << 11 | (u64)in << 15 | (u64)d->ls << 17 | (u64)type << 18 | 1UL << 20 |
              (u64)d->addr << 22 | 1UL << 31;
    return wr(HCCHAR(ch), chr);
}

/* Run a transfer to the end: the bytes moved, or -1. */
static int xfer(const struct dev *d, int ep, int in, int type, int mps, int pid, void *buf, int len) {
    if (start(0, d, ep, in, type, mps, pid, buf, len) != OK) return -1;
    for (int i = 0; i < 5000; i++) {
        u64 st = rd(HCINT(0));
        if (st & XFERCOMPL) {
            u64 left = rd(HCTSIZ(0)) & 0x7ffff;
            wr(HCINT(0), st);
            return in ? len - (int)left : len;
        }
        if (st & (STALL | XACTERR | BBLERR | DATATGLERR)) { wr(HCINT(0), st); return -1; }
        if ((st & CHHLTD) && !(st & XFERCOMPL)) { wr(HCINT(0), st); return -1; }
        sys0(SYS_YIELD);
    }
    return -1;
}

/* A control transfer: setup, data (if any), status. The bytes of data moved, or -1. */
static int control(struct usb *u, const struct dev *d, int type, int req, int value, int index, int len) {
    unsigned char *setup = u->dma, *data = u->dma + 64;
    setup[0] = (unsigned char)type;
    setup[1] = (unsigned char)req;
    setup[2] = (unsigned char)value;
    setup[3] = (unsigned char)(value >> 8);
    setup[4] = (unsigned char)index;
    setup[5] = (unsigned char)(index >> 8);
    setup[6] = (unsigned char)len;
    setup[7] = (unsigned char)(len >> 8);
    if (xfer(d, 0, 0, CONTROL, d->mps0, PID_SETUP, setup, 8) < 0) return -1;
    int in = type & 0x80, got = 0;
    if (len) {
        got = xfer(d, 0, in ? 1 : 0, CONTROL, d->mps0, PID_DATA1, data, len);
        if (got < 0) return -1;
    }
    if (xfer(d, 0, in ? 0 : 1, CONTROL, d->mps0, PID_DATA1, data + 512, 0) < 0) return -1;
    return got;
}

static int get_descriptor(struct usb *u, const struct dev *d, int type, int len) {
    return control(u, d, 0x80, 6, type << 8, 0, len);
}

static void add_hid(struct usb *u, const struct dev *d, int kind, int iface, int ep, int mps) {
    if (u->nhid >= MAX_HID) return;
    control(u, d, 0x21, 0x0B, 0, iface, 0);          /* SET_PROTOCOL: boot */
    if (kind == 1) control(u, d, 0x21, 0x0A, 0, iface, 0);   /* SET_IDLE: only on change */
    struct hid *h = &u->hid[u->nhid];
    h->d = *d;
    h->kind = kind;
    h->ep = ep;
    h->mps = mps > 64 ? 64 : mps;
    h->ch = 1 + u->nhid;
    h->pid = PID_DATA0;
    h->idle = 0;
    h->buf = u->dma + 2048 + 256 * u->nhid;
    u->nhid++;
    if (kind == 1) u->keyboards++;
    else u->mice++;
    put_s(&u->l, "usb: device ");
    put_dec(&u->l, (u64)d->addr);
    put_s(&u->l, kind == 1 ? ": keyboard" : ": mouse");
    say(u);
}

static void enumerate(struct usb *u, int ls, int depth);

static void hub(struct usb *u, const struct dev *d, int depth) {
    unsigned char *b = u->dma + 64;
    if (control(u, d, 0xA0, 6, 0x29 << 8, 0, 9) < 7) return;        /* the hub's class descriptor */
    int ports = b[2], delay = b[5] * 2;
    put_s(&u->l, "usb: device ");
    put_dec(&u->l, (u64)d->addr);
    put_s(&u->l, ": hub, ");
    put_dec(&u->l, (u64)ports);
    put_s(&u->l, " ports");
    say(u);
    for (int p = 1; p <= ports; p++) control(u, d, 0x23, 3, 8, p, 0);          /* PORT_POWER */
    sleep_ms((u64)(delay < 20 ? 20 : delay));
    for (int p = 1; p <= ports; p++) {
        if (control(u, d, 0xA3, 0, 0, p, 4) < 4) continue;                      /* GET_STATUS */
        if (!(b[0] & 1)) continue;                                              /* nothing there */
        control(u, d, 0x23, 3, 4, p, 0);                                        /* PORT_RESET */
        int ok = 0;
        for (int i = 0; i < 20 && !ok; i++) {
            sleep_ms(10);
            if (control(u, d, 0xA3, 0, 0, p, 4) == 4 && !(b[0] & 0x10) && (b[0] & 2)) ok = 1;
        }
        if (!ok) continue;
        int child_ls = (b[1] >> 1) & 1;                                         /* bit 9: low speed */
        control(u, d, 0x23, 1, 20, p, 0);                                       /* clear C_PORT_RESET */
        control(u, d, 0x23, 1, 16, p, 0);                                       /* clear C_PORT_CONNECTION */
        sleep_ms(10);
        enumerate(u, child_ls, depth + 1);
    }
}

/* The device at address 0 (just reset): give it an address, read what it is, configure it,
   and look for hubs and boot keyboards and mice in it. */
static void enumerate(struct usb *u, int ls, int depth) {
    if (depth > 4 || u->next_addr >= MAX_DEV + 1) return;
    unsigned char *b = u->dma + 64;
    struct dev d = {0, 8, ls};
    if (get_descriptor(u, &d, 1, 8) < 8) { put_s(&u->l, "usb: a device did not answer"); say(u); return; }
    d.mps0 = b[7] ? b[7] : 8;
    int addr = u->next_addr++;
    if (control(u, &d, 0x00, 5, addr, 0, 0) < 0) return;                        /* SET_ADDRESS */
    sleep_ms(10);
    d.addr = addr;
    if (get_descriptor(u, &d, 1, 18) < 18) return;
    int cls = b[4];
    if (get_descriptor(u, &d, 2, 9) < 9) return;
    int total = b[2] | b[3] << 8;
    if (total > 400) total = 400;
    if (get_descriptor(u, &d, 2, total) < total) return;
    unsigned char cfg[400];
    for (int i = 0; i < total; i++) cfg[i] = b[i];
    if (control(u, &d, 0x00, 9, cfg[5], 0, 0) < 0) return;                      /* SET_CONFIGURATION */
    if (cls == 9) { hub(u, &d, depth); return; }
    /* interfaces and their endpoints */
    int iface = -1, kind = 0;
    for (int i = 0; i + 2 <= total && cfg[i] >= 2; i += cfg[i]) {
        if (cfg[i + 1] == 4 && i + 9 <= total) {
            iface = cfg[i + 2];
            kind = 0;
            if (cfg[i + 5] == 9) { hub(u, &d, depth); return; }
            if (cfg[i + 5] == 3 && cfg[i + 6] == 1 && (cfg[i + 7] == 1 || cfg[i + 7] == 2)) kind = cfg[i + 7];
        } else if (cfg[i + 1] == 5 && i + 7 <= total && kind && (cfg[i + 2] & 0x80) && (cfg[i + 3] & 3) == 3) {
            add_hid(u, &d, kind, iface, cfg[i + 2] & 15, cfg[i + 4] | cfg[i + 5] << 8);
            kind = 0;
        }
    }
}

/* HID usage to a key leanos knows: ASCII, or 128-131 for the arrows. 0 for anything else. */
static int key_of(int usage, int shift) {
    static const char plain[] = "abcdefghijklmnopqrstuvwxyz1234567890\r\x1b\b\t -=[]\\#;'`,./";
    static const char shifted[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ!@#$%^&*()\r\x1b\b\t _+{}|~:\"~<>?";
    if (usage >= 4 && usage <= 0x38) return (shift ? shifted : plain)[usage - 4];
    if (usage == 0x52) return 128;   /* up */
    if (usage == 0x51) return 129;   /* down */
    if (usage == 0x4F) return 130;   /* right */
    if (usage == 0x50) return 131;   /* left */
    return 0;
}

static void keyboard(struct usb *u, const unsigned char *r, int n) {
    if (n < 8) return;
    int shift = (r[0] & 0x22) != 0;
    for (int i = 2; i < 8; i++) {
        int k = r[i], seen = 0;
        if (k < 4) continue;
        for (int j = 2; j < 8; j++) if (u->prev[j] == k) seen = 1;
        if (seen) continue;
        int c = key_of(k, shift);
        if (c == '\b') c = 127;
        if (c) event(EV_KEY, (u64)c, 0);
    }
    for (int i = 0; i < 8; i++) u->prev[i] = r[i];
}

static void mouse(struct usb *u, const unsigned char *r, int n) {
    if (n < 3) return;
    int dx = (signed char)r[1], dy = (signed char)r[2];
    if (dx || dy) {
        u->mx += dx;
        u->my += dy;
        if (u->mx < 0) u->mx = 0;
        if (u->mx > 1023) u->mx = 1023;
        if (u->my < 0) u->my = 0;
        if (u->my > 599) u->my = 599;
        event(EV_MOVE, (u64)u->mx, (u64)u->my);
    }
    int left = r[0] & 1;
    if (left != u->buttons) {
        u->buttons = left;
        event(left ? EV_DOWN : EV_UP, (u64)u->mx, (u64)u->my);
    }
}

static void arm(struct hid *h) {
    start(h->ch, &h->d, h->ep, 1, INTERRUPT, h->mps, h->pid, h->buf, h->mps);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct usb *u = (struct usb *)DATA;
    u->l.n = 0;
    u->next_addr = 1;
    u->nhid = u->keyboards = u->mice = u->buttons = 0;
    u->mx = 512;
    u->my = 300;
    for (int i = 0; i < 8; i++) u->prev[i] = 0;
    if (sys2(SYS_MAP, SPARE, DMA_PAGE).status != OK) { put_s(&u->l, "usb: cannot map its memory"); say(u); exit_task(); }
    u->dma = (unsigned char *)PAGE(DMA_PAGE);

    u64 id = rd(GSNPSID);
    if ((id >> 16) != 0x4F54) {
        put_s(&u->l, "usb: no DWC2 controller (id ");
        put_hex(&u->l, id);
        put_s(&u->l, ")");
        say(u);
        exit_task();
    }
    /* Host mode, buffer DMA, the core reset, the FIFOs sized, the port powered. */
    wr(PCGCCTL, 0);
    wr(GRSTCTL, 1);
    for (int i = 0; i < 100 && (rd(GRSTCTL) & 1); i++) sleep_ms(1);
    wr(GUSBCFG, (rd(GUSBCFG) & ~(1UL << 30)) | 1UL << 29);
    sleep_ms(50);
    wr(GRXFSIZ, 1024);
    wr(GNPTXFSIZ, 1024UL << 16 | 1024);
    wr(HPTXFSIZ, 1024UL << 16 | 2048);
    wr(GAHBCFG, 1 << 5 | 1);                          /* DMA on, interrupts on */
    wr(GINTMSK, 1UL << 25);                           /* host channels */
    wr(HAINTMSK, 0xff);
    wr(HPRT0, (rd(HPRT0) & ~(u64)HPRT0_W1C) | 1 << 12);   /* port power */
    put_s(&u->l, "usb: DWC2 ");
    put_hex(&u->l, id & 0xffff);
    put_s(&u->l, " in host mode, DMA checked by the kernel");
    say(u);

    /* What the kernel must refuse, tried for real: a transfer aimed at the display server's
       memory (its code, frame 256 on), turning on descriptor DMA, forcing device mode. */
    wr(HCDMA(7), 0x04000000UL + 256UL * 4096);
    wr(HCTSIZ(7), 8 | 1UL << 19);
    u64 aimed = wr(HCCHAR(7), 8 | 1UL << 15 | 1UL << 31);
    u64 desc = wr(0x400, rd(0x400) | 1UL << 23);
    u64 dev = wr(GUSBCFG, rd(GUSBCFG) | 1UL << 30);
    put_s(&u->l, aimed != OK && desc != OK && dev != OK
                     ? "usb: refused, as proved: DMA into the display's memory, descriptor DMA, device mode"
                     : "usb: the kernel let a dangerous request through");
    say(u);

    int told = 0;
    while (!(rd(HPRT0) & 1)) {
        if (!told) { put_s(&u->l, "usb: nothing plugged in yet"); say(u); told = 1; }
        sleep_ms(250);
    }
    sleep_ms(100);
    wr(HPRT0, (rd(HPRT0) & ~(u64)HPRT0_W1C) | 1 << 8);    /* reset */
    sleep_ms(60);
    wr(HPRT0, rd(HPRT0) & ~(u64)HPRT0_W1C & ~(1UL << 8));
    for (int i = 0; i < 50 && !(rd(HPRT0) & 4); i++) sleep_ms(10);
    u64 port = rd(HPRT0);
    wr(HPRT0, (port & ~(u64)HPRT0_W1C) | (port & HPRT0_W1C & ~4UL));   /* acknowledge the changes */
    int speed = (int)(port >> 17) & 3;
    put_s(&u->l, speed == 2 ? "usb: port: a low-speed device" : speed == 1 ? "usb: port: a full-speed device"
                                                                         : "usb: port: a high-speed device");
    say(u);
    sleep_ms(20);
    enumerate(u, speed == 2, 0);

    put_s(&u->l, "usb: ready, ");
    put_dec(&u->l, (u64)u->keyboards);
    put_s(&u->l, u->keyboards == 1 ? " keyboard, " : " keyboards, ");
    put_dec(&u->l, (u64)u->mice);
    put_s(&u->l, u->mice == 1 ? " mouse" : " mice");
    say(u);
    if (!u->nhid) exit_task();

    /* Each device is asked for a report; one with nothing to say answers NAK and its channel
       halts, and is asked again a polling interval later (8 ms, what keyboards and mice ask
       for), not at once: a channel re-armed on every NAK would keep the machine busy. */
    for (int i = 0; i < u->nhid; i++) arm(&u->hid[i]);
    for (;;) {
        sys1(SYS_IRQWAIT, IRQ);
        int later = 0;
        u64 g = rd(GINTSTS);
        if (g & (1UL << 25)) {
            u64 chans = rd(HAINT);
            for (int i = 0; i < u->nhid; i++) {
                struct hid *h = &u->hid[i];
                if (!(chans & (1UL << h->ch))) continue;
                u64 st = rd(HCINT(h->ch));
                wr(HCINT(h->ch), st);
                if (st & XFERCOMPL) {
                    u64 t = rd(HCTSIZ(h->ch));
                    int n = h->mps - (int)(t & 0x7ffff);
                    h->pid = (int)(t >> 29) & 3;
                    if (h->kind == 1) keyboard(u, h->buf, n);
                    else mouse(u, h->buf, n);
                    arm(h);
                } else {
                    h->idle = 1;
                    later = 1;
                }
            }
        }
        sys1(SYS_IRQACK, IRQ);
        if (later) {
            sleep_ms(8);
            for (int i = 0; i < u->nhid; i++)
                if (u->hid[i].idle) { u->hid[i].idle = 0; arm(&u->hid[i]); }
        }
    }
}
