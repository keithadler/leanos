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
   mice in the boot protocol, and touchscreens and tablets (absolute pointers, found by
   reading their report descriptors), read by interrupt transfers. */
#include "lib.h"
#define NET_SERVER
#include "net.h"
#include "netstack.h"
#include "date.h"

#define EP 4
#define IRQ 5
#define USB 6
#define NETEP 7              /* endpoint 2: the network service, which Terminal calls */
#define WALL 8               /* the time of day: this driver says what it is (setwall) */
#define SPARE 3
#define REQ_PAGE 3000        /* where a request's buffer is mapped */
/* In the spare run: control transfers (0-1023), keyboard and mouse reports (2048-3071),
   a received frame (page 1), a frame to send (page 2), the body of the last GET (pages 16
   on, 512 KiB). */
#define RX_OFF 4096
#define TX_OFF 8192
#define BODY_OFF (16 * 4096)
#define NET_IN_CH 5
#define NET_OUT_CH 6
#define BULK 2
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
/* Where an absolute pointer's report keeps what matters: a field is a bit offset and size,
   with the logical range for X and Y. */
struct field { int off, size, min, max; };
struct abs { int id, has_btn; struct field x, y, btn; };
/* kind 1 keyboard, 2 mouse, 3 touchscreen or tablet */
struct hid { struct dev d; int kind, ep, mps, ch, pid, idle; unsigned char *buf; struct abs a; };

struct usb {
    struct line l;
    unsigned char *dma;          /* the DMA area: the spare run, mapped */
    int next_addr, nhid, keyboards, mice, touch;
    struct hid hid[MAX_HID];
    unsigned char prev[8];       /* the keyboard's last report */
    int mx, my, buttons;
    /* the network adapter (CDC Ethernet), if one is plugged in */
    int has_net, net_in, net_out, net_mps, net_in_pid, net_out_pid, net_armed;
    struct dev netdev;
    u64 body_len;
    int body_status;
    u64 body_owner;              /* the badge that fetched it: only it may read it */
    struct { u64 h0, h1; int on; } allow[6];   /* the program allowed in each open slot */
    struct net net;
};

#define U ((struct usb *)DATA)

static void put_hex2(struct line *l, unsigned v) {
    char c[3] = {"0123456789abcdef"[(v >> 4) & 15], "0123456789abcdef"[v & 15], 0};
    put_s(l, c);
}

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

/* A HID report descriptor: find the first absolute X and Y on the generic desktop page,
   and the first button 1 or digitizer tip switch, in the same report. Returns 1 if there
   are X and Y. (Short items only; a long item ends the walk.) */
static int parse_report(const unsigned char *d, int n, struct abs *a) {
    int page = 0, size = 0, count = 0, id = 0, lmin = 0, lmax = 0;
    int usages[16], nu = 0, umin = -1, umax = -1;
    int off[16] = {0};                   /* the bit offset so far, per report ID (low 4 bits) */
    int found = 0;
    a->has_btn = 0;
    a->id = -1;
    for (int i = 0; i < n;) {
        int b = d[i], sz = b & 3, type = (b >> 2) & 3, tag = b >> 4;
        if (b == 0xFE) break;
        if (sz == 3) sz = 4;
        if (i + 1 + sz > n) break;
        unsigned v = 0;
        for (int k = 0; k < sz; k++) v |= (unsigned)d[i + 1 + k] << (8 * k);
        int sv = sz == 1 ? (signed char)v : sz == 2 ? (short)v : (int)v;
        i += 1 + sz;
        if (type == 1) {                                   /* global */
            if (tag == 0) page = (int)v;
            else if (tag == 1) lmin = sv;
            else if (tag == 2) lmax = sz == 4 ? (int)v : sv < lmin ? (int)v : sv;
            else if (tag == 7) size = (int)v;
            else if (tag == 8) id = (int)v;
            else if (tag == 9) count = (int)v;
        } else if (type == 2) {                            /* local */
            if (tag == 0 && nu < 16) usages[nu++] = (int)v;
            else if (tag == 1) umin = (int)v;
            else if (tag == 2) umax = (int)v;
        } else if (type == 0) {                            /* main */
            if (tag == 8) {                                /* input */
                int *o = &off[id & 15];
                for (int k = 0; k < count; k++) {
                    int us = k < nu ? usages[k] : umin >= 0 && umin + k <= umax ? umin + k : nu ? usages[nu - 1] : -1;
                    int upage = us > 0xFFFF ? us >> 16 : page;
                    us &= 0xFFFF;
                    int constant = v & 1, relative = (v >> 2) & 1;
                    struct field f = {*o + k * size, size, lmin, lmax};
                    if (!constant && found < 2 && (a->id < 0 || a->id == id)) {
                        if (upage == 1 && us == 0x30 && !relative && !a->x.size) { a->x = f; a->id = id; found++; }
                        else if (upage == 1 && us == 0x31 && !relative && !a->y.size) { a->y = f; a->id = id; found++; }
                    }
                    if (!constant && !a->has_btn && ((upage == 9 && us == 1) || (upage == 0x0D && us == 0x42)) &&
                        (a->id < 0 || a->id == id)) {
                        a->btn = f;
                        a->has_btn = 1;
                    }
                }
                *o += size * count;
            }
            nu = 0;
            umin = umax = -1;
        }
    }
    return a->x.size && a->y.size;
}

static int bits(const unsigned char *r, int n, struct field f) {
    unsigned v = 0;
    for (int k = 0; k < f.size && k < 32; k++) {
        int bit = f.off + k;
        if (bit / 8 < n && (r[bit / 8] >> (bit % 8) & 1)) v |= 1u << k;
    }
    return (int)v;
}

static void add_hid(struct usb *u, const struct dev *d, int kind, int iface, int ep, int mps) {
    if (u->nhid >= MAX_HID) return;
    struct abs a = {0};
    if (kind == 3) {                                  /* report protocol: read what it sends */
        int len = control(u, d, 0x81, 6, 0x22 << 8, iface, 900);
        if (len <= 0 || !parse_report(u->dma + 64, len, &a)) return;
        control(u, d, 0x21, 0x0A, 0, iface, 0);   /* SET_IDLE: only on change */
    } else control(u, d, 0x21, 0x0B, 0, iface, 0);          /* SET_PROTOCOL: boot */
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
    h->a = a;
    u->nhid++;
    if (kind == 1) u->keyboards++;
    else if (kind == 2) u->mice++;
    else u->touch++;
    put_s(&u->l, "usb: device ");
    put_dec(&u->l, (u64)d->addr);
    put_s(&u->l, kind == 1 ? ": keyboard" : kind == 2 ? ": mouse" : ": touchscreen or tablet");
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
    int cls = b[4], nconf = b[17] ? b[17] : 1;
    /* its configurations: a network adapter may offer several (QEMU's: RNDIS, then CDC
       Ethernet); take the one with CDC Ethernet in it, else the first */
    unsigned char cfg[400];
    int total = 0;
    for (int c = 0; c < nconf && c < 4; c++) {
        if (control(u, &d, 0x80, 6, 2 << 8 | c, 0, 9) < 9) break;
        int len = b[2] | b[3] << 8;
        if (len > 400) len = 400;
        if (control(u, &d, 0x80, 6, 2 << 8 | c, 0, len) < len) break;
        int ecm = 0;
        for (int i = 0; i + 8 < len && b[i] >= 2; i += b[i])
            if (b[i + 1] == 4 && b[i + 5] == 2 && b[i + 6] == 6) ecm = 1;
        if (c == 0 || ecm) { for (int i = 0; i < len; i++) cfg[i] = b[i]; total = len; }
        if (ecm) break;
    }
    if (total < 9) return;
    if (control(u, &d, 0x00, 9, cfg[5], 0, 0) < 0) return;                      /* SET_CONFIGURATION */
    if (cls == 9) { hub(u, &d, depth); return; }
    /* interfaces and their endpoints */
    int iface = -1, kind = 0, data_iface = -1, in_data = 0, mac_string = 0, bin = 0, bout = 0, bmps = 64;
    for (int i = 0; i + 2 <= total && cfg[i] >= 2; i += cfg[i]) {
        if (cfg[i + 1] == 4 && i + 9 <= total) {
            iface = cfg[i + 2];
            kind = 0;
            in_data = cfg[i + 5] == 0x0A && cfg[i + 3] == 1;     /* CDC data, the alternate with endpoints */
            if (in_data) data_iface = iface;
            if (cfg[i + 5] == 9) { hub(u, &d, depth); return; }
            if (cfg[i + 5] == 3 && cfg[i + 6] == 1 && (cfg[i + 7] == 1 || cfg[i + 7] == 2)) kind = cfg[i + 7];
            else if (cfg[i + 5] == 3 && cfg[i + 6] == 0) kind = 3;     /* not boot: maybe absolute */
        } else if (cfg[i + 1] == 0x24 && i + 4 <= total && cfg[i + 2] == 0x0F) {
            mac_string = cfg[i + 3];                             /* CDC Ethernet: its MAC, as a string */
        } else if (cfg[i + 1] == 5 && i + 7 <= total && in_data && (cfg[i + 3] & 3) == BULK) {
            if (cfg[i + 2] & 0x80) bin = cfg[i + 2] & 15;
            else bout = cfg[i + 2] & 15;
            bmps = cfg[i + 4] | cfg[i + 5] << 8;
        } else if (cfg[i + 1] == 5 && i + 7 <= total && kind && (cfg[i + 2] & 0x80) && (cfg[i + 3] & 3) == 3) {
            add_hid(u, &d, kind, iface, cfg[i + 2] & 15, cfg[i + 4] | cfg[i + 5] << 8);
            kind = 0;
        }
    }
    if (data_iface >= 0 && bin && bout && !u->has_net) {
        control(u, &d, 0x01, 11, 1, data_iface, 0);                          /* SET_INTERFACE: alt 1 */
        control(u, &d, 0x21, 0x43, 0x000F, data_iface - 1 < 0 ? 0 : data_iface - 1, 0);   /* the packet filter */
        unsigned char *mac = u->net.mac;
        for (int k = 0; k < 6; k++) mac[k] = (unsigned char)(0x02 + k);
        if (mac_string && control(u, &d, 0x80, 6, 3 << 8 | mac_string, 0x0409, 64) >= 26) {
            for (int k = 0; k < 6; k++) {
                int hv = 0;
                for (int j = 0; j < 2; j++) {
                    char c = (char)b[2 + 2 * (2 * k + j)];
                    hv = hv * 16 + (c >= 'a' ? c - 'a' + 10 : c >= 'A' ? c - 'A' + 10 : c - '0');
                }
                mac[k] = (unsigned char)hv;
            }
        }
        u->has_net = 1;
        u->netdev = d;
        u->net_in = bin;
        u->net_out = bout;
        u->net_mps = bmps > 512 ? 512 : bmps;
        u->net_in_pid = u->net_out_pid = PID_DATA0;
        put_s(&u->l, "usb: device ");
        put_dec(&u->l, (u64)d.addr);
        put_s(&u->l, ": network adapter, ");
        for (int k = 0; k < 6; k++) { if (k) put_s(&u->l, ":"); put_hex2(&u->l, mac[k]); }
        say(u);
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

/* A key with Control held is sent as the serial line sends it: Ctrl+A to Ctrl+Z are bytes 1
   to 26 (Ctrl+C and Ctrl+V are copy and paste, user/display.c). */
static void keyboard(struct usb *u, const unsigned char *r, int n) {
    if (n < 8) return;
    int shift = (r[0] & 0x22) != 0, ctrl = (r[0] & 0x11) != 0;
    for (int i = 2; i < 8; i++) {
        int k = r[i], seen = 0;
        if (k < 4) continue;
        for (int j = 2; j < 8; j++) if (u->prev[j] == k) seen = 1;
        if (seen) continue;
        int c = ctrl ? (k <= 0x1d ? k - 3 : 0) : key_of(k, shift);
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

/* A touchscreen or tablet: where it says, scaled to the screen; touching (or its button)
   is the left button. */
static void absolute(struct usb *u, struct hid *h, const unsigned char *r, int n) {
    struct abs *a = &h->a;
    if (a->id > 0) {
        if (n < 1 || r[0] != a->id) return;
        r++;
        n--;
    }
    int rx = bits(r, n, a->x) , ry = bits(r, n, a->y);
    int wx = a->x.max > a->x.min ? a->x.max - a->x.min : 1, wy = a->y.max > a->y.min ? a->y.max - a->y.min : 1;
    int x = (int)((long)(rx - a->x.min) * 1023 / wx), y = (int)((long)(ry - a->y.min) * 599 / wy);
    if (x < 0) x = 0;
    if (x > 1023) x = 1023;
    if (y < 0) y = 0;
    if (y > 599) y = 599;
    if (x != u->mx || y != u->my) {
        u->mx = x;
        u->my = y;
        event(EV_MOVE, (u64)x, (u64)y);
    }
    int down = a->has_btn && bits(r, n, a->btn) != 0;
    if (down != u->buttons) {
        u->buttons = down;
        event(down ? EV_DOWN : EV_UP, (u64)x, (u64)y);
    }
}

static void arm(struct hid *h) {
    start(h->ch, &h->d, h->ep, 1, INTERRUPT, h->mps, h->pid, h->buf, h->mps);
}

/* The keyboard and mouse: a finished report is handled and asked for again; a channel that
   halted with nothing (NAK) is asked again on the next poll, a few milliseconds later. */
static void poll_hid(struct usb *u) {
    for (int i = 0; i < u->nhid; i++) {
        struct hid *h = &u->hid[i];
        u64 st = rd(HCINT(h->ch));
        if (!st) continue;
        wr(HCINT(h->ch), st);
        if (st & XFERCOMPL) {
            u64 t = rd(HCTSIZ(h->ch));
            int n = h->mps - (int)(t & 0x7ffff);
            h->pid = (int)(t >> 29) & 3;
            if (h->kind == 1) keyboard(u, h->buf, n);
            else if (h->kind == 2) mouse(u, h->buf, n);
            else absolute(u, h, h->buf, n);
        }
        if (st & (XFERCOMPL | CHHLTD)) arm(h);
    }
}

/* ---- the network adapter ---- */

static void arm_net(struct usb *u) {
    if (!u->has_net) return;
    start(NET_IN_CH, &u->netdev, u->net_in, 1, BULK, u->net_mps, u->net_in_pid, u->dma + RX_OFF, 1536);
    u->net_armed = 1;
}

/* A frame that arrived, handled; 1 if there was one. */
static int poll_net(struct usb *u) {
    if (!u->has_net || !u->net_armed) return 0;
    u64 st = rd(HCINT(NET_IN_CH));
    if (!st) return 0;
    wr(HCINT(NET_IN_CH), st);
    int got = 0;
    if (st & XFERCOMPL) {
        u64 t = rd(HCTSIZ(NET_IN_CH));
        u->net_in_pid = (int)(t >> 29) & 3;
        unsigned n = 1536 - (unsigned)(t & 0x7ffff);
        if (n) { net_input(&u->net, u->dma + RX_OFF, n); got = 1; }
    }
    if (st & (XFERCOMPL | CHHLTD)) arm_net(u);
    return got;
}

static int bulk_out(struct usb *u, unsigned len) {
    if (start(NET_OUT_CH, &u->netdev, u->net_out, 0, BULK, u->net_mps, u->net_out_pid, u->dma + TX_OFF, (int)len) != OK)
        return 0;
    for (int i = 0; i < 2000; i++) {
        u64 st = rd(HCINT(NET_OUT_CH));
        if (st & XFERCOMPL) {
            wr(HCINT(NET_OUT_CH), st);
            u->net_out_pid = (int)(rd(HCTSIZ(NET_OUT_CH)) >> 29) & 3;
            return 1;
        }
        if (st & (STALL | XACTERR | BBLERR | DATATGLERR | CHHLTD)) { wr(HCINT(NET_OUT_CH), st); return 0; }
        sys0(SYS_YIELD);
    }
    return 0;
}

static int net_send(const unsigned char *frame, unsigned len) {
    struct usb *u = U;
    if (!u->has_net || len > 1514) return 0;
    for (unsigned i = 0; i < len; i++) u->dma[TX_OFF + i] = frame[i];
    int ok = bulk_out(u, len);
    if (ok && len % (unsigned)u->net_mps == 0) ok = bulk_out(u, 0);   /* the zero-length end */
    return ok;
}

static u64 net_now(void) { return millis(); }

/* While an operation waits: frames, keys and the mouse keep moving. */
static void net_poll(void) {
    struct usb *u = U;
    int got = poll_net(u);
    poll_hid(u);
    if (!got) sleep_ms(1);
}

/* ---- the service: requests from Terminal, and polling in between ---- */

static void put_ip(struct line *l, unsigned ip) {
    for (int k = 3; k >= 0; k--) { put_dec(l, (ip >> (8 * k)) & 255); if (k) put_s(l, "."); }
}

/* Ask the time server `host` (host[:port]) and tell the kernel: Unix seconds, or 0. */
static unsigned set_time(struct usb *u, const char *host, int tries) {
    char name[64];
    unsigned port = 123;
    int i = 0;
    for (; host[i] && host[i] != ':' && i < 63; i++) name[i] = host[i];
    name[i] = 0;
    if (host[i] == ':') {
        port = 0;
        for (i++; host[i] >= '0' && host[i] <= '9'; i++) port = port * 10 + (unsigned)(host[i] - '0');
    }
    unsigned ip = resolve(&u->net, name);
    if (!ip) return 0;
    unsigned secs = 0;
    for (int k = 0; k < tries && !secs; k++) secs = ntp_time(&u->net, ip, port);
    if (!secs || sys(SYS_SETWALL, WALL, secs, 0, 0, 0).status != OK) return 0;
    put_s(&u->l, "usb: network: the time is ");
    put_date(&u->l, secs);
    put_s(&u->l, ", from ");
    put_s(&u->l, host);
    say(u);
    return secs;
}

/* May the caller with this badge use the network? Terminal, yes; a program from the card,
   only the one Terminal allowed in its slot (the same program: the kernel's hash of it). */
static int allowed(struct usb *u, u64 badge) {
    if (badge == 5) return 1;
    if (badge < 10 || badge > 15) return 0;
    struct res b = sys1(SYS_BOOTINFO, badge);
    int k = (int)badge - 10;
    return u->allow[k].on && b.x[4] == 1 && b.x[2] == u->allow[k].h0 && b.x[3] == u->allow[k].h1;
}

static u64 request(struct usb *u, u64 badge, u64 op, u64 arg, char *buf, u64 *v2, u64 *v3) {
    buf[239] = 0;
    if (!allowed(u, badge) && !(badge == 16 && op == NET_ALLOW)) return NET_DENIED;   /* Apps: only to allow */
    if ((op == NET_TIME && badge != 5) || (op == NET_ALLOW && badge != 5 && badge != 16)) return NET_DENIED;
    if (op == NET_ALLOW) {
        u64 slot = arg & 255;
        if (slot < 10 || slot > 15) return NET_BAD;
        struct res b = sys1(SYS_BOOTINFO, slot);
        int k = (int)slot - 10;
        u->allow[k].on = (int)(arg >> 8 & 1) && b.x[4] == 1;
        u->allow[k].h0 = b.x[2];
        u->allow[k].h1 = b.x[3];
        put_s(&u->l, "usb: network: slot ");
        put_dec(&u->l, slot);
        put_s(&u->l, u->allow[k].on ? " may use the network" : " may not use the network");
        say(u);
        return NET_OK;
    }
    if (op == NET_READ && badge != u->body_owner) return NET_DENIED;
    if (op == NET_INFO) {
        struct net_info *i = (struct net_info *)(buf + NET_DATA_OFF);
        i->ip = u->net.ip; i->mask = u->net.mask; i->gateway = u->net.gw; i->dns = u->net.dns;
        for (int k = 0; k < 6; k++) i->mac[k] = u->net.mac[k];
        i->device = (unsigned char)u->has_net;
        i->up = (unsigned char)u->net.up;
        return NET_OK;
    }
    if (op == NET_READ) {
        if (arg > u->body_len) return NET_BAD;
        u64 n = u->body_len - arg < NET_CHUNK ? u->body_len - arg : NET_CHUNK;
        const unsigned char *from = u->dma + BODY_OFF + arg;
        for (u64 k = 0; k < n; k++) buf[NET_DATA_OFF + k] = (char)from[k];
        *v2 = n;
        return NET_OK;
    }
    if (!u->has_net) return NET_NO_DEVICE;
    if (!u->net.up && !dhcp(&u->net)) return NET_NO_ADDRESS;
    if (op == NET_PING) {
        unsigned ip = resolve(&u->net, buf);
        if (!ip) return NET_NO_HOST;
        long ms = ping(&u->net, ip);
        if (ms < 0) return NET_NO_ANSWER;
        *v2 = (u64)ms;
        *v3 = ip;
        return NET_OK;
    }
    if (op == NET_TIME) {
        unsigned secs = set_time(u, buf[0] ? buf : "pool.ntp.org", 1);
        if (!secs) return NET_NO_ANSWER;
        *v2 = secs;
        return NET_OK;
    }
    if (op == NET_GET) {
        int http_status = 0;
        u64 body = 0;
        u->body_len = 0;
        long n = http_get(&u->net, buf, u->dma + BODY_OFF, NET_BODY_MAX, &http_status, &body);
        if (n == -2) return NET_UNSUPPORTED;
        if (n == -3) return NET_NO_HOST;
        if (n < 0) return NET_NO_ANSWER;
        /* the body to the start of the area */
        for (long k = 0; k < n; k++) u->dma[BODY_OFF + k] = u->dma[BODY_OFF + body + (u64)k];
        u->body_len = (u64)n;
        u->body_status = http_status;
        u->body_owner = badge;
        *v2 = (u64)n;
        *v3 = (u64)http_status;
        return NET_OK;
    }
    return NET_BAD;
}

static void serve(struct usb *u) {
    if (u->has_net) {
        arm_net(u);
        if (dhcp(&u->net)) {
            put_s(&u->l, "usb: network: address ");
            put_ip(&u->l, u->net.ip);
            put_s(&u->l, ", gateway ");
            put_ip(&u->l, u->net.gw);
            put_s(&u->l, ", DNS ");
            put_ip(&u->l, u->net.dns);
            say(u);
            if (!set_time(u, "pool.ntp.org", 1)) {
                put_s(&u->l, "usb: network: no answer from a time server");
                say(u);
            }
        } else {
            put_s(&u->l, "usb: network: no address from DHCP");
            say(u);
        }
    }
    for (int i = 0; i < u->nhid; i++) arm(&u->hid[i]);
    for (;;) {
        /* a request, or a few milliseconds (a second, with nothing plugged in) */
        u64 wait = u->nhid || u->has_net ? 8 : 1000;
        struct res r = sys(SYS_RECVT, NETEP, wait, 0, 0, 0);
        if (r.status == OK) {
            u64 badge = r.x[1], op = r.x[2], arg = r.x[3], grant = r.x[5], slot = r.x[6];
            u64 code = NET_BAD, v2 = 0, v3 = 0;
            if (grant) {
                struct res info = sys1(SYS_CAPINFO, grant - 1);
                if (info.x[2] == 0 && info.x[3] == NET_BUF_PAGES && (info.x[1] & (R | W)) == (R | W) &&
                    sys2(SYS_MAP, grant - 1, REQ_PAGE).status == OK) {
                    code = request(u, badge, op, arg, (char *)PAGE(REQ_PAGE), &v2, &v3);
                    sys2(SYS_UNMAP, REQ_PAGE, NET_BUF_PAGES);
                }
                sys1(SYS_DROP, grant - 1);
            }
            if (slot) sys(SYS_REPLY, slot - 1, code, v2, v3, 0);
        }
        while (poll_net(u)) {}
        poll_hid(u);
    }
}

__attribute__((section(".text.start"))) void _start(void) {
    struct usb *u = (struct usb *)DATA;
    u->l.n = 0;
    u->next_addr = 1;
    u->nhid = u->keyboards = u->mice = u->touch = u->buttons = 0;
    u->mx = 512;
    u->my = 300;
    u->has_net = u->net_armed = 0;
    u->body_len = 0;
    u->body_owner = 0;
    for (int k = 0; k < 6; k++) u->allow[k].on = 0;
    u->net.up = 0;
    u->net.ip = u->net.mask = u->net.gw = u->net.dns = 0;
    u->net.arp_next = 0;
    for (int i = 0; i < 8; i++) u->net.arp[i].ip = 0;
    u->net.tcp_state = 0;
    u->net.ping_seq = 0;
    u->net.rand = (unsigned)millis() * 2654435761u;
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
    wr(GAHBCFG, 1 << 5);                              /* DMA on; polled, no interrupts */
    wr(GINTMSK, 0);
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

    if (!(rd(HPRT0) & 1)) {
        sleep_ms(250);
        if (!(rd(HPRT0) & 1)) {
            put_s(&u->l, "usb: nothing plugged in");
            say(u);
            serve(u);                     /* no devices: the network service still answers */
        }
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
    if (u->touch) {
        put_s(&u->l, ", ");
        put_dec(&u->l, (u64)u->touch);
        put_s(&u->l, u->touch == 1 ? " touchscreen or tablet" : " touchscreens or tablets");
    }
    put_s(&u->l, u->has_net ? ", a network adapter" : "");
    say(u);
    serve(u);
}
