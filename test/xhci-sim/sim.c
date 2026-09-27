/*
 * The xHCI simulator: the USB driver's xHCI code (user/xhci.c) and the machine layer's side of
 * the controller (arch/xhci.c), compiled for the host and run against a model of an xHCI
 * controller and of the devices behind it, with the Lean kernel itself deciding every system
 * call. QEMU has no PCIe, so this is how the USB-A ports are tested before they meet a Pi.
 *
 * What is real, and what is modelled:
 *
 *   the driver       user/xhci.c, as usb.c includes it; usb.c's keyboard() and mouse() are
 *                    stand-ins here that record each report they are handed
 *   the kernel       every `xhci` call goes to test/xhci-sim/Oracle.lean, which runs
 *                    `sysXhci` from LeanOS/Kernel.lean on the call, with the arguments as
 *                    arch/kmain.c passes them; its answer (refused, or what the machine layer
 *                    must do) is used as is. The boot content is the kernel's `xhciBoot`.
 *   machine layer    arch/xhci.c, the same file the Pi kernel links: the boot checks, the
 *                    boot content's placement, the reset, and every request
 *   memory           the driver's 256 frames twice: what the controller reads and writes
 *                    (RAM), and what the processor sees (its cache). The driver sees RAM only
 *                    through cache maintenance (`xhci` op 5): a line it wrote and did not have
 *                    cleaned is written back over what the controller put there, as a dirty
 *                    line would be. Its view of the xHCI memory is mapped read-only.
 *   the controller   a model written from the xHCI specification, revision 1.2: registers
 *                    (a 4 KiB BAR like the VL805's, 5 ports, 32 slots), the command ring, the
 *                    transfer rings, the event ring with its cycle bit, Link TRBs with Toggle
 *                    Cycle, ERDP, device and input contexts of 32 or 64 bytes, scratchpads,
 *                    endpoint states (halted on a stall, reset, a new dequeue pointer), port
 *                    power, reset and change bits, and port status change events. Every
 *                    address it follows is checked against where that structure may be in the
 *                    xHCI memory, and every data buffer against the driver's own frames
 *                    outside it (the property `xhci_dma_own_memory` proves); every departure
 *                    from what the specification asks of software is a violation.
 *   the devices      a high-speed hub with a transaction translator and a status endpoint, a
 *                    low-speed keyboard, a full-speed mouse whose endpoint 0 takes 64 bytes, a
 *                    keyboard that stalls SET_IDLE, a receiver with a keyboard and a mouse, and
 *                    a USB 3 drive; each answers only in the boot protocol after SET_PROTOCOL
 *                    (in the report protocol their reports carry a report ID, which the checks
 *                    would see).
 *
 * The scenario, run once with 32-byte contexts and once with 64-byte ones: boot, enumerate
 * through the hub, type and move, unplug and plug devices (the same slots again), enough
 * plugging and typing to wrap the command ring, the event ring and the transfer rings several
 * times, unplug the whole hub and plug it back. Then the machine layer's boot checks are given
 * controllers it must refuse.
 *
 * What is not modelled (see TRUST.md): timing beyond milliseconds, USB 3 devices beyond their
 * port, streams, isochronous transfers, bandwidth, power management, errors on the wire other
 * than a device gone, the VL805's own quirks (it reads ahead of a ring's end: the driver never
 * uses the last ring), and the PCIe bridge (arch/pcie.c runs only on a Pi).
 *
 * Usage: sim ORACLE-COMMAND...   (exit status 0 if every check held)
 */
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../../arch/xhci.h"

/* ======================================================================================
 * The world: memory, time, the oracle
 * ====================================================================================== */

#define FRAMES_PA 0x05100000UL           /* the USB driver's 256 frames (slot 17) */
#define FRAMES_LEN (256UL * 4096)
#define XMEM_PA 0x051C0000UL             /* its last 64: the xHCI memory */
#define XMEM_LEN (64UL * 4096)
#define XOFF (XMEM_PA - FRAMES_PA)

static unsigned char *ram;               /* what the controller reads and writes */
static unsigned char *cpu;               /* what the processor sees */
static unsigned char *snap;              /* cpu as of each line's last cache maintenance */
static uint64_t now_us;
static int violations, failures;
static int quiet;

static void violation(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    printf("VIOLATION: ");
    vprintf(fmt, ap);
    printf("\n");
    va_end(ap);
    violations++;
}

static void failure(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    printf("FAIL: ");
    vprintf(fmt, ap);
    printf("\n");
    va_end(ap);
    failures++;
}

static void view_writable(int w) {
    if (mprotect(cpu + XOFF, XMEM_LEN, w ? PROT_READ | PROT_WRITE : PROT_READ)) { perror("mprotect"); exit(2); }
}

/* Cache maintenance over [pa, pa + len): each line the processor wrote is written back, then
   every line is read again from RAM. */
static void cache_sync(uint64_t pa, uint64_t len) {
    if (!len) return;
    if (pa < FRAMES_PA || pa + len > FRAMES_PA + FRAMES_LEN) {
        violation("cache maintenance at %#llx (%llu bytes), outside the USB driver's frames", (unsigned long long)pa,
                  (unsigned long long)len);
        return;
    }
    uint64_t a = (pa - FRAMES_PA) & ~63UL, end = pa - FRAMES_PA + len;
    int in_view = end > XOFF;
    if (in_view) view_writable(1);
    for (; a < end; a += 64) {
        if (memcmp(cpu + a, snap + a, 64)) {
            if (a >= XOFF) violation("the processor wrote the xHCI memory at %#llx", (unsigned long long)(FRAMES_PA + a));
            memcpy(ram + a, cpu + a, 64);
        }
        memcpy(cpu + a, ram + a, 64);
        memcpy(snap + a, ram + a, 64);
    }
    if (in_view) view_writable(0);
}

/* The oracle: the Lean kernel, on a pipe. */
static FILE *to_oracle, *from_oracle;

static void oracle_start(char **argv) {
    int in[2], out[2];
    if (pipe(in) || pipe(out)) { perror("pipe"); exit(2); }
    pid_t pid = fork();
    if (pid == 0) {
        dup2(in[0], 0);
        dup2(out[1], 1);
        close(in[1]);
        close(out[0]);
        execvp(argv[0], argv);
        perror("exec oracle");
        _exit(2);
    }
    close(in[0]);
    close(out[1]);
    to_oracle = fdopen(in[1], "w");
    from_oracle = fdopen(out[0], "r");
}

static void oracle_line(char *buf, int n) {
    fflush(to_oracle);
    if (!fgets(buf, n, from_oracle)) { printf("FAIL: the oracle stopped answering\n"); exit(1); }
}

static uint64_t boot_word[64 * 512];

static void oracle_boot(void) {
    char line[200];
    fprintf(to_oracle, "base\n");
    oracle_line(line, sizeof line);
    if (strtoull(line, 0, 10) != XMEM_PA) { printf("FAIL: xhciBase is %s, not %#lx\n", line, XMEM_PA); exit(1); }
    fprintf(to_oracle, "boot\n");
    for (;;) {
        oracle_line(line, sizeof line);
        if (!strncmp(line, "end", 3)) break;
        unsigned long long i, w;
        if (sscanf(line, "%llu %llu", &i, &w) != 2 || i >= 64 * 512) { printf("FAIL: oracle said %s", line); exit(1); }
        boot_word[i] = w;
    }
}

/* ======================================================================================
 * The controller: registers, rings, contexts, ports
 * ====================================================================================== */

#define CAPLEN 0x20u
#define DBOFF 0x480u
#define RTSOFF 0x600u
#define XECP 0x700u
#define BAR 0x1000u
#define NPORTS 5
#define MAXSLOTS 32
#define NSCRATCH 2

struct dev;

enum { EP_DISABLED, EP_RUNNING, EP_HALTED, EP_STOPPED };
struct mep {
    int state, dcs, type, mps, interval;
    uint64_t deq, next_at;
    int doorbell;
};
struct mslot {
    int on, addressed;
    struct dev *d;
    uint64_t out;                        /* its output device context */
    uint32_t sc[4];                      /* the slot context as the controller holds it */
    struct mep ep[32];
};
struct rport { int power, reset_until, enabled, csc, pec, prc, plc, usb3; struct dev *d; uint64_t link_at; };

static struct {
    int csz, scratch, ports, bar_ok;
    uint32_t usbcmd, usbsts, config, dnctrl, iman, imod, erstsz;
    uint64_t dcbaap, erstba, erdp, cmd_ptr;
    uint32_t lo[0x1000 / 4];             /* the low word of a 64-bit register, until its high one */
    int ccs, cmd_doorbell, running, bus_master;
    uint64_t hcrst_until, ev_base;
    uint32_t ev_size, ev_enq;
    int pcs, last_lo;                     /* last_lo: the register a low word was written to */
    struct rport port[NPORTS];
    struct mslot slot[MAXSLOTS + 1];
    int events, commands, transfers;
} X;

enum { A_DATA, A_TABLE, A_EVENTS, A_CMD, A_SCRATCH, A_DEVICE, A_INPUT, A_RING };
static const char *const part_name[] = {"a data buffer", "a table", "the event ring", "the command ring",
                                        "a scratchpad page", "a device context", "an input context", "the transfer rings"};
static unsigned char junk[1 << 17];

/* The controller touches `n` bytes at `pa` as `part`: only where the xHCI memory keeps that part
   (xhci_layout), or, for data, in the driver's frames outside the xHCI memory. */
static unsigned char *dma(uint64_t pa, uint64_t n, int part) {
    static const unsigned first[] = {0, 0, 2, 3, 4, 16, 32, 48}, last[] = {0, 1, 2, 3, 15, 31, 47, 63};
    if (!X.bus_master) violation("DMA (%s at %#llx) with bus mastering off", part_name[part], (unsigned long long)pa);
    if (!X.running) violation("DMA (%s at %#llx) while halted", part_name[part], (unsigned long long)pa);
    int ok = pa >= FRAMES_PA && pa + n <= FRAMES_PA + FRAMES_LEN && n <= sizeof junk;
    if (ok && part == A_DATA) ok = pa + n <= XMEM_PA;
    else if (ok) ok = pa >= XMEM_PA + first[part] * 4096UL && pa + n <= XMEM_PA + (last[part] + 1) * 4096UL;
    if (!ok) {
        violation("the controller was sent to %#llx (%llu bytes) for %s", (unsigned long long)pa, (unsigned long long)n,
                  part_name[part]);
        return junk;
    }
    return ram + (pa - FRAMES_PA);
}

/* Each TRB of the command ring and the transfer rings: written (by the machine layer) since
   the controller last did it. A TRB done twice is a ring that went wrong: a dequeue pointer
   set back, a Link that did not toggle, a cycle bit left behind. */
static unsigned char trb_fresh[XMEM_LEN / 16];

static void trb_done(uint64_t at) {
    uint64_t i = (at - XMEM_PA) / 16;
    if (at < XMEM_PA || i >= XMEM_LEN / 16) return;
    if (!trb_fresh[i]) violation("the controller did the TRB at %#llx a second time, unwritten since", (unsigned long long)at);
    trb_fresh[i] = 0;
}

static uint32_t rd32(const unsigned char *p) { uint32_t v; memcpy(&v, p, 4); return v; }
static uint64_t rd64(const unsigned char *p) { uint64_t v; memcpy(&v, p, 8); return v; }
static void wr32(unsigned char *p, uint32_t v) { memcpy(p, &v, 4); }
static void wr64(unsigned char *p, uint64_t v) { memcpy(p, &v, 8); }

static void post(uint64_t p, uint32_t status, uint32_t control) {
    if (!X.running) return;
    if (!X.ev_size) { violation("an event with no event ring"); return; }
    uint32_t next = (X.ev_enq + 1) % X.ev_size;
    if (X.ev_base + 16UL * next == (X.erdp & ~15UL)) { violation("the event ring is full: the driver fell behind"); return; }
    unsigned char *e = dma(X.ev_base + 16UL * X.ev_enq, 16, A_EVENTS);
    wr64(e, p);
    wr32(e + 8, status);
    wr32(e + 12, (control & ~1u) | (uint32_t)X.pcs);         /* the cycle bit last */
    if (++X.ev_enq == X.ev_size) {
        X.ev_enq = 0;
        X.pcs ^= 1;
    }
    X.usbsts |= 8;                                            /* EINT */
    X.iman |= 1;
    X.events++;
}

/* ---- devices ---- */

struct report { unsigned char b[8]; int n; };
struct dev {
    const char *name;
    int id, speed, mps0, hub, stall_idle, nports;
    const unsigned char *ddesc, *cdesc;
    int clen, address, config, slot;
    int protocol[2];
    struct { int num, mps, iface, kind, fresh; struct report q[512]; int head, tail; } in[2];
    int nin;
    struct { struct dev *d; int power, enable, reset_until, c_conn, c_enable, c_reset; } hp[8];
    struct dev *parent;                  /* the hub it is plugged into, or 0 */
    int port;                            /* its port there, or its root port */
};

/* What the driver was handed, in order, and what the devices sent, in order. */
struct seen { int dev, kind, n, fresh; unsigned char b[8], prev[8]; };
static struct seen got[4096], sent[4096];
static int ngot, nsent;

static int hub_changes(struct dev *h) {
    int bits = 0;
    for (int p = 1; p <= h->nports; p++)
        if (h->hp[p].c_conn || h->hp[p].c_enable || h->hp[p].c_reset) bits |= 1 << p;
    return bits;
}

/* A device's reply to a control request: the bytes in `r`, or -1 for a stall. */
static int dev_request(struct dev *d, const unsigned char *s, unsigned char *r) {
    unsigned type = s[0], req = s[1], value = s[2] | s[3] << 8, index = s[4] | s[5] << 8, len = s[6] | s[7] << 8;
    if (type == 0x80 && req == 6 && value >> 8 == 1) {
        memcpy(r, d->ddesc, 18);
        return len < 18 ? (int)len : 18;
    }
    if (type == 0x80 && req == 6 && value >> 8 == 2) {
        memcpy(r, d->cdesc, (size_t)d->clen);
        return (int)len < d->clen ? (int)len : d->clen;
    }
    if (type == 0x00 && req == 5) {
        violation("the driver sent SET_ADDRESS itself (Address Device does that)");
        return -1;
    }
    if (type == 0x00 && req == 9) {
        if (value != d->cdesc[5]) return -1;
        d->config = (int)value;
        d->protocol[0] = d->protocol[1] = 1;       /* the report protocol, until asked */
        d->in[0].fresh = d->in[1].fresh = 1;       /* its next reports are its first */
        return 0;
    }
    if (type == 0x80 && req == 0) { r[0] = r[1] = 0; return len < 2 ? (int)len : 2; }
    if (d->hub) {
        if (type == 0xA0 && req == 6 && value >> 8 == 0x29) {
            static const unsigned char hd[9] = {9, 0x29, 4, 0x29, 0, 50, 100, 0, 0xff};
            memcpy(r, hd, 9);
            r[2] = (unsigned char)d->nports;
            return len < 9 ? (int)len : 9;
        }
        if (index < 1 || index > (unsigned)d->nports) return -1;
        typeof(d->hp[0]) *p = &d->hp[index];
        if (!d->config) return -1;
        if (type == 0xA3 && req == 0) {
            unsigned st = (p->d && p->power) | p->enable << 1 | (p->reset_until ? 1u : 0u) << 4 | p->power << 8;
            if (p->d && p->enable && p->d->speed == 2) st |= 1 << 9;
            if (p->d && p->enable && p->d->speed == 3) st |= 1 << 10;
            unsigned ch = (unsigned)p->c_conn | (unsigned)p->c_enable << 1 | (unsigned)p->c_reset << 4;
            r[0] = (unsigned char)st;
            r[1] = (unsigned char)(st >> 8);
            r[2] = (unsigned char)ch;
            r[3] = (unsigned char)(ch >> 8);
            return len < 4 ? (int)len : 4;
        }
        if (type == 0x23 && req == 3) {                          /* SET_FEATURE */
            if (value == 8) {
                if (!p->power && p->d) p->c_conn = 1;
                p->power = 1;
            } else if (value == 4) {
                if (!p->d || !p->power) return 0;
                p->reset_until = (int)((now_us + 20000) / 1000) + 1;
                p->enable = 0;
            } else return -1;
            return 0;
        }
        if (type == 0x23 && req == 1) {                          /* CLEAR_FEATURE */
            if (value == 16) p->c_conn = 0;
            else if (value == 17) p->c_enable = 0;
            else if (value == 20) p->c_reset = 0;
            else if (value == 1) p->enable = 0;
            else if (value != 18 && value != 19) return -1;
            return 0;
        }
        return -1;
    }
    if (type == 0x21 && req == 0x0B) {                           /* SET_PROTOCOL */
        if (index >= 2 || value > 1) return -1;
        d->protocol[index] = (int)value;
        return 0;
    }
    if (type == 0x21 && req == 0x0A) return d->stall_idle ? -1 : 0;   /* SET_IDLE */
    return -1;
}

/* ---- the topology ---- */

static struct dev *slot_dev(int slot);

/* The device a slot's context names, following its route (root port, then a hub's port per
   tier), or 0 if nothing is there; with the checks a controller's transaction translation
   depends on. */
static struct dev *route(const uint32_t *sc, int speak) {
    unsigned rs = sc[0] & 0xfffff, speed = sc[0] >> 20 & 15, root = sc[1] >> 16 & 0xff;
    unsigned tt_slot = sc[2] & 0xff, tt_port = sc[2] >> 8 & 0xff;
    if (root < 1 || root > NPORTS) { if (speak) violation("a slot context with root port %u", root); return 0; }
    struct rport *rp = &X.port[root - 1];
    if (!rp->d || !rp->power || !rp->enabled) return 0;
    struct dev *d = rp->d, *tt = 0;
    int ttp = 0;
    for (int tier = 0; rs >> (4 * tier) & 15; tier++) {
        unsigned p = rs >> (4 * tier) & 15;
        if (!d->hub || p > (unsigned)d->nports || !d->hp[p].enable || !d->hp[p].d) return 0;
        if (d->speed == 3) { tt = d; ttp = (int)p; }
        d = d->hp[p].d;
    }
    if (speak && (int)speed != d->speed) violation("slot context speed %u for %s, a speed-%d device", speed, d->name, d->speed);
    if (speak && d->speed < 3 && tt) {
        if ((int)tt_slot != tt->slot || (int)tt_port != ttp)
            violation("%s is behind %s's transaction translator (slot %d, port %d); its slot context says slot %u, port %u",
                      d->name, tt->name, tt->slot, ttp, tt_slot, tt_port);
        else if (!(X.slot[tt->slot].sc[0] >> 26 & 1))
            violation("%s is behind %s, whose slot the controller was never told is a hub", d->name, tt->name);
    } else if (speak && (tt_slot || tt_port))
        violation("%s has transaction translator fields it does not need", d->name);
    return d;
}

static struct dev *slot_dev(int slot) {
    struct mslot *s = &X.slot[slot];
    if (!s->on || !s->d) return 0;
    struct dev *d = route(s->sc, 1);
    if (d != s->d || d->address != slot) return 0;   /* unplugged, reset, or something else there */
    return d;
}

/* ---- contexts ---- */

static unsigned ctxsz(void) { return X.csz ? 64u : 32u; }

static void write_out(int slot) {
    struct mslot *s = &X.slot[slot];
    unsigned char *o = dma(s->out, 33 * ctxsz(), A_DEVICE);
    uint32_t sc3 = (uint32_t)(s->d ? s->d->address : 0) | (uint32_t)(s->addressed ? (s->ep[2].state || s->ep[3].state ? 3 : 2) : 1) << 27;
    wr32(o, s->sc[0]);
    wr32(o + 4, s->sc[1]);
    wr32(o + 8, s->sc[2]);
    wr32(o + 12, sc3);
    for (int dci = 1; dci < 32; dci++) {
        struct mep *e = &s->ep[dci];
        unsigned char *c = o + dci * ctxsz();
        wr32(c, (uint32_t)e->state | (uint32_t)e->interval << 16);
        wr32(c + 4, 3u << 1 | (uint32_t)e->type << 3 | (uint32_t)e->mps << 16);
        wr64(c + 8, e->deq | (uint64_t)e->dcs);
    }
}

static int check_ep(const unsigned char *c, int dci, const char *cmd) {
    uint32_t w0 = rd32(c), w1 = rd32(c + 4);
    uint64_t deq = rd64(c + 8);
    int ok = 1;
    if (w0 >> 10 & 31) { violation("%s: endpoint %d with streams", cmd, dci); ok = 0; }
    if (deq & 14) { violation("%s: endpoint %d's dequeue pointer %#llx is not 16-byte aligned", cmd, dci, (unsigned long long)deq); ok = 0; }
    if ((deq & ~15UL) < XMEM_PA + 48 * 4096UL || (deq & ~15UL) >= XMEM_PA + XMEM_LEN) {
        violation("%s: endpoint %d's ring is at %#llx", cmd, dci, (unsigned long long)deq);
        ok = 0;
    }
    if ((w1 >> 1 & 3) != 3) { violation("%s: endpoint %d with CErr %u", cmd, dci, w1 >> 1 & 3); ok = 0; }
    return ok;
}

/* ---- commands ---- */

static uint32_t cmd_address(uint64_t p, int slot) {
    struct mslot *s = &X.slot[slot];
    if (slot < 1 || slot > MAXSLOTS || !s->on) return 11;               /* slot not enabled */
    unsigned char *in = dma(p, 33 * ctxsz(), A_INPUT);
    if ((p & 4095) != 0) violation("Address Device: input context at %#llx, not a page", (unsigned long long)p);
    uint32_t drop = rd32(in), add = rd32(in + 4);
    if (drop != 0 || add != 3) { violation("Address Device: drop %#x, add %#x (want 0 and A0|A1)", drop, add); return 17; }
    const unsigned char *sc = in + ctxsz(), *ep0 = in + 2 * ctxsz();
    uint32_t w[4] = {rd32(sc), rd32(sc + 4), rd32(sc + 8), rd32(sc + 12)};
    if (w[2] >> 22) violation("Address Device: interrupter %u", w[2] >> 22);
    if ((w[0] >> 27) != 1) violation("Address Device: context entries %u", w[0] >> 27);
    if (!check_ep(ep0, 1, "Address Device")) return 17;
    uint32_t e1 = rd32(ep0 + 4);
    if ((e1 >> 3 & 7) != 4) { violation("Address Device: endpoint 0 of type %u", e1 >> 3 & 7); return 17; }
    memcpy(s->sc, w, sizeof w);
    struct dev *d = route(s->sc, 1);
    if (!d || d->address != 0) return 4;                                  /* USB transaction error */
    unsigned mps = e1 >> 16;
    if ((d->speed == 2 && mps != 8) || (d->speed == 3 && mps != 64) || (d->speed == 1 && mps != 8 && mps != 64))
        violation("Address Device: endpoint 0 of %s with %u bytes a packet", d->name, mps);
    s->d = d;
    s->addressed = 1;
    d->address = slot;                                                    /* SET_ADDRESS, by the controller */
    d->slot = slot;
    struct mep *e = &s->ep[1];
    e->state = EP_RUNNING;
    e->type = 4;
    e->mps = (int)mps;
    e->deq = rd64(ep0 + 8) & ~15UL;
    e->dcs = (int)(rd64(ep0 + 8) & 1);
    write_out(slot);
    return 1;
}

static uint32_t cmd_configure(uint64_t p, int slot, int evaluate) {
    struct mslot *s = &X.slot[slot];
    const char *what = evaluate ? "Evaluate Context" : "Configure Endpoint";
    if (slot < 1 || slot > MAXSLOTS || !s->on) return 11;
    if (!s->addressed) return 19;
    unsigned char *in = dma(p, 33 * ctxsz(), A_INPUT);
    uint32_t drop = rd32(in), add = rd32(in + 4);
    if (drop) violation("%s: drop flags %#x", what, drop);
    const unsigned char *sc = in + ctxsz();
    uint32_t w[4] = {rd32(sc), rd32(sc + 4), rd32(sc + 8), rd32(sc + 12)};
    if (evaluate) {
        if (add & ~3u) { violation("Evaluate Context: add flags %#x", add); return 17; }
        if (add & 1) {                                     /* hub fields, exit latency, interrupter */
            if (w[2] >> 22) violation("Evaluate Context: interrupter %u", w[2] >> 22);
            s->sc[0] = (s->sc[0] & ~(3u << 25)) | (w[0] & 3u << 25);
            s->sc[1] = (s->sc[1] & 0x00ffffffu) | (w[1] & 0xff000000u);
            s->sc[2] = (s->sc[2] & ~(3u << 16)) | (w[2] & 3u << 16);
        }
        if (add & 2) {
            const unsigned char *e0 = in + 2 * ctxsz();
            if (!check_ep(e0, 1, what)) return 17;
            s->ep[1].mps = (int)(rd32(e0 + 4) >> 16);
            if (s->d && s->ep[1].mps != s->d->mps0) violation("Evaluate Context: endpoint 0 of %s told %d bytes, it has %d",
                                                             s->d->name, s->ep[1].mps, s->d->mps0);
        }
        write_out(slot);
        return 1;
    }
    if (!(add & 1) || (add & 2)) { violation("Configure Endpoint: add flags %#x (want A0, not A1)", add); return 17; }
    unsigned entries = w[0] >> 27, max = 1;
    for (int dci = 2; dci < 32; dci++) {
        if (!(add >> dci & 1)) continue;
        max = (unsigned)dci;
        const unsigned char *c = in + (unsigned)(dci + 1) * ctxsz();
        if (!check_ep(c, dci, what)) return 17;
        uint32_t w0 = rd32(c), w1 = rd32(c + 4), type = w1 >> 3 & 7, mps = w1 >> 16, ival = w0 >> 16 & 0xff;
        struct dev *d = s->d;
        int k = -1;
        for (int i = 0; d && i < d->nin; i++) if (2 * d->in[i].num + 1 == dci) k = i;
        if (k < 0 || type != 7) { violation("Configure Endpoint: endpoint %d (type %u) that %s does not have", dci, type,
                                            d ? d->name : "?"); return 17; }
        if ((int)mps != d->in[k].mps) violation("Configure Endpoint: %s's endpoint %d told %u bytes, it has %d", d->name, dci, mps, d->in[k].mps);
        if (ival < (d->speed == 3 ? 0u : 3u) || ival > 15) violation("Configure Endpoint: interval %u", ival);
        struct mep *e = &s->ep[dci];
        e->state = EP_RUNNING;
        e->type = (int)type;
        e->mps = (int)mps;
        e->interval = (int)ival;
        e->deq = rd64(c + 8) & ~15UL;
        e->dcs = (int)(rd64(c + 8) & 1);
        e->next_at = 0;
    }
    if (entries < max) violation("Configure Endpoint: context entries %u, below endpoint %u", entries, max);
    if (w[2] >> 22) violation("Configure Endpoint: interrupter %u", w[2] >> 22);
    s->sc[0] = (s->sc[0] & ~(31u << 27)) | entries << 27;
    write_out(slot);
    return 1;
}

static void run_commands(void) {
    for (int n = 0; n < 1024 && X.running; n++) {
        unsigned char *t = dma(X.cmd_ptr, 16, A_CMD);
        uint64_t p = rd64(t);
        uint32_t st = rd32(t + 8), ctl = rd32(t + 12), type = ctl >> 10 & 63;
        if ((int)(ctl & 1) != X.ccs) return;
        uint64_t at = X.cmd_ptr;
        trb_done(at);
        X.cmd_ptr += 16;
        if (type == 6) {                                       /* Link */
            X.cmd_ptr = p & ~15UL;
            if (ctl & 2) X.ccs ^= 1;
            continue;
        }
        int slot = (int)(ctl >> 24), dci = (int)(ctl >> 16 & 31);
        uint32_t cc = 1, out_slot = (uint32_t)slot;
        struct mslot *s = slot >= 1 && slot <= MAXSLOTS ? &X.slot[slot] : 0;
        X.commands++;
        if (st) violation("a command with status %#x", st);
        if (type == 9) {                                       /* Enable Slot */
            out_slot = 0;
            cc = 9;
            for (int k = 1; k <= (int)(X.config & 0xff) && k <= MAXSLOTS; k++)
                if (!X.slot[k].on) {
                    memset(&X.slot[k], 0, sizeof X.slot[k]);
                    X.slot[k].on = 1;
                    X.slot[k].out = rd64(dma(X.dcbaap + 8UL * (unsigned)k, 8, A_TABLE));
                    dma(X.slot[k].out, 33 * ctxsz(), A_DEVICE);
                    out_slot = (uint32_t)k;
                    cc = 1;
                    break;
                }
        } else if (type == 10) {                               /* Disable Slot */
            if (!s || !s->on) cc = 11;
            else {
                if (s->d && s->d->address == slot) s->d->address = 0, s->d->slot = 0;
                memset(s, 0, sizeof *s);
            }
        } else if (type == 11) {
            if (ctl & 512) violation("Address Device with BSR");
            cc = s ? cmd_address(p, slot) : 11;
        } else if (type == 12 || type == 13) {
            if (type == 12 && (ctl & 512)) violation("Configure Endpoint with Deconfigure");
            cc = s ? cmd_configure(p, slot, type == 13) : 11;
        } else if (type == 14 || type == 15) {                 /* Reset Endpoint, Stop Endpoint */
            if (!s || !s->on) cc = 11;
            else if (dci < 1 || s->ep[dci].state == EP_DISABLED) cc = 19;
            else if (type == 14 && s->ep[dci].state != EP_HALTED) cc = 19;
            else if (type == 15 && s->ep[dci].state != EP_RUNNING) cc = 19;
            else s->ep[dci].state = EP_STOPPED;
        } else if (type == 16) {                               /* Set TR Dequeue Pointer */
            if (!s || !s->on) cc = 11;
            else if (dci < 1 || (s->ep[dci].state != EP_STOPPED)) cc = 19;
            else if (p & 14 || st >> 16) { violation("Set TR Dequeue Pointer with a stream"); cc = 17; }
            else {
                dma(p & ~15UL, 16, A_RING);
                s->ep[dci].deq = p & ~15UL;
                s->ep[dci].dcs = (int)(p & 1);
            }
        } else if (type == 23) {
            out_slot = 0;
        } else {
            violation("command TRB type %u", type);
            cc = 5;
        }
        if (s && s->on && cc == 1 && type != 10) write_out(slot);
        post(at, cc << 24, 33u << 10 | out_slot << 24);
    }
}

/* ---- transfers ---- */

static void xfer_event(uint64_t trb, uint32_t cc, uint32_t left, int slot, int dci) {
    X.transfers++;
    post(trb, cc << 24 | left, 32u << 10 | (uint32_t)dci << 16 | (uint32_t)slot << 24);
}

/* Read the TRB at an endpoint's dequeue pointer, following Links; 0 if the ring is empty
   there (the cycle bit is not the endpoint's). */
static int next_trb(struct mep *e, uint64_t *at, uint64_t *p, uint32_t *st, uint32_t *ctl) {
    for (int links = 0; links < 4; links++) {
        unsigned char *t = dma(e->deq, 16, A_RING);
        *at = e->deq;
        *p = rd64(t);
        *st = rd32(t + 8);
        *ctl = rd32(t + 12);
        if ((int)(*ctl & 1) != e->dcs) return 0;
        if ((*ctl >> 10 & 63) != 6) {
            if (*st >> 22) violation("a transfer TRB for interrupter %u", *st >> 22);
            return 1;
        }
        trb_done(e->deq);
        dma(*p & ~15UL, 16, A_RING);
        e->deq = *p & ~15UL;
        if (*ctl & 2) e->dcs ^= 1;
    }
    violation("a ring of Links");
    return 0;
}

/* The TRB at `at`, done: the endpoint goes on to the next. */
static void consume(struct mep *e, uint64_t at) {
    trb_done(at);
    e->deq = at + 16;
}

/* Endpoint 0: whole control transfers, a TD at a time. */
static void run_control(int slot) {
    struct mslot *s = &X.slot[slot];
    struct mep *e = &s->ep[1];
    for (int n = 0; n < 64 && e->state == EP_RUNNING; n++) {
        uint64_t at, p;
        uint32_t st, ctl;
        if (!next_trb(e, &at, &p, &st, &ctl)) return;
        uint32_t type = ctl >> 10 & 63;
        consume(e, at);
        if (type == 8) { if (ctl & 32) xfer_event(at, 1, 0, slot, 1); continue; }
        if (type != 2) { violation("endpoint 0: a TRB of type %u where a Setup Stage belongs", type); xfer_event(at, 5, 0, slot, 1); e->state = EP_HALTED; return; }
        if (!(ctl & 64) || (st & 0x1ffff) != 8) violation("a Setup Stage TRB without its 8 bytes in it");
        unsigned char setup[8], reply[1100];
        memcpy(setup, &p, 8);
        unsigned trt = ctl >> 16 & 3, len = setup[6] | setup[7] << 8;
        int in = setup[0] >> 7;
        if (trt != (len ? (in ? 3u : 2u) : 0u)) violation("a Setup Stage TRB with TRT %u for a request of %u bytes", trt, len);
        struct dev *d = slot_dev(slot);
        int r = d ? dev_request(d, setup, reply) : -1;
        uint32_t fail = d ? 6 : 4;                          /* a stall, or a transaction error */
        uint64_t dat, sat, dp;
        uint32_t dst, dctl, sst, sctl;
        uint32_t left = 0;
        if (len) {
            if (!next_trb(e, &dat, &dp, &dst, &dctl) || (dctl >> 10 & 63) != 3) {
                violation("a Setup Stage TRB for %u bytes with no Data Stage after it", len);
                e->state = EP_HALTED;
                return;
            }
            consume(e, dat);
            uint32_t dlen = dst & 0x1ffff;
            if ((int)(dctl >> 16 & 1) != in) violation("a Data Stage TRB in the wrong direction");
            if (dlen != len) violation("a Data Stage TRB of %u bytes for a request of %u", dlen, len);
            if (r < 0) { xfer_event(dat, fail, dlen, slot, 1); e->state = EP_HALTED; return; }
            int packet = r < d->mps0 ? r : d->mps0;
            if (packet > e->mps) { xfer_event(dat, 3, dlen, slot, 1); e->state = EP_HALTED; return; }   /* babble */
            if (in) {
                unsigned char *b = dma(dp, dlen, A_DATA);
                memcpy(b, reply, (size_t)r);
                left = dlen - (unsigned)r;
            }
            if (dctl & 32 || (left && dctl & 4)) xfer_event(dat, left ? 13 : 1, left, slot, 1);
        } else if (r < 0) {
            /* the stall comes in the status stage */
        }
        if (!next_trb(e, &sat, &dp, &sst, &sctl) || (sctl >> 10 & 63) != 4) {
            violation("a control transfer with no Status Stage TRB");
            e->state = EP_HALTED;
            return;
        }
        consume(e, sat);
        if ((int)(sctl >> 16 & 1) != (len && in ? 0 : 1)) violation("a Status Stage TRB in the wrong direction");
        if (r < 0) { xfer_event(sat, fail, 0, slot, 1); e->state = EP_HALTED; return; }
        if (sctl & 32) xfer_event(sat, 1, 0, slot, 1);
    }
}

/* An interrupt IN endpoint: a Normal TRB waits there until the device has a report and its
   interval has passed. */
static void run_interrupt(int slot, int dci) {
    struct mslot *s = &X.slot[slot];
    struct mep *e = &s->ep[dci];
    if (e->state != EP_RUNNING || now_us < e->next_at) return;
    uint64_t at, p;
    uint32_t st, ctl;
    if (!next_trb(e, &at, &p, &st, &ctl)) return;
    uint32_t type = ctl >> 10 & 63, len = st & 0x1ffff;
    if (type != 1) { violation("an interrupt endpoint: a TRB of type %u", type); consume(e, at); xfer_event(at, 5, 0, slot, dci); return; }
    if (ctl & 64) violation("a Normal TRB with immediate data on an IN endpoint");
    struct dev *d = slot_dev(slot);
    if (!d) return;                                      /* nothing answers: it waits */
    int k = -1;
    for (int i = 0; i < d->nin; i++) if (2 * d->in[i].num + 1 == dci) k = i;
    if (k < 0) return;
    unsigned char r[8];
    int n;
    if (d->hub) {
        int bits = hub_changes(d);
        if (!bits) return;
        r[0] = (unsigned char)bits;
        n = 1;
    } else {
        typeof(d->in[0]) *q = &d->in[k];
        if (q->head == q->tail) return;
        struct report *rep = &q->q[q->head % 512];
        if (d->protocol[q->iface] != 0) {                  /* the report protocol: an ID first */
            r[0] = (unsigned char)(q->kind == 1 ? 1 : 2);
            memcpy(r + 1, rep->b, 7);
            n = rep->n + 1 > q->mps ? q->mps : rep->n + 1;
        } else {
            memcpy(r, rep->b, 8);
            n = rep->n;
        }
        q->head++;
        struct seen *w = &sent[nsent++ % 4096];
        w->dev = d->id;
        w->kind = q->kind;
        w->n = rep->n;                                    /* what the driver must hand on: the */
        memcpy(w->b, rep->b, 8);                          /* boot report, whatever went on the wire */
        w->fresh = q->fresh;
        q->fresh = 0;
    }
    if ((uint32_t)n > len) { consume(e, at); xfer_event(at, 3, len, slot, dci); e->state = EP_HALTED; return; }
    memcpy(dma(p, len, A_DATA), r, (size_t)n);
    consume(e, at);
    e->next_at = now_us + (125UL << e->interval);
    if (ctl & 32 || ((uint32_t)n < len && ctl & 4)) xfer_event(at, (uint32_t)n < len ? 13 : 1, len - (uint32_t)n, slot, dci);
}

/* ---- ports ---- */

static void port_event(int p) {
    post((uint64_t)(p + 1) << 24, 1u << 24, 34u << 10);
}

static uint32_t portsc(int p) {
    struct rport *r = &X.port[p];
    int conn = r->d && r->power;
    uint32_t v = (uint32_t)conn | (uint32_t)r->enabled << 1 | (r->reset_until ? 1u : 0u) << 4 | (uint32_t)r->power << 9;
    v |= (uint32_t)(r->enabled ? 0 : conn ? 7 : 5) << 5;      /* PLS: U0, polling, RxDetect */
    if (r->enabled && r->d) v |= (uint32_t)(r->d->speed == 4 ? 4 : r->d->speed == 2 ? 2 : r->d->speed == 3 ? 3 : 1) << 10;
    v |= (uint32_t)r->csc << 17 | (uint32_t)r->pec << 18 | (uint32_t)r->prc << 21 | (uint32_t)r->plc << 22;
    return v;
}

static void attach_root(int p, struct dev *d) {
    struct rport *r = &X.port[p - 1];
    r->d = d;
    d->parent = 0;
    d->port = p;
    d->address = 0;
    d->config = 0;
    if (r->power) {
        r->csc = 1;
        port_event(p - 1);
        if (r->usb3) r->link_at = now_us + 20000;
    }
}

static void detach_root(int p) {
    struct rport *r = &X.port[p - 1];
    if (r->d) r->d->address = 0;
    r->d = 0;
    r->enabled = 0;
    r->reset_until = 0;
    r->csc = 1;
    port_event(p - 1);
}

static void attach_hub(struct dev *h, int p, struct dev *d) {
    h->hp[p].d = d;
    d->parent = h;
    d->port = p;
    d->address = 0;
    d->config = 0;
    if (h->hp[p].power) h->hp[p].c_conn = 1;
}

static void detach_hub(struct dev *h, int p) {
    if (h->hp[p].d) h->hp[p].d->address = 0;
    h->hp[p].d = 0;
    h->hp[p].enable = 0;
    h->hp[p].reset_until = 0;
    h->hp[p].c_conn = 1;
}

static void unaddress_below(struct dev *d) {
    d->address = 0;
    d->config = 0;
    for (int p = 1; d->hub && p <= d->nports; p++) {
        d->hp[p].enable = 0;
        if (d->hp[p].d) unaddress_below(d->hp[p].d);
    }
}

/* ---- the whole controller, one step ---- */

static void hubs_step(struct dev *d) {
    for (int p = 1; d && d->hub && p <= d->nports; p++) {
        typeof(d->hp[0]) *hp = &d->hp[p];
        if (hp->reset_until && now_us / 1000 >= (uint64_t)hp->reset_until) {
            hp->reset_until = 0;
            if (hp->d) {
                hp->enable = 1;
                hp->c_reset = 1;
                unaddress_below(hp->d);
            }
        }
        if (hp->d) hubs_step(hp->d);
    }
}

static void step(void) {
    if (X.hcrst_until && now_us >= X.hcrst_until) {
        X.hcrst_until = 0;
        X.usbcmd &= ~2u;
        X.usbsts &= ~(1u << 11);
    }
    for (int p = 0; p < NPORTS; p++) {
        struct rport *r = &X.port[p];
        if (r->reset_until && now_us >= (uint64_t)r->reset_until) {
            r->reset_until = 0;
            if (r->d) {
                r->enabled = 1;
                unaddress_below(r->d);
            }
            r->prc = 1;
            port_event(p);
        }
        if (r->link_at && now_us >= r->link_at) {
            r->link_at = 0;
            if (r->d) { r->enabled = 1; r->plc = 1; port_event(p); }
        }
        if (r->d) hubs_step(r->d);
    }
    if (!X.running) return;
    if (X.cmd_doorbell) { X.cmd_doorbell = 0; run_commands(); }
    for (int s = 1; s <= MAXSLOTS; s++) {
        if (!X.slot[s].on) continue;
        struct mep *e = &X.slot[s].ep[1];
        if (e->doorbell && e->state == EP_STOPPED) e->state = EP_RUNNING;
        if (e->doorbell) { e->doorbell = 0; run_control(s); }
        for (int dci = 2; dci < 32; dci++) {
            struct mep *f = &X.slot[s].ep[dci];
            if (f->doorbell && f->state == EP_STOPPED) f->state = EP_RUNNING;
            f->doorbell = 0;
            if (f->state == EP_RUNNING) run_interrupt(s, dci);
        }
    }
}

static void advance(uint64_t us) {
    uint64_t end = now_us + us;
    while (now_us < end) {
        now_us = now_us + 500 < end ? now_us + 500 : end;
        step();
    }
}

/* ---- registers ---- */

static uint32_t reg_read(uint64_t off) {
    if (off & 3 || off >= BAR) { violation("a register read at %#llx", (unsigned long long)off); return 0xffffffff; }
    uint32_t o = (uint32_t)off;
    if (o == 0) return CAPLEN | 0x0100u << 16;
    if (o == 4) return MAXSLOTS | 1u << 8 | (uint32_t)X.ports << 24;
    if (o == 8) return (uint32_t)(X.scratch & 31) << 27 | (uint32_t)(X.scratch >> 5) << 21 | 1u << 4;
    if (o == 0x10) return 1u | 1u << 3 | (uint32_t)X.csz << 2 | (XECP / 4) << 16;   /* AC64, PPC */
    if (o == 0x14) return DBOFF;
    if (o == 0x18) return RTSOFF;
    if (o == XECP) return 2 | (0x10 / 4) << 8 | 0x0200u << 16;          /* USB 2: port 1 */
    if (o == XECP + 4 || o == XECP + 0x14) return 0x20425355;          /* "USB " */
    if (o == XECP + 8) return 1 | 1 << 8;
    if (o == XECP + 0x10) return 2 | 0x0300u << 16;                     /* USB 3: ports 2 to 5 */
    if (o == XECP + 0x18) return 2 | 4 << 8;
    if (o < CAPLEN || (o >= XECP && o < XECP + 0x20)) return 0;
    if (o >= CAPLEN && o < CAPLEN + 0x400) {
        uint32_t r = o - CAPLEN;
        if (r == 0) return X.usbcmd;
        if (r == 4) return X.usbsts | (X.running ? 0 : 1);
        if (r == 8) return 1;                                   /* 4 KiB pages */
        if (r == 0x14) return X.dnctrl;
        if (r == 0x18) return 0;                                /* CRCR reads 0, but for CRR */
        if (r == 0x38) return X.config;
        return 0;
    }
    if (o >= CAPLEN + 0x400 && o < CAPLEN + 0x400 + 0x10 * NPORTS) {
        uint32_t r = o - CAPLEN - 0x400;
        return r % 16 == 0 ? portsc((int)(r / 16)) : 0;
    }
    if (o >= RTSOFF && o < RTSOFF + 0x40) {
        uint32_t r = o - RTSOFF;
        if (r == 0) return (uint32_t)(now_us / 125) & 0x3fff;
        if (r == 0x20) return X.iman;
        if (r == 0x24) return X.imod;
        if (r == 0x28) return X.erstsz;
        if (r == 0x38) return (uint32_t)X.erdp;
        if (r == 0x3c) return (uint32_t)(X.erdp >> 32);
        return 0;
    }
    return 0;
}

static void hc_reset(void) {
    X.usbcmd = 2;
    X.usbsts = 1u << 11;
    X.hcrst_until = now_us + 1500;
    X.config = X.dnctrl = X.iman = X.erstsz = 0;
    X.imod = 4000;
    X.dcbaap = X.erstba = X.erdp = X.cmd_ptr = 0;
    X.ev_base = X.ev_size = X.ev_enq = 0;
    X.running = 0;
    memset(X.slot, 0, sizeof X.slot);
    for (int p = 0; p < NPORTS; p++) {
        X.port[p].power = X.port[p].enabled = X.port[p].reset_until = 0;
        X.port[p].csc = X.port[p].pec = X.port[p].prc = X.port[p].plc = 0;
        if (X.port[p].d) unaddress_below(X.port[p].d);
    }
}

static void reg_write(uint64_t off, uint32_t v) {
    if (off & 3 || off >= BAR) { violation("a register write at %#llx", (unsigned long long)off); return; }
    uint32_t o = (uint32_t)off;
    int was_lo = X.last_lo;
    X.last_lo = 0;
    if (o < CAPLEN || (o >= XECP && o < XECP + 0x20)) { violation("a write to capability register %#x", o); return; }
    if (o >= CAPLEN && o < CAPLEN + 0x400) {
        uint32_t r = o - CAPLEN;
        if (r == 0) {
            if (v & 2) { if (X.running) violation("HCRST while running"); hc_reset(); return; }
            if (X.hcrst_until) violation("USBCMD written during a reset");
            if (v & ~(1u | 4u | 8u | 1u << 10)) violation("USBCMD written with %#x", v);
            if ((v & 1) && !X.running) {
                if (!X.dcbaap || !X.cmd_ptr || !X.ev_size) violation("Run/Stop with DMA bases unset");
                X.running = 1;
                /* The scratchpad array and its pages: the controller's own. */
                if (X.scratch) {
                    uint64_t arr = rd64(dma(X.dcbaap, 8, A_TABLE));
                    for (int k = 0; k < X.scratch; k++) memset(dma(rd64(dma(arr + 8UL * (unsigned)k, 8, A_TABLE)), 4096, A_SCRATCH), 0x5c, 4096);
                }
                for (int p = 0; p < NPORTS; p++)
                    if (X.port[p].csc || X.port[p].prc) port_event(p);
            } else if (!(v & 1) && X.running) X.running = 0;
            X.usbcmd = v & ~2u;
            return;
        }
        if (r == 4) { X.usbsts &= ~(v & 0x41c); return; }
        if (r == 0x14) { X.dnctrl = v; return; }
        if (r == 0x38) { if (X.running) violation("CONFIG written while running"); X.config = v; return; }
        if (r == 0x18 || r == 0x30) { X.lo[o / 4] = v; X.last_lo = (int)o; return; }
        if (r == 0x1c || r == 0x34) {
            if (was_lo != (int)o - 4) violation("the high word of %#x without its low word just before", r - 4);
            uint64_t full = (uint64_t)v << 32 | X.lo[(o - 4) / 4];
            if (r == 0x34) {
                if (X.running) violation("DCBAAP written while running");
                X.dcbaap = full;
            } else if (!X.running) {
                X.cmd_ptr = full & ~63UL;
                X.ccs = (int)(full & 1);
            }
            return;
        }
        violation("a write to operational register %#x", r);
        return;
    }
    if (o >= CAPLEN + 0x400 && o < CAPLEN + 0x400 + 0x10 * NPORTS) {
        uint32_t r = o - CAPLEN - 0x400;
        int p = (int)(r / 16);
        struct rport *pt = &X.port[p];
        if (r % 16) return;                                     /* PORTPMSC, PORTLI, PORTHLPMC */
        if (v & 2) { violation("PORTSC of port %d written with PED set (that disables it)", p + 1); pt->enabled = 0; }
        if (v & 0x00fe0000u & ~0x00ee0000u) {}
        pt->csc &= !(v >> 17 & 1);
        pt->pec &= !(v >> 18 & 1);
        pt->prc &= !(v >> 21 & 1);
        pt->plc &= !(v >> 22 & 1);
        int power = (int)(v >> 9 & 1);
        if (power && !pt->power) {
            pt->power = 1;
            if (pt->d) {
                pt->csc = 1;
                port_event(p);
                if (pt->usb3) pt->link_at = now_us + 20000;
            }
        } else if (!power && pt->power) {
            violation("port %d powered off", p + 1);
            pt->power = pt->enabled = 0;
        }
        if (v & 16) {                                           /* PR */
            if (pt->usb3) violation("a reset of USB 3 port %d", p + 1);
            else if (pt->d && pt->power) {
                pt->enabled = 0;
                pt->reset_until = (int)(now_us + 50000);
            }
        }
        return;
    }
    if (o >= RTSOFF && o < RTSOFF + 0x40) {
        uint32_t r = o - RTSOFF;
        if (r == 0x20) { X.iman = (X.iman & ~1u & ~2u) | (v & 2) | (X.iman & 1 & ~v); return; }
        if (r == 0x24) { X.imod = v; return; }
        if (r == 0x28) { X.erstsz = v; return; }
        if (r == 0x30 || r == 0x38) { X.lo[o / 4] = v; X.last_lo = (int)o; return; }
        if (r == 0x34 || r == 0x3c) {
            if (was_lo != (int)o - 4) violation("the high word of runtime %#x without its low word just before", r - 4);
            uint64_t full = (uint64_t)v << 32 | X.lo[(o - 4) / 4];
            if (r == 0x34) {                                    /* ERSTBA: the table is read now */
                X.erstba = full;
                if (X.erstsz != 1) violation("ERSTBA written with ERSTSZ %u", X.erstsz);
                int bm = X.bus_master, run = X.running;
                X.bus_master = X.running = 1;                   /* (this read is checked for place only) */
                unsigned char *t = dma(full, 16, A_TABLE);
                X.bus_master = bm;
                X.running = run;
                X.ev_base = rd64(t);
                X.ev_size = rd32(t + 8);
                if ((X.ev_base & 63) || X.ev_size < 16 || X.ev_size > 256) violation("an event ring segment of %u TRBs at %#llx", X.ev_size, (unsigned long long)X.ev_base);
                X.ev_enq = 0;
                X.pcs = 1;
            } else {
                uint64_t p = full & ~15UL;
                if (p < X.ev_base || p >= X.ev_base + 16UL * X.ev_size) violation("ERDP %#llx outside the event ring", (unsigned long long)full);
                X.erdp = p | (X.erdp & 8 & ~(full & 8));
                if (full & 7) violation("ERDP with a segment index");
            }
            return;
        }
        violation("a write to runtime register %#x", r);
        return;
    }
    if (o >= DBOFF && o < DBOFF + 4 * (MAXSLOTS + 1)) {
        int s = (int)((o - DBOFF) / 4);
        if (!X.running) { violation("a doorbell while halted"); return; }
        if (s == 0) {
            if (v) violation("doorbell 0 with target %u", v);
            X.cmd_doorbell = 1;
            return;
        }
        if (!X.slot[s].on) { violation("a doorbell for slot %d, which is not enabled", s); return; }
        int dci = (int)(v & 0xff);
        if (dci < 1 || dci > 31 || v >> 8) { violation("doorbell %d with %#x", s, v); return; }
        if (X.slot[s].ep[dci].state == EP_DISABLED) { violation("a doorbell for endpoint %d of slot %d, not configured", dci, s); return; }
        X.slot[s].ep[dci].doorbell = 1;
        return;
    }
    violation("a register write at %#x, in no register", o);
}

/* ======================================================================================
 * The machine layer's surroundings (arch/xhci.h); arch/xhci.c is compiled beside this file
 * ====================================================================================== */

static char console[1 << 20];
static size_t console_n;

static void out(const char *s) {
    size_t n = strlen(s);
    if (console_n + n < sizeof console) { memcpy(console + console_n, s, n); console_n += n; }
    if (!quiet) fputs(s, stdout);
}

uint32_t xhci_mmio_r32(uint64_t off) { now_us += 1; return reg_read(off); }
void xhci_mmio_w32(uint64_t off, uint32_t v) { now_us += 1; reg_write(off, v); }
volatile uint32_t *xhci_phys32(uint64_t pa) {
    if (pa < XMEM_PA || pa + 4 > XMEM_PA + XMEM_LEN || (pa & 3)) {
        violation("the machine layer wrote %#llx, outside the xHCI memory", (unsigned long long)pa);
        return (volatile uint32_t *)junk;
    }
    uint64_t page = (pa - XMEM_PA) / 4096;
    if ((page == 3 || page >= 48) && !(pa & 15)) trb_fresh[(pa - XMEM_PA) / 16] = 1;
    return (volatile uint32_t *)(ram + (pa - FRAMES_PA));
}
void xhci_clean(uint64_t pa, uint64_t len) { (void)pa; (void)len; }   /* its writes go to RAM here */
void xhci_flush(uint64_t pa, uint64_t len) { cache_sync(pa, len); }
void xhci_barrier(void) {}
void xhci_bus_master(int on) { X.bus_master = on; }
void xhci_udelay(uint64_t us) { advance(us); }
uint64_t xhci_boot_word(uint64_t i) { return boot_word[i]; }
void kputs(const char *s) { out(s); }
void kputhex(uint64_t v) { char b[24]; snprintf(b, sizeof b, "%#llx", (unsigned long long)v); out(v ? b : "0x0"); }
void kputdec(uint64_t v) { char b[24]; snprintf(b, sizeof b, "%llu", (unsigned long long)v); out(b); }
void kpanic(const char *msg) { printf("FAIL: kernel panic: %s\n", msg); exit(1); }

/* ======================================================================================
 * The driver's surroundings (what usb.c and user/lib.h give it), and user/xhci.c itself
 * ====================================================================================== */

typedef unsigned long u64;
struct res { union { u64 x[7]; u64 status; }; };
enum { SYS_YIELD = 1, SYS_MAP = 2, SYS_SLEEP = 20, SYS_XHCI = 28 };   /* as in user/lib.h */
enum { OK = 0, NO_CAP = 1, BAD_ARG = 2 };
#define USB 6
#define DMA_PAGE 64
#define PAGE(n) (0x80000000UL + (n) * 4096UL)
#define DMA_PA (0x04000000UL + (256UL * 17 + 28) * 4096)
#define XH_VIEW ((const volatile unsigned *)(cpu + XOFF))
#define XH_RMB() __asm__ volatile("" ::: "memory")

struct line { char b[200]; u64 n; };
static void put_s(struct line *l, const char *s) { while (*s && l->n < sizeof l->b) l->b[l->n++] = *s++; }
static void put_hex(struct line *l, u64 v) {
    put_s(l, "0x");
    int started = 0;
    for (int i = 60; i >= 0; i -= 4) {
        int d = (v >> i) & 15;
        if ((d || started || i == 0) && l->n < sizeof l->b) { l->b[l->n++] = "0123456789abcdef"[d]; started = 1; }
    }
}
static void put_dec(struct line *l, u64 v) {
    char t[20];
    int i = 0;
    do { t[i++] = (char)('0' + v % 10); v /= 10; } while (v);
    while (i && l->n < sizeof l->b) l->b[l->n++] = t[--i];
}

struct usb { struct line l; unsigned char *dma; unsigned char prev[8]; int mx, my, buttons; };
static struct usb the_usb;

static void say(struct usb *u) {
    char b[210];
    memcpy(b, u->l.b, u->l.n);
    b[u->l.n] = 0;
    out(b);
    out("\n");
    u->l.n = 0;
}

/* usb.c's keyboard() and mouse(), as far as this test needs: what they were handed. */
static void keyboard(struct usb *u, const unsigned char *r, int n) {
    struct seen *g = &got[ngot++ % 4096];
    g->kind = 1;
    g->n = n;
    memcpy(g->b, r, n < 8 ? (size_t)n : 8);
    memcpy(g->prev, u->prev, 8);
    if (n < 8) return;
    for (int i = 0; i < 8; i++) u->prev[i] = r[i];
}
static void mouse(struct usb *u, const unsigned char *r, int n) {
    (void)u;
    struct seen *g = &got[ngot++ % 4096];
    g->kind = 2;
    g->n = n;
    memcpy(g->b, r, n < 8 ? (size_t)n : 8);
}

static u64 millis(void) { return now_us / 1000; }
static void sleep_ms(u64 ms) { advance((ms + 9) / 10 * 10000); }   /* whole 10 ms ticks */

/* The system calls: `xhci` goes to the Lean kernel, then to arch/xhci.c. */
static long calls, refused_calls, io_errors, by_op[6];
static const char *demo[4] = {0};
static int mapped;

static struct res sys(u64 n, u64 a0, u64 a1, u64 a2, u64 a3, u64 a4) {
    struct res r;
    memset(&r, 0, sizeof r);
    now_us += 3;
    step();
    if (n == SYS_YIELD) { advance(40); return r; }
    if (n == SYS_MAP) {
        if (a0 == 9 && a1 == 1024) mapped = 1;
        else r.status = BAD_ARG;
        return r;
    }
    if (n != SYS_XHCI) { failure("system call %lu", n); r.status = BAD_ARG; return r; }
    /* arch/kmain.c: x1 to x3 keep their low 63 bits (`carries_words`), x0 and x4 clamp at 2^40 */
    u64 cap = a0 < (1UL << 40) ? a0 : 1UL << 40, z = a4 < (1UL << 40) ? a4 : 1UL << 40;
    u64 op = a1 & ~(1UL << 63), x = a2 & ~(1UL << 63), y = a3 & ~(1UL << 63);
    fprintf(to_oracle, "x %lu %lu %lu %lu %lu\n", cap, op, x, y, z);
    char line[300];
    oracle_line(line, sizeof line);
    unsigned long long st, xop, A, B, C, D;
    if (sscanf(line, "%llu %llu %llu %llu %llu %llu", &st, &xop, &A, &B, &C, &D) != 6) { failure("the oracle said %s", line); exit(1); }
    calls++;
    if (op < 6) by_op[op]++;
    if (st != 0) {
        refused_calls++;
        char what[160];
        snprintf(what, sizeof what, "op %lu x %#lx y %#lx z %#lx", op, x, y, z);
        int expected = 0;
        for (int k = 0; k < 4; k++) if (demo[k] && !strcmp(demo[k], what)) expected = 1;
        if (!expected) failure("the kernel refused a request the driver made: %s (status %llu)", what, st);
        r.status = st;
        return r;
    }
    uint32_t v = 0;
    if (xop && !xhci_request(xop, A, B, C, D, &v)) { io_errors++; r.status = 5; return r; }
    r.x[1] = v;
    return r;
}
#define sys0(n) sys(n, 0, 0, 0, 0, 0)
#define sys2(n, a, b) sys(n, a, b, 0, 0, 0)

#include "../../user/xhci.c"

/* ======================================================================================
 * The scenario
 * ====================================================================================== */

#define D(...) ((const unsigned char[]){__VA_ARGS__})
static const unsigned char hub_dd[18] = {18, 1, 0, 2, 9, 0, 1, 64, 0x09, 0x21, 0x31, 0x34, 0, 1, 0, 0, 0, 1};
static const unsigned char hub_cd[25] = {9, 2, 25, 0, 1, 1, 0, 0xe0, 0, 9, 4, 0, 0, 1, 9, 0, 0, 0,
                                         7, 5, 0x81, 3, 1, 0, 12};
static const unsigned char kbd_dd[18] = {18, 1, 0x10, 1, 0, 0, 0, 8, 0x6d, 0x04, 0x1c, 0xc3, 0, 1, 0, 0, 0, 1};
static const unsigned char kbd_cd[34] = {9, 2, 34, 0, 1, 1, 0, 0xa0, 50, 9, 4, 0, 0, 1, 3, 1, 1, 0,
                                         9, 0x21, 0x11, 1, 0, 1, 0x22, 63, 0, 7, 5, 0x81, 3, 8, 0, 10};
static const unsigned char mouse_dd[18] = {18, 1, 0, 2, 0, 0, 0, 64, 0x6d, 0x04, 0x77, 0xc0, 0, 1, 0, 0, 0, 1};
static const unsigned char mouse_cd[34] = {9, 2, 34, 0, 1, 1, 0, 0xa0, 50, 9, 4, 0, 0, 1, 3, 1, 2, 0,
                                           9, 0x21, 0x11, 1, 0, 1, 0x22, 52, 0, 7, 5, 0x81, 3, 4, 0, 10};
/* a keyboard with a second, non-boot interface (media keys) first, its boot one on endpoint 2 */
static const unsigned char kbd2_dd[18] = {18, 1, 0, 2, 0, 0, 0, 8, 0x5e, 0x04, 0xdb, 0x07, 0, 1, 0, 0, 0, 1};
static const unsigned char kbd2_cd[59] = {9, 2, 59, 0, 2, 1, 0, 0xa0, 50,
                                          9, 4, 0, 0, 1, 3, 0, 0, 0, 9, 0x21, 0x11, 1, 0, 1, 0x22, 40, 0, 7, 5, 0x81, 3, 8, 0, 10,
                                          9, 4, 1, 0, 1, 3, 1, 1, 0, 9, 0x21, 0x11, 1, 0, 1, 0x22, 63, 0, 7, 5, 0x82, 3, 8, 0, 4};
/* a receiver: a boot keyboard (endpoint 1) and a boot mouse (endpoint 2) */
static const unsigned char combo_dd[18] = {18, 1, 0, 2, 0, 0, 0, 32, 0x6d, 0x04, 0x2b, 0xc5, 0, 1, 0, 0, 0, 1};
static const unsigned char combo_cd[59] = {9, 2, 59, 0, 2, 1, 0, 0xa0, 50,
                                           9, 4, 0, 0, 1, 3, 1, 1, 0, 9, 0x21, 0x11, 1, 0, 1, 0x22, 63, 0, 7, 5, 0x81, 3, 8, 0, 8,
                                           9, 4, 1, 0, 1, 3, 1, 2, 0, 9, 0x21, 0x11, 1, 0, 1, 0x22, 52, 0, 7, 5, 0x82, 3, 8, 0, 2};
static const unsigned char drive_dd[18] = {18, 1, 0, 3, 0, 0, 0, 9, 0x81, 0x07, 0x81, 0x55, 0, 1, 0, 0, 0, 1};

static struct dev hub, kbd, mouse_dev, kbd2, combo, drive;

static void make(struct dev *d, const char *name, int id, int speed, const unsigned char *dd, const unsigned char *cd, int clen) {
    memset(d, 0, sizeof *d);
    d->name = name;
    d->id = id;
    d->speed = speed;
    d->ddesc = dd;
    d->cdesc = cd;
    d->clen = clen;
    d->mps0 = dd[7] == 9 ? 512 : dd[7];
    /* its interrupt IN endpoints, from its own configuration */
    int iface = 0, kind = 0;
    for (int i = 0; i + 2 <= clen && cd[i] >= 2; i += cd[i]) {
        if (cd[i + 1] == 4) { iface = cd[i + 2]; kind = cd[i + 5] == 3 && cd[i + 6] == 1 ? cd[i + 7] : cd[i + 5] == 9 ? 3 : 0; }
        if (cd[i + 1] == 5 && (cd[i + 2] & 0x80) && (cd[i + 3] & 3) == 3 && d->nin < 2) {
            d->in[d->nin].num = cd[i + 2] & 15;
            d->in[d->nin].mps = cd[i + 4];
            d->in[d->nin].iface = iface;
            d->in[d->nin].kind = kind;
            d->nin++;
        }
    }
    d->protocol[0] = d->protocol[1] = 1;
}

/* A report from a device's endpoint of `kind` (1 keys, 2 mouse). */
static void press(struct dev *d, int kind, const unsigned char *b, int n) {
    for (int i = 0; i < d->nin; i++)
        if (d->in[i].kind == kind) {
            struct report *r = &d->in[i].q[d->in[i].tail++ % 512];
            memset(r, 0, sizeof *r);
            memcpy(r->b, b, (size_t)n);
            r->n = n;
            return;
        }
    failure("%s has no endpoint of kind %d", d->name, kind);
}

static int pending_reports(void) {
    struct dev *all[] = {&kbd, &mouse_dev, &kbd2, &combo};
    int n = 0;
    for (int k = 0; k < 4; k++)
        for (int i = 0; i < all[k]->nin; i++) n += all[k]->in[i].tail - all[k]->in[i].head;
    return n;
}

/* usb.c's loop: a poll every 8 ms, for `ms`, or until every report is delivered. */
static void run_for(int ms, int until_delivered) {
    for (int t = 0; t < ms; t += 8) {
        xhci_poll(&the_usb);
        advance(8000);
        if (until_delivered && !pending_reports() && ngot == nsent) {
            xhci_poll(&the_usb);
            return;
        }
    }
}

static int console_has(const char *line) {
    char want[300];
    snprintf(want, sizeof want, "\n%s\n", line);
    console[console_n] = 0;
    return strstr(console, want) != 0 || !strncmp(console, want + 1, strlen(want + 1));
}

static void expect_line(const char *line) {
    if (!console_has(line)) failure("no line \"%s\"", line);
}

static int keyboards_now(void) { return XH(&the_usb)->keyboards; }
static int mice_now(void) { return XH(&the_usb)->mice; }

/* The reports the driver handed on are exactly those the devices sent, in order; a keyboard's
   came with that keyboard's last report as the previous one. */
static void check_reports(const char *when) {
    if (ngot != nsent) { failure("%s: %d reports sent, %d handed on", when, nsent, ngot); return; }
    unsigned char last[16][8];
    memset(last, 0, sizeof last);
    for (int i = 0; i < ngot && i < 4096; i++) {
        struct seen *g = &got[i], *s = &sent[i];
        if (g->kind != s->kind || g->n != s->n || memcmp(g->b, s->b, (size_t)g->n)) {
            failure("%s: report %d: the %s sent %d bytes %02x %02x %02x, the driver handed on %d bytes %02x %02x %02x as the %s's", when, i,
                    s->kind == 1 ? "keyboard" : "mouse", s->n, s->b[0], s->b[1], s->b[2], g->n, g->b[0], g->b[1], g->b[2],
                    g->kind == 1 ? "keyboard" : "mouse");
            return;
        }
        if (g->kind == 1) {
            if (s->fresh) memset(last[s->dev], 0, 8);       /* plugged in again: nothing before */
            if (memcmp(g->prev, last[s->dev], 8)) { failure("%s: report %d: keyboard %d's previous report was not its own", when, i, s->dev); return; }
            memcpy(last[s->dev], g->b, 8);
        }
    }
}

static void reset_world(int csz) {
    memset(&X, 0, sizeof X);
    X.csz = csz;
    X.scratch = NSCRATCH;
    X.ports = NPORTS;
    for (int p = 1; p < NPORTS; p++) X.port[p].usb3 = 1;
    view_writable(1);
    memset(ram, 0, FRAMES_LEN);
    memset(cpu, 0, FRAMES_LEN);
    memset(snap, 0, FRAMES_LEN);
    view_writable(0);
    memset(trb_fresh, 0, sizeof trb_fresh);
    memset(&the_usb, 0, sizeof the_usb);
    the_usb.dma = cpu + 28 * 4096;
    ngot = nsent = 0;
    console_n = 0;
    mapped = 0;
}

/* What arch/kmain.c does: the probe at boot, then load_program's hooks around the frames being
   cleared and loaded. */
static void machine_boot(void) {
    if (!xhci_probe(BAR, 0x34831106u, 1)) { failure("the machine layer refused the model controller"); exit(1); }
    xhci_before_load();
    memset(ram, 0, FRAMES_LEN);
    if (!xhci_after_load(XMEM_PA)) { failure("the controller did not come out of reset"); exit(1); }
    view_writable(1);
    memcpy(cpu, ram, FRAMES_LEN);                         /* the kernel's stores are coherent */
    memcpy(snap, ram, FRAMES_LEN);
    view_writable(0);
    /* The boot content, placed for the context size: every endpoint context of every input
       context names the transfer rings, and the DCBAA and scratchpad array are full. */
    for (int ic = 0; ic < 16; ic++)
        for (unsigned c = 2; c < 33; c++) {
            uint64_t deq = rd64(ram + XOFF + (32 + (unsigned)ic) * 4096UL + c * ctxsz() + 8);
            if (deq != XMEM_PA + 48 * 4096UL) { failure("input context %d, context %u: dequeue pointer %#llx after boot", ic, c, (unsigned long long)deq); return; }
        }
    for (int k = 0; k < 256; k++) {
        uint64_t e = rd64(ram + XOFF + 8UL * (unsigned)k), sp = rd64(ram + XOFF + 2048 + 8UL * (unsigned)k);
        if (!e || !sp) { failure("DCBAA or scratchpad entry %d is 0 after boot", k); return; }
    }
}

static void scenario(int csz) {
    printf("---- the scenario, with %d-byte contexts ----\n", csz ? 64 : 32);
    reset_world(csz);
    make(&hub, "the hub", 0, 3, hub_dd, hub_cd, sizeof hub_cd);
    hub.hub = 1;
    hub.nports = 4;
    make(&kbd, "the keyboard", 1, 2, kbd_dd, kbd_cd, sizeof kbd_cd);
    make(&mouse_dev, "the mouse", 2, 1, mouse_dd, mouse_cd, sizeof mouse_cd);
    make(&kbd2, "the second keyboard", 3, 1, kbd2_dd, kbd2_cd, sizeof kbd2_cd);
    kbd2.stall_idle = 1;
    make(&combo, "the receiver", 4, 1, combo_dd, combo_cd, sizeof combo_cd);
    combo.stall_idle = 1;                 /* endpoint 0 must work again for its mouse's SET_PROTOCOL */
    make(&drive, "the USB 3 drive", 5, 4, drive_dd, hub_cd, sizeof hub_cd);
    attach_root(1, &hub);
    attach_root(3, &drive);
    attach_hub(&hub, 1, &kbd);
    attach_hub(&hub, 3, &mouse_dev);

    machine_boot();
    xhci_start(&the_usb);
    if (!mapped) failure("the driver did not map its xHCI memory");
    for (const char *const *l = (const char *const[]){
             "usb: xHCI: refused, as proved: a TRB aimed at the display's memory, DCBAAP, Run/Stop, a Link out of its ring",
             "usb: xHCI: running, 5 ports, 16 device slots, DMA checked by the kernel", "usb: xHCI: port 1: a high-speed device",
             "usb: xHCI: hub on port 1, 4 ports", "usb: xHCI: keyboard on port 1.1", "usb: xHCI: mouse on port 1.3",
             "usb: xHCI: port 3: a USB 3 device, not a keyboard or mouse; left alone", "usb: xHCI: ready, 1 keyboard, 1 mouse", 0};
         *l; l++)
        expect_line(*l);

    /* Typing and moving: "Hi", a move, a click. */
    press(&kbd, 1, D(0x02, 0, 0x0b, 0, 0, 0, 0, 0), 8);
    press(&kbd, 1, D(0, 0, 0, 0, 0, 0, 0, 0), 8);
    press(&kbd, 1, D(0, 0, 0x0c, 0, 0, 0, 0, 0), 8);
    press(&kbd, 1, D(0, 0, 0, 0, 0, 0, 0, 0), 8);
    press(&mouse_dev, 2, D(0, 10, 0xfb), 3);
    press(&mouse_dev, 2, D(1, 0, 0), 3);
    press(&mouse_dev, 2, D(0, 0, 0), 3);
    run_for(2000, 1);
    check_reports("typing");

    /* Unplugged, and another keyboard (which stalls SET_IDLE, and has a media-key interface
       before its boot one) plugged into another port. */
    detach_hub(&hub, 1);
    run_for(1000, 0);
    expect_line("usb: xHCI: keyboard on port 1.1 unplugged");
    attach_hub(&hub, 2, &kbd2);
    run_for(1500, 0);
    expect_line("usb: xHCI: keyboard on port 1.2");
    attach_hub(&hub, 4, &combo);
    run_for(1500, 0);
    expect_line("usb: xHCI: keyboard on port 1.4");
    expect_line("usb: xHCI: mouse on port 1.4");
    press(&kbd2, 1, D(0, 0, 0x04, 0, 0, 0, 0, 0), 8);
    press(&combo, 1, D(0, 0, 0x05, 0, 0, 0, 0, 0), 8);
    press(&kbd2, 1, D(0, 0, 0x04, 0x06, 0, 0, 0, 0), 8);
    press(&combo, 2, D(0, 0xff, 1), 3);
    press(&combo, 1, D(0, 0, 0, 0, 0, 0, 0, 0), 8);
    press(&kbd2, 1, D(0, 0, 0, 0, 0, 0, 0, 0), 8);
    run_for(2000, 1);
    check_reports("two keyboards");
    if (keyboards_now() != 2 || mice_now() != 2) failure("%d keyboards and %d mice, not 2 and 2", keyboards_now(), mice_now());

    /* The mouse, unplugged and plugged back 100 times: its slot again each time, endpoint 0's
       ring and the command ring round and round. */
    for (int k = 0; k < 100; k++) {
        detach_hub(&hub, 3);
        run_for(600, 0);
        attach_hub(&hub, 3, &mouse_dev);
        run_for(900, 0);
        press(&mouse_dev, 2, D(0, (unsigned char)k, 0), 3);
        run_for(500, 1);
    }
    check_reports("plugging");
    if (mice_now() != 2) failure("%d mice after plugging the mouse again and again", mice_now());
    /* Held keys: 300 reports, round the interrupt rings and the event ring. */
    for (int k = 0; k < 150; k++) {
        press(&kbd2, 1, D(0, 0, (unsigned char)(4 + k % 26), 0, 0, 0, 0, 0), 8);
        press(&combo, 1, D(0, 0, (unsigned char)(4 + (k + 7) % 26), 0, 0, 0, 0, 0), 8);
    }
    run_for(20000, 1);
    check_reports("held keys");

    /* The whole hub unplugged, then plugged back with what hangs off it. */
    detach_root(1);
    run_for(2000, 0);
    expect_line("usb: xHCI: hub on port 1 unplugged");
    if (keyboards_now() || mice_now()) failure("%d keyboards and %d mice with the hub gone", keyboards_now(), mice_now());
    attach_root(1, &hub);
    run_for(4000, 0);
    if (keyboards_now() != 2 || mice_now() != 2) failure("%d keyboards and %d mice with the hub back", keyboards_now(), mice_now());
    press(&kbd2, 1, D(0, 0, 0x0b, 0, 0, 0, 0, 0), 8);
    press(&mouse_dev, 2, D(0, 3, 3), 3);
    press(&combo, 2, D(1, 0, 0), 3);
    run_for(2000, 1);
    check_reports("the hub again");

    struct xhci *x = XH(&the_usb);
    printf("  %d events, %d commands (the command ring went round %u times), %d transfers; %ld system calls\n", X.events,
           X.commands, (unsigned)(X.commands / 255), X.transfers, calls);
    if (X.commands < 2 * 255) failure("only %d commands: the command ring did not go round twice", X.commands);
    if (X.events < 2 * 256) failure("only %d events: the event ring did not go round twice", X.events);
    if (!x->on) failure("the driver turned the controller off");
}

/* Controllers the machine layer must refuse, each with a line saying why. */
static void refusals(void) {
    printf("---- controllers the machine layer must keep off ----\n");
    struct { const char *what, *why; int ports, scratch, bar; } cases[] = {
        {"4 ports", "it has fewer than 5 ports", 4, NSCRATCH, BAR},
        {"13 scratchpad pages", "it wants more than 12 scratchpad pages", NPORTS, 13, BAR},
        {"registers of 2 KiB", "its registers are smaller than 4 KiB", NPORTS, NSCRATCH, 0x800},
    };
    quiet = 1;
    for (unsigned k = 0; k < sizeof cases / sizeof cases[0]; k++) {
        reset_world(0);
        X.ports = cases[k].ports;
        X.scratch = cases[k].scratch;
        int r = xhci_probe((uint64_t)cases[k].bar, 0x34831106u, 1);
        char want[200];
        snprintf(want, sizeof want, "leanos: xHCI: refused: %s; the USB-A ports are off", cases[k].why);
        if (r || !console_has(want)) failure("a controller with %s was not refused as it should be", cases[k].what);
        else printf("  refused, with %s: \"%s\"\n", cases[k].what, want);
        uint32_t v;
        if (xhci_request(1, 0x10004, 0, 0, 0, &v)) failure("a refused controller still took a request");
    }
    quiet = 0;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: sim ORACLE-COMMAND...\n"); return 2; }
    setvbuf(stdout, 0, _IOLBF, 0);
    oracle_start(argv + 1);
    oracle_boot();
    ram = mmap(0, FRAMES_LEN, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    cpu = mmap(0, FRAMES_LEN, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    snap = mmap(0, FRAMES_LEN, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (ram == MAP_FAILED || cpu == MAP_FAILED || snap == MAP_FAILED) { perror("mmap"); return 2; }
    demo[0] = "op 3 x 0x4100000 y 0x40000000008 z 0x100";
    demo[1] = "op 1 x 0 y 0 z 0x10030";
    demo[2] = "op 1 x 0x1 y 0 z 0x10000";
    demo[3] = "op 3 x 0x51f0000 y 0x180000000000 z 0x5";
    scenario(0);
    scenario(1);
    refusals();
    printf("---- %ld xhci calls: %ld reads, %ld writes, %ld runs, %ld TRBs, %ld input context writes, %ld cache syncs; "
           "%ld refused (the 4 tried on purpose), %ld I/O errors ----\n",
           calls, by_op[0], by_op[1], by_op[2], by_op[3], by_op[4], by_op[5], refused_calls, io_errors);
    if (refused_calls != 8) failure("%ld requests refused, not the 4 the driver tries on purpose (twice)", refused_calls);
    if (io_errors) failure("%ld requests failed in the machine layer", io_errors);
    fclose(to_oracle);
    wait(0);
    if (violations || failures) {
        printf("FAIL: %d violations, %d failed checks\n", violations, failures);
        return 1;
    }
    printf("ok: the xHCI driver, the machine layer and the kernel's checks, against the controller model: "
           "every request allowed, every report delivered, nothing touched outside its place\n");
    return 0;
}
