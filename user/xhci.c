/* The USB-A ports: keyboards and mice on the Pi 4's VL805 xHCI controller, behind the PCIe
   bridge. Included by usb.c, whose HID boot keyboard and mouse handling (`keyboard`, `mouse`)
   it feeds; test/xhci-sim/ compiles it for the host against a model of the controller.

   An xHCI controller finds its work in memory (rings of TRBs, contexts, tables), and many of
   those hold DMA addresses, so this driver writes none of them. They are in the xHCI memory,
   the last 64 of its frames, which it holds read-only (capability 9); the kernel writes them
   for it, one TRB or 16 bytes of an input context at a time, after checking every address
   (`xhci`, `sysXhci` in LeanOS/Kernel.lean: `xhci_dma_own_memory`). The layout is fixed:

     page 2       the event ring, 256 TRBs, which the controller writes and this reads
     page 3       the command ring, 256 TRBs, the last a Link back to its start
     pages 32-47  16 input contexts: slot s uses number s - 1
     pages 48-63  the transfer rings: here 48 rings of 64 TRBs, each ending in a Link back to
                  its start (slot s: ring 3(s - 1) for endpoint 0, the next two for its
                  interrupt endpoints); the rest unused, so the last TRB of the area, which
                  only ever holds the Link back to the area's start, is never reached, and
                  neither is the end of the area (the VL805 reads ahead of a ring's end)

   Every buffer is in the spare run: this code's pages are 144 to 147 of it (its state, a
   control transfer's data, the interrupt reports). Before a transfer and after it, before
   reading what came in, the cache is made consistent over the buffer (`xhci` op 5), which
   also does the event ring and the device contexts.

   What it knows: root ports (USB 2 ones reset, USB 3 ones left alone: no keyboard or mouse is
   a USB 3 device), hubs at any depth up to four (the Pi 4's USB 2 lines all go through one,
   on the VL805's first port), their ports' changes through the hub's status endpoint, and
   devices plugged and unplugged at any time; HID keyboards and mice in the boot protocol, up
   to two in one device (a receiver for both). */

#ifndef COLD
#define COLD __attribute__((cold, minsize))
#endif

#define XH_CAP 9                      /* capability 9: the xHCI memory, read-only */
#define XH_PAGE 1024                  /* where it is mapped */
#define XH_PA (0x04000000UL + (256UL * 17 + 192) * 4096)   /* its physical address */
#define XH_EVENTS (XH_PA + 2 * 4096UL)
#define XH_CMD (XH_PA + 3 * 4096UL)
#define XH_IN (XH_PA + 32 * 4096UL)
#define XH_RINGS (XH_PA + 48 * 4096UL)
#define XH_OFF (144 * 4096)           /* this code's pages in the spare run */
#ifndef XH_VIEW
#define XH_VIEW ((const volatile unsigned *)PAGE(XH_PAGE))
#endif
/* Loads of an event's words after its control word (with its cycle bit) are not made first. */
#ifndef XH_RMB
#define XH_RMB() __asm__ volatile("dmb ishld" ::: "memory")
#endif

/* Registers, as the kernel names them: space << 16 | offset (`xSpace`, `xOff`). */
#define XR_OP(o) (0x10000UL | (o))
#define XR_RT(o) (0x20000UL | (o))
#define XR_DB(n) (0x30000UL | 4UL * (n))
#define USBCMD XR_OP(0x00)
#define USBSTS XR_OP(0x04)
#define CONFIG XR_OP(0x38)
#define PORTSC(p) XR_OP(0x400 + 0x10 * ((p) - 1))
#define ERDP XR_RT(0x38)
#define STS_HCH 1u
#define STS_HSE 4u
#define STS_CNR (1u << 11)
#define PORT_CCS 1u
#define PORT_PED 2u
#define PORT_PR 16u
#define PORT_PP (1u << 9)
#define PORT_KEEP (PORT_PP | 3u << 14 | 7u << 25)   /* written back as read: power, indicator, wake */
#define PORT_CHANGES 0x00FE0000u                    /* CSC to CEC: write 1 to clear */
#define PORT_CSC (1u << 17)
#define PORT_PRC (1u << 21)

enum { T_NORMAL = 1, T_SETUP = 2, T_DATA = 3, T_STATUS = 4, T_LINK = 6, T_NOOP = 8, T_ENABLE = 9,
       T_DISABLE = 10, T_ADDRESS = 11, T_CONFIGURE = 12, T_EVALUATE = 13, T_RESET_EP = 14,
       T_STOP_EP = 15, T_SET_DEQ = 16, T_NOOP_CMD = 23, E_TRANSFER = 32, E_COMMAND = 33, E_PORT = 34 };
enum { F_ISP = 4, F_IOC = 32, F_IDT = 64, F_IN = 1 << 16 };
enum { CC_SUCCESS = 1, CC_SHORT = 13, CC_CONTEXT_STATE = 19 };
enum { SP_FULL = 1, SP_LOW = 2, SP_HIGH = 3 };
enum { K_KEYBOARD = 1, K_MOUSE = 2, K_HUB = 3 };

#define XH_SLOTS 16
#define XH_RING 64                    /* TRBs in each transfer ring, the Link included */

/* An interrupt IN endpoint: a keyboard's or mouse's reports, or a hub's port changes. */
struct xhid {
    unsigned char kind, ep, dci, len, interval, iface, armed, failed, errors;
    unsigned char prev[8];            /* a keyboard's last report */
    u64 trb;                          /* the TRB waiting for a report */
};
struct xdev {
    unsigned char slot, speed, root, depth, parent, port, nports, ttt;
    unsigned char tt_slot, tt_port, mps0, nhid, hub, ring0;
    unsigned route, pending;          /* a hub's ports with changes */
    struct xhid hid[2];
};
struct xring { unsigned enq, cycle; };
struct xhci {
    int on, busy, ports, errors, recover, keyboards, mice, spoke;
    unsigned cmd_enq, cmd_cycle, ev_deq, ev_cycle, root_pending;
    /* the command being waited for, and the control transfer */
    int cmd_done, ctl_done;
    unsigned cmd_cc, cmd_slot, ctl_cc, ctl_left, ctl_slot;
    u64 cmd_trb, ctl_setup, ctl_data, ctl_status, next_scan;
    struct xring ring[3 * XH_SLOTS];
    struct xdev dev[XH_SLOTS];        /* by slot - 1 */
};

#define XH(u) ((struct xhci *)((u)->dma + XH_OFF))
#define XH_CTL(u) ((u)->dma + XH_OFF + 2 * 4096)
#define XH_RPT(u) ((u)->dma + XH_OFF + 3 * 4096)

static u64 xpa(struct usb *u, const void *p) { return DMA_PA + (u64)((const unsigned char *)p - u->dma); }

/* ---- the system call, and what it does ---- */

static u64 xh_sys(struct xhci *x, u64 op, u64 a, u64 b, u64 c, u64 *v) {
    struct res r = sys(SYS_XHCI, USB, op, a, b, c);
    if (r.status != OK) x->errors++;
    if (v) *v = r.x[1];
    return r.status;
}

static unsigned xr(struct xhci *x, u64 reg) {
    u64 v = 0;
    return xh_sys(x, 0, 0, 0, reg, &v) == OK ? (unsigned)v : 0xffffffffu;
}
static void xw(struct xhci *x, u64 reg, u64 v) { xh_sys(x, 1, v, 0, reg, 0); }
/* 16 bytes at byte 16w of context c of input context `ic` */
static void xh_ctx(struct xhci *x, unsigned ic, unsigned c, unsigned w, u64 lo, u64 hi) {
    xh_sys(x, 4, lo, hi, ic * 4096UL + 64 * c + 16 * w, 0);
}
static void xh_sync(struct usb *u, struct xhci *x, const void *p, u64 n) { xh_sys(x, 5, xpa(u, p), n, 0, 0); }

static u64 xh_ring_at(unsigned r, unsigned i) { return XH_RINGS + 16UL * (XH_RING * r + i); }

/* Put a TRB on ring `r` (-1: the command ring) with the ring's cycle bit; at its last slot,
   the Link back to its start, and the other cycle. Its address. */
static u64 xh_put(struct xhci *x, int r, u64 p, unsigned status, unsigned control) {
    unsigned n = r < 0 ? 256 : XH_RING, *enq = r < 0 ? &x->cmd_enq : &x->ring[r].enq;
    unsigned *cyc = r < 0 ? &x->cmd_cycle : &x->ring[r].cycle;
    u64 base = r < 0 ? XH_CMD : xh_ring_at((unsigned)r, 0), k0 = r < 0 ? 0 : 256 + XH_RING * (u64)r;
    u64 at = base + 16UL * *enq;
    xh_sys(x, 3, p, (u64)status | (u64)(control | *cyc) << 32, k0 + *enq, 0);
    if (++*enq == n - 1) {
        xh_sys(x, 3, base, (u64)(T_LINK << 10 | 2 | *cyc) << 32, k0 + n - 1, 0);   /* toggle cycle */
        *cyc ^= 1;
        *enq = 0;
    }
    return at;
}

static void xh_where(struct line *l, const struct xdev *d) {
    put_s(l, "port ");
    put_dec(l, d->root);
    for (unsigned k = 0; k < d->depth; k++) {
        put_s(l, ".");
        put_dec(l, d->route >> (4 * k) & 15);
    }
}

static const char *xh_kind(unsigned k) { return k == K_KEYBOARD ? "keyboard" : k == K_MOUSE ? "mouse" : "hub"; }

/* ---- events ---- */

static void xh_arm(struct usb *u, struct xhci *x, struct xdev *d, int i) {
    struct xhid *h = &d->hid[i];
    unsigned char *b = XH_RPT(u) + (d->slot - 1) * 128 + 64 * i;
    h->trb = xh_put(x, d->ring0 + 1 + i, xpa(u, b), h->len, T_NORMAL << 10 | F_IOC);
    h->armed = 1;
    xw(x, XR_DB(d->slot), h->dci);
}

/* A report came in: to usb.c's keyboard or mouse handling (each keyboard with the last report
   it sent, as keys are new only against it), or a hub's changed ports, for `xhci_poll`. */
static void xh_report(struct usb *u, struct xhci *x, struct xdev *d, struct xhid *h, const unsigned char *r, int n) {
    if (h->kind == K_KEYBOARD) {
        unsigned char keep[8];
        for (int k = 0; k < 8; k++) { keep[k] = u->prev[k]; u->prev[k] = h->prev[k]; }
        keyboard(u, r, n);
        for (int k = 0; k < 8; k++) { h->prev[k] = u->prev[k]; u->prev[k] = keep[k]; }
    } else if (h->kind == K_MOUSE) {
        mouse(u, r, n);
    } else {
        d->pending |= (unsigned)r[0] | (n > 1 ? (unsigned)r[1] << 8 : 0);
    }
}

static void xh_event(struct usb *u, struct xhci *x, u64 p, unsigned st, unsigned ctl) {
    unsigned type = ctl >> 10 & 63, cc = st >> 24, slot = ctl >> 24;
    if (type == E_COMMAND) {
        if (p == x->cmd_trb && !x->cmd_done) { x->cmd_cc = cc; x->cmd_slot = slot; x->cmd_done = 1; }
        return;
    }
    if (type == E_PORT) {
        unsigned port = (unsigned)(p >> 24) & 0xff;
        if (port >= 1 && port <= 31) x->root_pending |= 1u << port;
        return;
    }
    if (type != E_TRANSFER || slot < 1 || slot > XH_SLOTS) return;
    unsigned dci = ctl >> 16 & 31, left = st & 0xffffff;
    if (slot == x->ctl_slot && dci == 1 && !x->ctl_done &&
        (p == x->ctl_setup || (p == x->ctl_data && x->ctl_data) || p == x->ctl_status)) {
        if (p == x->ctl_data && (cc == CC_SUCCESS || cc == CC_SHORT)) x->ctl_left = left;
        else if (p == x->ctl_status || cc != CC_SUCCESS) { x->ctl_cc = cc; x->ctl_done = 1; }
        return;
    }
    struct xdev *d = &x->dev[slot - 1];
    for (int i = 0; d->slot && i < d->nhid; i++) {
        struct xhid *h = &d->hid[i];
        if (h->dci != dci || !h->armed || p != h->trb) continue;
        h->armed = 0;
        if (cc == CC_SUCCESS || cc == CC_SHORT) {
            int n = left < h->len ? (int)(h->len - left) : 0;
            h->errors = 0;
            xh_report(u, x, d, h, XH_RPT(u) + (slot - 1) * 128 + 64 * i, n);
            xh_arm(u, x, d, i);
        } else {
            h->failed = 1;                /* xhci_poll resets the endpoint and asks again */
            x->recover = 1;
        }
        return;
    }
}

/* Take what the controller wrote on the event ring, and tell it how far (ERDP). */
static void xh_events(struct usb *u, struct xhci *x) {
    struct { u64 p; unsigned st, ctl; } ev[16];
    for (int round = 0; round < 32; round++) {
        xh_sync(u, x, x, 0);              /* the event ring, fresh */
        int n = 0, reports = 0;
        while (n < 16) {
            const volatile unsigned *e = XH_VIEW + 2 * 1024 + 4 * x->ev_deq;
            unsigned ctl = e[3];
            if ((ctl & 1) != x->ev_cycle) break;
            XH_RMB();
            ev[n].p = e[0] | (u64)e[1] << 32;
            ev[n].st = e[2];
            ev[n].ctl = ctl;
            reports |= (ctl >> 10 & 63) == E_TRANSFER && (ctl >> 16 & 31) != 1;
            n++;
            if (++x->ev_deq == 256) {
                x->ev_deq = 0;
                x->ev_cycle ^= 1;
            }
        }
        if (!n) return;
        xw(x, ERDP, (XH_EVENTS + 16UL * x->ev_deq) | 8);     /* and clear Event Handler Busy */
        if (reports) xh_sync(u, x, XH_RPT(u), 4096);         /* the reports, fresh */
        for (int i = 0; i < n; i++) xh_event(u, x, ev[i].p, ev[i].st, ev[i].ctl);
        if (n < 16) return;
    }
}

/* Wait up to `ms` for *flag, taking events meanwhile: 1 if it came. */
static int xh_wait(struct usb *u, struct xhci *x, const int *flag, u64 ms) {
    u64 until = millis() + ms;
    for (int spin = 0; !*flag; spin++) {
        xh_events(u, x);
        if (*flag) break;
        if (millis() > until) return 0;
        if (spin < 40) sys0(SYS_YIELD);
        else sleep_ms(1);
    }
    return 1;
}

/* A command: its completion code (0 if none came: the controller is off from then on). */
static unsigned xh_cmd(struct usb *u, struct xhci *x, u64 p, unsigned control) {
    if (!x->on) return 0;
    x->cmd_done = 0;
    x->cmd_slot = 0;
    x->cmd_trb = xh_put(x, -1, p, 0, control);
    xw(x, XR_DB(0), 0);
    if (xh_wait(u, x, &x->cmd_done, 3000)) return x->cmd_cc;
    put_s(&u->l, "usb: xHCI: the controller did not answer a command; the USB-A ports are off");
    say(u);
    x->on = 0;
    return 0;
}

/* Endpoint `dci` of `d` halted (or stopped answering): reset it, and start it again at the
   end of its ring, past whatever it did not finish. 1 if it is ready again. */
static int xh_restart(struct usb *u, struct xhci *x, struct xdev *d, unsigned dci, unsigned ring) {
    unsigned cmd = (unsigned)d->slot << 24 | dci << 16;
    if (xh_cmd(u, x, 0, T_RESET_EP << 10 | cmd) == CC_CONTEXT_STATE)   /* not halted: stop it */
        xh_cmd(u, x, 0, T_STOP_EP << 10 | cmd);
    u64 deq = xh_ring_at(ring, x->ring[ring].enq) | x->ring[ring].cycle;
    return xh_cmd(u, x, deq, T_SET_DEQ << 10 | cmd) == CC_SUCCESS;
}

/* A control transfer on endpoint 0: setup, data (in `XH_CTL`, if any), status. The bytes of
   data moved, or -1. */
static int xh_control(struct usb *u, struct xhci *x, struct xdev *d, unsigned type, unsigned req,
                      unsigned value, unsigned index, unsigned len) {
    if (!x->on) return -1;
    unsigned char *buf = XH_CTL(u);
    int in = (type & 0x80) != 0;
    u64 setup = type | req << 8 | (u64)value << 16 | (u64)index << 32 | (u64)len << 48;
    xh_sync(u, x, buf, 1024);
    x->ctl_slot = d->slot;
    x->ctl_done = 0;
    x->ctl_left = 0;
    x->ctl_data = 0;
    unsigned r = d->ring0;
    x->ctl_setup = xh_put(x, (int)r, setup, 8, T_SETUP << 10 | F_IDT | (len ? (in ? 3u : 2u) : 0u) << 16);
    if (len) x->ctl_data = xh_put(x, (int)r, xpa(u, buf), len, T_DATA << 10 | F_IOC | (in ? F_IN : 0));
    x->ctl_status = xh_put(x, (int)r, 0, 0, T_STATUS << 10 | F_IOC | (in && len ? 0 : F_IN));
    xw(x, XR_DB(d->slot), 1);
    int done = xh_wait(u, x, &x->ctl_done, 1000);
    x->ctl_slot = 0;
    if (!done || x->ctl_cc != CC_SUCCESS) {
        if (x->on) xh_restart(u, x, d, 1, r);
        return -1;
    }
    xh_sync(u, x, buf, 1024);
    return x->ctl_left < len ? (int)(len - x->ctl_left) : 0;
}

/* ---- input contexts: slot s - 1's; context 0 the control, 1 the slot, 1 + DCI an endpoint ---- */

static void xh_ctl_ctx(struct xhci *x, unsigned ic, unsigned add) {
    xh_ctx(x, ic, 0, 0, (u64)add << 32, 0);          /* drop nothing */
    xh_ctx(x, ic, 0, 1, 0, 0);
}

static void xh_slot_ctx(struct xhci *x, const struct xdev *d, unsigned entries) {
    u64 w0 = d->route | (u64)d->speed << 20 | (u64)(d->hub && d->nports) << 26 | (u64)entries << 27;
    u64 w1 = (u64)d->root << 16 | (u64)d->nports << 24;
    u64 w2 = d->tt_slot | (u64)d->tt_port << 8 | (u64)d->ttt << 16;   /* interrupter 0 */
    xh_ctx(x, d->slot - 1u, 1, 0, w0 | w1 << 32, w2);
    xh_ctx(x, d->slot - 1u, 1, 1, 0, 0);
}

/* Endpoint context `dci`: type 4 control, 7 interrupt in; its ring from where it is now. */
static void xh_ep_ctx(struct xhci *x, const struct xdev *d, unsigned dci, unsigned type, unsigned mps,
                      unsigned interval, unsigned ring) {
    u64 w0 = (u64)interval << 16, w1 = 3u << 1 | type << 3 | (u64)mps << 16;   /* three tries */
    u64 deq = xh_ring_at(ring, x->ring[ring].enq) | x->ring[ring].cycle;
    unsigned avg = type == 4 ? 8 : mps;
    xh_ctx(x, d->slot - 1u, dci + 1, 0, w0 | w1 << 32, deq);
    xh_ctx(x, d->slot - 1u, dci + 1, 1, avg | (u64)(type == 4 ? 0 : mps) << 16, 0);
}

static u64 xh_input(const struct xdev *d) { return XH_IN + 4096UL * (d->slot - 1u); }

/* ---- devices ---- */

static struct xdev *xh_child(struct xhci *x, unsigned parent, unsigned root, unsigned port) {
    for (int i = 0; i < XH_SLOTS; i++) {
        struct xdev *d = &x->dev[i];
        if (d->slot && d->parent == parent && (parent ? d->port == port : d->root == root && d->depth == 0))
            return d;
    }
    return 0;
}

COLD static void xh_say(struct usb *u, const struct xdev *d, const char *what) {
    put_s(&u->l, "usb: xHCI: ");
    put_s(&u->l, what);
    put_s(&u->l, " on ");
    xh_where(&u->l, d);
    say(u);
}

/* It was unplugged (or its hub was): what hangs off it first, then its slot. */
COLD static void xh_remove(struct usb *u, struct xhci *x, struct xdev *d) {
    for (int i = 0; i < XH_SLOTS; i++)
        if (x->dev[i].slot && x->dev[i].parent == d->slot) xh_remove(u, x, &x->dev[i]);
    put_s(&u->l, "usb: xHCI: ");
    put_s(&u->l, d->hub ? "hub" : d->nhid ? xh_kind(d->hid[0].kind) : "device");
    for (int i = 1; i < d->nhid; i++) { put_s(&u->l, " and "); put_s(&u->l, xh_kind(d->hid[i].kind)); }
    put_s(&u->l, " on ");
    xh_where(&u->l, d);
    put_s(&u->l, " unplugged");
    say(u);
    for (int i = 0; i < d->nhid; i++) {
        if (d->hid[i].kind == K_KEYBOARD) x->keyboards--;
        if (d->hid[i].kind == K_MOUSE) x->mice--;
    }
    unsigned slot = d->slot;
    memset(d, 0, sizeof *d);
    xh_cmd(u, x, 0, T_DISABLE << 10 | slot << 24);
}

static void xh_hub_port(struct usb *u, struct xhci *x, struct xdev *hub, unsigned p);

/* A device just reset on root port `root` (hub = 0) or on port `port` of `hub`: a slot, an
   address, what it is; configured if it is a hub, a keyboard or a mouse. */
COLD static void xh_enumerate(struct usb *u, struct xhci *x, struct xdev *hub, unsigned root, unsigned port,
                              unsigned speed) {
    unsigned depth = hub ? hub->depth + 1u : 0;
    if (depth > 4) return;
    unsigned cc = xh_cmd(u, x, 0, T_ENABLE << 10), slot = x->cmd_slot;
    if (cc != CC_SUCCESS || slot < 1 || slot > XH_SLOTS) {
        if (cc == CC_SUCCESS && slot) xh_cmd(u, x, 0, T_DISABLE << 10 | slot << 24);
        put_s(&u->l, "usb: xHCI: no device slot (completion code ");
        put_dec(&u->l, cc);
        put_s(&u->l, ")");
        say(u);
        return;
    }
    struct xdev *d = &x->dev[slot - 1];
    memset(d, 0, sizeof *d);
    d->slot = (unsigned char)slot;
    d->speed = (unsigned char)speed;
    d->root = (unsigned char)root;
    d->depth = (unsigned char)depth;
    d->parent = hub ? hub->slot : 0;
    d->port = (unsigned char)port;
    d->route = hub ? hub->route | (port > 15 ? 15u : port) << (4 * hub->depth) : 0;
    if (hub && hub->speed == SP_HIGH && speed != SP_HIGH) {   /* through the hub's transaction translator */
        d->tt_slot = hub->slot;
        d->tt_port = (unsigned char)port;
    } else if (hub) {
        d->tt_slot = hub->tt_slot;
        d->tt_port = hub->tt_port;
    }
    d->ring0 = (unsigned char)(3 * (slot - 1));
    d->mps0 = speed == SP_HIGH ? 64 : 8;
    xh_ctl_ctx(x, slot - 1, 3);                            /* the slot and endpoint 0 */
    xh_slot_ctx(x, d, 1);
    xh_ep_ctx(x, d, 1, 4, d->mps0, 0, d->ring0);
    cc = xh_cmd(u, x, xh_input(d), T_ADDRESS << 10 | slot << 24);
    unsigned char *b = XH_CTL(u);
    const char *why = 0;
    if (cc != CC_SUCCESS) why = "no address";
    else {
        sleep_ms(10);
        if (xh_control(u, x, d, 0x80, 6, 1 << 8, 0, 8) < 8) why = "no answer";
    }
    /* A full-speed device's endpoint 0 may take up to 64 bytes a packet: the controller is told. */
    if (!why && speed == SP_FULL && b[7] != d->mps0 && (b[7] == 16 || b[7] == 32 || b[7] == 64)) {
        d->mps0 = b[7];
        xh_ctl_ctx(x, slot - 1, 2);
        xh_ep_ctx(x, d, 1, 4, d->mps0, 0, d->ring0);
        if (xh_cmd(u, x, xh_input(d), T_EVALUATE << 10 | slot << 24) != CC_SUCCESS) why = "no packet size";
    }
    if (!why && xh_control(u, x, d, 0x80, 6, 1 << 8, 0, 18) < 18) why = "no device descriptor";
    unsigned cls = b[4];
    if (!why && xh_control(u, x, d, 0x80, 6, 2 << 8, 0, 9) < 9) why = "no configuration";
    unsigned total = b[2] | b[3] << 8;
    if (total > 1024) total = 1024;
    int got = why ? -1 : xh_control(u, x, d, 0x80, 6, 2 << 8, 0, total);
    if (!why && got < 9) why = "no configuration";
    if (why) {
        put_s(&u->l, "usb: xHCI: ");
        xh_where(&u->l, d);
        put_s(&u->l, ": ");
        put_s(&u->l, why);
        if (cc != CC_SUCCESS) { put_s(&u->l, " (completion code "); put_dec(&u->l, cc); put_s(&u->l, ")"); }
        say(u);
        memset(d, 0, sizeof *d);
        xh_cmd(u, x, 0, T_DISABLE << 10 | slot << 24);
        return;
    }
    /* Its interfaces: a hub, or up to two boot keyboards and mice, each with an interrupt IN
       endpoint of at most 64 bytes a report. */
    unsigned config = b[5], kind = 0, iface = 0, maxdci = 1;
    d->hub = cls == 9;
    for (int i = 0; i + 2 <= got && b[i] >= 2; i += b[i]) {
        if (b[i + 1] == 4 && i + 9 <= got) {
            iface = b[i + 2];
            kind = 0;
            if (b[i + 3] != 0) continue;                      /* alternate settings: not these */
            if (b[i + 5] == 9) {
                d->hub = 1;
                kind = K_HUB;
            } else if (b[i + 5] == 3 && b[i + 6] == 1 && (b[i + 7] == 1 || b[i + 7] == 2)) kind = b[i + 7];
        } else if (b[i + 1] == 5 && i + 7 <= got && kind && (b[i + 2] & 0x80) && (b[i + 3] & 3) == 3 && d->nhid < 2) {
            unsigned mps = (b[i + 4] | b[i + 5] << 8) & 0x7ff, ival = b[i + 6], e = b[i + 2] & 15;
            if (mps == 0 || mps > 64 || e == 0) { kind = 0; continue; }
            struct xhid *h = &d->hid[d->nhid++];
            h->kind = (unsigned char)kind;
            h->ep = (unsigned char)e;
            h->dci = (unsigned char)(2 * e + 1);
            h->len = (unsigned char)mps;
            h->iface = (unsigned char)iface;
            if (speed == SP_HIGH) h->interval = (unsigned char)(ival < 1 ? 0 : ival > 16 ? 15 : ival - 1);
            else {                        /* frames of 1 ms, as 2^n x 125 us */
                unsigned n = 3;
                while (n < 10 && (125u << n) < 1000u * ival) n++;
                h->interval = (unsigned char)n;
            }
            if (h->dci > maxdci) maxdci = h->dci;
            kind = 0;
        }
    }
    if (d->hub && (d->nhid != 1 || d->hid[0].kind != K_HUB)) d->nhid = 0;   /* a hub's own endpoint only */
    if (!d->hub && !d->nhid) {
        put_s(&u->l, "usb: xHCI: ");
        xh_where(&u->l, d);
        put_s(&u->l, ": not a keyboard, mouse or hub (class ");
        put_hex(&u->l, cls);
        put_s(&u->l, "), left alone");
        say(u);
        return;                           /* its slot stays: the port is taken */
    }
    /* Its endpoints to the controller, then the configuration to the device. */
    unsigned add = 1;
    for (int i = 0; i < d->nhid; i++) add |= 1u << d->hid[i].dci;
    xh_ctl_ctx(x, slot - 1, add);
    xh_slot_ctx(x, d, maxdci);
    for (int i = 0; i < d->nhid; i++)
        xh_ep_ctx(x, d, d->hid[i].dci, 7, d->hid[i].len, d->hid[i].interval, d->ring0 + 1u + (unsigned)i);
    cc = xh_cmd(u, x, xh_input(d), T_CONFIGURE << 10 | slot << 24);
    if (cc != CC_SUCCESS || xh_control(u, x, d, 0x00, 9, config, 0, 0) < 0) {
        put_s(&u->l, "usb: xHCI: ");
        xh_where(&u->l, d);
        put_s(&u->l, ": not configured (completion code ");
        put_dec(&u->l, cc);
        put_s(&u->l, ")");
        say(u);
        d->nhid = 0;
        return;
    }
    if (d->hub) {
        /* The hub's descriptor: its ports and think time, to the controller (Evaluate Context:
           the slot is a hub), then each port powered and looked at. */
        if (xh_control(u, x, d, 0xA0, 6, 0x29 << 8, 0, 9) < 7) { d->nhid = 0; return; }
        unsigned ports = b[2] > 15 ? 15 : b[2], chars = b[3] | b[4] << 8, power = b[5] * 2u;
        d->nports = (unsigned char)ports;
        d->ttt = speed == SP_HIGH ? (unsigned char)(chars >> 5 & 3) : 0;
        xh_ctl_ctx(x, slot - 1, 1);
        xh_slot_ctx(x, d, maxdci);
        cc = xh_cmd(u, x, xh_input(d), T_EVALUATE << 10 | slot << 24);
        put_s(&u->l, "usb: xHCI: hub on ");
        xh_where(&u->l, d);
        put_s(&u->l, ", ");
        put_dec(&u->l, ports);
        put_s(&u->l, cc == CC_SUCCESS ? " ports" : " ports, but the controller did not take it as a hub");
        say(u);
        for (unsigned p = 1; p <= ports; p++) xh_control(u, x, d, 0x23, 3, 8, p, 0);   /* PORT_POWER */
        sleep_ms((power < 20 ? 20 : power) + 100);
        for (unsigned p = 1; p <= ports && x->on; p++) xh_hub_port(u, x, d, p);
        xh_sync(u, x, XH_RPT(u), 4096);
        if (d->nhid && x->on) xh_arm(u, x, d, 0);
        return;
    }
    for (int i = 0; i < d->nhid; i++) {
        struct xhid *h = &d->hid[i];
        xh_control(u, x, d, 0x21, 0x0B, 0, h->iface, 0);          /* SET_PROTOCOL: boot */
        if (h->kind == K_KEYBOARD) xh_control(u, x, d, 0x21, 0x0A, 0, h->iface, 0);   /* SET_IDLE */
        if (h->kind == K_KEYBOARD) x->keyboards++;
        else x->mice++;
        xh_say(u, d, xh_kind(h->kind));
    }
    xh_sync(u, x, XH_RPT(u), 4096);
    for (int i = 0; i < d->nhid && x->on; i++) xh_arm(u, x, d, i);
}

/* Port `p` of `hub` changed, or is looked at for the first time. */
COLD static void xh_hub_port(struct usb *u, struct xhci *x, struct xdev *hub, unsigned p) {
    unsigned char *b = XH_CTL(u);
    if (xh_control(u, x, hub, 0xA3, 0, 0, p, 4) < 4) return;              /* GET_STATUS */
    unsigned st = b[0] | b[1] << 8, change = b[2] | b[3] << 8;
    for (unsigned k = 0; k < 5; k++)                                      /* C_PORT_CONNECTION to C_PORT_RESET */
        if (change >> k & 1) xh_control(u, x, hub, 0x23, 1, 16 + k, p, 0);
    struct xdev *child = xh_child(x, hub->slot, 0, p);
    if (child && (!(st & 1) || (change & 1))) {
        xh_remove(u, x, child);
        child = 0;
    }
    if (!(st & 1) || child) return;
    xh_control(u, x, hub, 0x23, 3, 4, p, 0);                              /* PORT_RESET */
    int ok = 0;
    for (int i = 0; i < 50 && !ok && x->on; i++) {
        sleep_ms(10);
        if (xh_control(u, x, hub, 0xA3, 0, 0, p, 4) == 4) {
            st = b[0] | b[1] << 8;
            ok = !(st & 0x10) && (st & 2);
        }
    }
    xh_control(u, x, hub, 0x23, 1, 20, p, 0);                             /* C_PORT_RESET */
    if (!ok) return;
    sleep_ms(10);
    xh_enumerate(u, x, hub, hub->root, p, st & 0x200 ? SP_LOW : st & 0x400 ? SP_HIGH : SP_FULL);
}

/* Root port `p` changed, or is looked at for the first time. */
COLD static void xh_root_port(struct usb *u, struct xhci *x, unsigned p) {
    unsigned sc = xr(x, PORTSC(p));
    if (sc == 0xffffffffu) return;
    xw(x, PORTSC(p), (sc & PORT_KEEP) | (sc & PORT_CHANGES));            /* the changes, seen */
    struct xdev *d = xh_child(x, 0, p, 0);
    if (d && (!(sc & PORT_CCS) || (sc & PORT_CSC))) {
        xh_remove(u, x, d);
        d = 0;
    }
    if (!(sc & PORT_CCS) || d) return;
    if (!(sc & PORT_PED)) {               /* a USB 2 port: reset it (a USB 3 port enables itself) */
        xw(x, PORTSC(p), (sc & PORT_KEEP) | PORT_PR);
        for (int i = 0; i < 50; i++) {
            sleep_ms(10);
            sc = xr(x, PORTSC(p));
            if ((sc & PORT_PRC) || !(sc & PORT_PR)) break;
        }
        xw(x, PORTSC(p), (sc & PORT_KEEP) | (sc & PORT_CHANGES));
        sleep_ms(10);
    }
    unsigned speed = sc >> 10 & 15;
    put_s(&u->l, "usb: xHCI: port ");
    put_dec(&u->l, p);
    if (!(sc & PORT_PED) || speed < 1 || speed > 4) {
        put_s(&u->l, ": a device the port did not enable (PORTSC ");
        put_hex(&u->l, sc);
        put_s(&u->l, ")");
        say(u);
        return;
    }
    put_s(&u->l, speed == 4 ? ": a USB 3 device, not a keyboard or mouse; left alone"
                 : speed == SP_LOW ? ": a low-speed device" : speed == SP_FULL ? ": a full-speed device"
                 : ": a high-speed device");
    say(u);
    if (speed != 4) xh_enumerate(u, x, 0, p, 0, speed);
}

/* ---- usb.c's hooks ---- */

static int xhci_on(struct usb *u) { return XH(u)->on; }

/* Called after the DWC2 is up: what the kernel must refuse, tried for real; then the
   controller, if the machine layer brought it up, running, and what is plugged in. */
COLD static void xhci_start(struct usb *u) {
    struct xhci *x = XH(u);
    memset(x, 0, sizeof *x);
    u64 display = 0x04000000UL + 256UL * 4096;          /* the display server's code */
    int refused = sys(SYS_XHCI, USB, 3, display, 8 | (u64)(T_NORMAL << 10) << 32, 256).status == BAD_ARG &&
                  sys(SYS_XHCI, USB, 1, 0, 0, XR_OP(0x30)).status == BAD_ARG &&
                  sys(SYS_XHCI, USB, 1, 1, 0, USBCMD).status == BAD_ARG &&
                  sys(SYS_XHCI, USB, 3, XH_RINGS, (u64)(T_LINK << 10) << 32, 5).status == BAD_ARG;
    put_s(&u->l, refused ? "usb: xHCI: refused, as proved: a TRB aimed at the display's memory, DCBAAP, Run/Stop, a Link out of its ring"
                         : "usb: xHCI: the kernel let a dangerous request through");
    say(u);
    u64 v = 0;
    if (sys(SYS_XHCI, USB, 0, 0, 0, 0).status != OK || sys2(SYS_MAP, XH_CAP, XH_PAGE).status != OK) {
        put_s(&u->l, "usb: xHCI: no controller (the USB-A ports are off)");
        say(u);
        return;
    }
    unsigned hcs1 = xr(x, 0x04);
    x->ports = (int)(hcs1 >> 24) > 5 ? 5 : (int)(hcs1 >> 24);   /* the kernel lets it touch five */
    unsigned slots = (hcs1 & 0xff) < XH_SLOTS ? (hcs1 & 0xff) : XH_SLOTS;
    /* The machine layer reset it before this driver started: it is halted and ready. */
    for (int i = 0; i < 100 && (xr(x, USBSTS) & STS_CNR); i++) sleep_ms(10);
    unsigned sts = xr(x, USBSTS);
    if ((sts & STS_CNR) || !(sts & STS_HCH)) {
        put_s(&u->l, "usb: xHCI: the controller is not halted and ready (USBSTS ");
        put_hex(&u->l, sts);
        put_s(&u->l, ")");
        say(u);
        return;
    }
    xw(x, CONFIG, slots);                                 /* MaxSlotsEn */
    /* Interrupter 0 and the controller's interrupt enabled, as Linux and Circle run the
       VL805: nothing reaches the processor (the machine layer keeps its PCI interrupt and MSI
       off), and this driver polls; ERDP's Event Handler Busy is cleared as events are taken. */
    xw(x, XR_RT(0x20), 2);                                /* IMAN.IE */
    xw(x, USBCMD, 4);                                     /* INTE */
    x->cmd_cycle = x->ev_cycle = 1;
    for (int r = 0; r < 3 * XH_SLOTS; r++) x->ring[r].cycle = 1;
    xh_sys(x, 2, 0, 0, 0, &v);                            /* run */
    for (int i = 0; i < 20 && (xr(x, USBSTS) & STS_HCH); i++) sleep_ms(1);
    sts = xr(x, USBSTS);
    x->on = !(sts & (STS_HCH | STS_HSE));
    unsigned cc = xh_cmd(u, x, 0, T_NOOP_CMD << 10);
    put_s(&u->l, "usb: xHCI: ");
    if (!x->on || cc != CC_SUCCESS) {
        x->on = 0;
        put_s(&u->l, "the controller did not start (USBSTS ");
        put_hex(&u->l, sts);
        put_s(&u->l, ")");
        say(u);
        return;
    }
    put_s(&u->l, "running, ");
    put_dec(&u->l, (u64)x->ports);
    put_s(&u->l, " ports, ");
    put_dec(&u->l, slots);
    put_s(&u->l, " device slots, DMA checked by the kernel");
    say(u);
    for (int p = 1; p <= x->ports; p++) {
        unsigned sc = xr(x, PORTSC(p));
        if (!(sc & PORT_PP)) xw(x, PORTSC(p), (sc & PORT_KEEP) | PORT_PP);
    }
    sleep_ms(120);                        /* power good, and a connection settled */
    x->busy = 1;
    for (int p = 1; p <= x->ports && x->on; p++) xh_root_port(u, x, (unsigned)p);
    x->busy = 0;
    x->root_pending = 0;
    x->next_scan = millis() + 1000;
    put_s(&u->l, "usb: xHCI: ready, ");
    put_dec(&u->l, (u64)x->keyboards);
    put_s(&u->l, x->keyboards == 1 ? " keyboard, " : " keyboards, ");
    put_dec(&u->l, (u64)x->mice);
    put_s(&u->l, x->mice == 1 ? " mouse" : " mice");
    say(u);
}

/* From usb.c's loop, every few milliseconds: reports, and whatever changed. */
static void xhci_poll(struct usb *u) {
    struct xhci *x = XH(u);
    if (!x->on || x->busy) return;
    x->busy = 1;
    xh_events(u, x);
    if (x->recover) {                     /* an interrupt endpoint halted: reset it, ask again */
        x->recover = 0;
        for (int i = 0; i < XH_SLOTS && x->on; i++)
            for (int k = 0; k < x->dev[i].nhid; k++) {
                struct xdev *d = &x->dev[i];
                struct xhid *h = &d->hid[k];
                if (!h->failed) continue;
                h->failed = 0;
                if (++h->errors <= 8 && xh_restart(u, x, d, h->dci, d->ring0 + 1u + (unsigned)k)) xh_arm(u, x, d, k);
            }
    }
    for (int i = 0; i < XH_SLOTS && x->on; i++) {
        struct xdev *d = &x->dev[i];
        unsigned bits = d->pending;
        d->pending = 0;
        for (unsigned p = 1; d->slot && d->hub && p <= d->nports && x->on; p++)
            if (bits >> p & 1) xh_hub_port(u, x, d, p);
    }
    /* Root ports: those that said they changed, and every second each one, in case. */
    unsigned bits = x->root_pending;
    x->root_pending = 0;
    if (millis() >= x->next_scan) {
        x->next_scan = millis() + 1000;
        for (int p = 1; p <= x->ports; p++)
            if (xr(x, PORTSC(p)) & PORT_CHANGES) bits |= 1u << p;
    }
    for (int p = 1; p <= x->ports && x->on; p++)
        if (bits >> p & 1) xh_root_port(u, x, (unsigned)p);
    x->busy = 0;
}
