/*
 * The machine layer's side of the xHCI controller: the VL805 behind the BCM2711's PCIe bridge,
 * the Pi 4's four USB-A ports. The Lean kernel decides every request (`sysXhci` in
 * LeanOS/Kernel.lean); this file only carries out what it approved, and what ROADMAP.md (stage
 * 7, USB part 2) makes this layer's duty:
 *
 *   - at boot, keep the controller off unless its registers are laid out the way the kernel's
 *     checks assume (`xhci_probe`): 4 KiB pages, at least the 5 ports the driver may touch, at
 *     most the 12 scratchpad pages the xHCI memory has, and the windows the kernel lets the
 *     driver write (operational, runtime, doorbells) inside the registers, apart from each
 *     other, from the capability registers and from every extended capability;
 *   - before the USB driver runs, store the xHCI memory's boot content (`xhciBoot`), placing
 *     the input contexts for the controller's context size, clean it to memory, reset the
 *     controller, and only then turn its bus mastering on (`xhci_after_load`);
 *   - for each approved request, the register, the TRB in its three guarded steps, the input
 *     context's 16 bytes, or the cache maintenance (`xhci_request`).
 *
 * It reaches the hardware only through the functions arch/xhci.h lists, so test/xhci-sim/
 * compiles this same file for the host, against a model of the controller.
 */
#include "xhci.h"

/* The controller as `xhci_probe` found it. */
static int present;               /* the layout is one the kernel's checks were written for */
static int on;                    /* its memory is stored and it came out of reset: requests go through */
static uint32_t caplen, rtsoff, dboff;
static int csz;                   /* HCCPARAMS1.CSZ: contexts of 64 bytes (1) or 32 (0) */
static uint64_t xbase;            /* the xHCI memory, physical */

#define PAGE 4096u
#define OP(o) (caplen + (o))
#define USBCMD 0x00
#define USBSTS 0x04
#define PAGESIZE 0x08
#define CRCR 0x18
#define DCBAAP 0x30
#define RT_ERSTSZ 0x28
#define RT_ERSTBA 0x30
#define RT_ERDP 0x38
#define STS_HCH 1u
#define STS_CNR (1u << 11)

/* What the kernel lets the driver reach (LeanOS/Kernel.lean: `xReadable`, `xWriteOk`), in
   bytes from the start of each space: the five ports' registers after the operational ones,
   interrupter 0 after MFINDEX, and doorbells 0 to 16. */
#define OP_WINDOW (0x400u + 16u * 5u)
#define RT_WINDOW 0x40u
#define DB_WINDOW (4u * 17u)
#define READ_WINDOW 0x1000u
#define MAX_SCRATCH 12u
#define MIN_PORTS 5u

int xhci_present(void) { return present; }

static void refuse(const char *why) {
    kputs("leanos: xHCI: refused: ");
    kputs(why);
    kputs("; the USB-A ports are off\n");
    present = 0;
}

static int overlap(uint64_t a, uint64_t alen, uint64_t b, uint64_t blen) {
    return a < b + blen && b < a + alen;
}

/* The three windows the driver may write. */
static int hits_window(uint64_t at, uint64_t len) {
    return overlap(at, len, caplen, OP_WINDOW) || overlap(at, len, rtsoff, RT_WINDOW) ||
           overlap(at, len, dboff, DB_WINDOW);
}

int xhci_probe(uint64_t bar, uint32_t id, uint32_t rev) {
    present = on = 0;
    uint32_t cap0 = xhci_mmio_r32(0);
    caplen = cap0 & 0xff;
    uint32_t version = cap0 >> 16;
    uint32_t hcs1 = xhci_mmio_r32(0x04), hcs2 = xhci_mmio_r32(0x08), hcc1 = xhci_mmio_r32(0x10);
    dboff = xhci_mmio_r32(0x14) & ~3u;
    rtsoff = xhci_mmio_r32(0x18) & ~0x1fu;
    uint32_t slots = hcs1 & 0xff, intrs = (hcs1 >> 8) & 0x7ff, ports = hcs1 >> 24;
    uint32_t scratch = ((hcs2 >> 21) & 0x1f) << 5 | ((hcs2 >> 27) & 0x1f);
    csz = (hcc1 >> 2) & 1;
    kputs("leanos: xHCI: ");
    kputs(id == 0x34831106u ? "VL805" : "controller");
    kputs(" rev ");
    kputhex(rev);
    kputs(" (");
    kputhex(id & 0xffff);
    kputs(":");
    kputhex(id >> 16);
    kputs("), xHCI ");
    kputhex(version);
    kputs(", ");
    kputdec(ports);
    kputs(" ports, ");
    kputdec(slots);
    kputs(" slots, ");
    kputdec(scratch);
    kputs(csz ? " scratchpad pages, 64-byte contexts\n" : " scratchpad pages, 32-byte contexts\n");
    kputs("leanos: xHCI: registers: ");
    kputdec(bar);
    kputs(" bytes; operational at ");
    kputhex(caplen);
    kputs(", runtime at ");
    kputhex(rtsoff);
    kputs(", doorbells at ");
    kputhex(dboff);
    kputs("\n");

    if (cap0 == 0xffffffffu || version == 0) { refuse("its registers do not answer"); return 0; }
    if (bar < READ_WINDOW || (bar & (bar - 1))) { refuse("its registers are smaller than 4 KiB"); return 0; }
    if (caplen < 0x20) { refuse("CAPLENGTH is shorter than the capability registers"); return 0; }
    if (caplen + OP_WINDOW > bar || rtsoff + RT_WINDOW > bar || dboff + DB_WINDOW > bar) {
        refuse("a register window lies past the end of its registers");
        return 0;
    }
    if (overlap(caplen, OP_WINDOW, rtsoff, RT_WINDOW) || overlap(caplen, OP_WINDOW, dboff, DB_WINDOW) ||
        overlap(rtsoff, RT_WINDOW, dboff, DB_WINDOW) || hits_window(0, caplen)) {
        refuse("its operational, runtime and doorbell registers overlap");
        return 0;
    }
    if (!(xhci_mmio_r32(OP(PAGESIZE)) & 1)) { refuse("it does not take 4 KiB pages"); return 0; }
    if (ports < MIN_PORTS) { refuse("it has fewer than 5 ports"); return 0; }
    if (scratch > MAX_SCRATCH) { refuse("it wants more than 12 scratchpad pages"); return 0; }
    if (slots == 0 || intrs == 0) { refuse("it has no device slots or no interrupter"); return 0; }
    /* The extended capabilities (the debug capability has DMA addresses of its own): each
       must lie in the registers and apart from every window the driver may write. A
       capability's extent: what the specification (7.1 to 7.8) gives its kind; one of a
       kind it does not size, up to the next capability (at most 1 KiB), or 16 bytes if it
       is the last. */
    uint32_t at = (hcc1 >> 16) * 4, n = 0;
    while (at) {
        if (at + 16 > bar || (at & 3) || ++n > 64) { refuse("its extended capabilities run past its registers"); return 0; }
        uint32_t head = xhci_mmio_r32(at), next = ((head >> 8) & 0xff) * 4, kind = head & 0xff;
        uint32_t len = kind == 1 || kind == 3 ? 8 : kind == 2 ? 16 + 4 * (xhci_mmio_r32(at + 8) >> 28)
                     : kind == 10 ? 0x40 : next ? (next < 1024 ? next : 1024) : 16;
        if (at + len > bar) { refuse("an extended capability runs past its registers"); return 0; }
        if (hits_window(at, len)) { refuse("an extended capability overlaps a register window"); return 0; }
        if (kind == 2) {
            uint32_t ports_word = xhci_mmio_r32(at + 8), first = ports_word & 0xff, count = (ports_word >> 8) & 0xff;
            kputs("leanos: xHCI: USB ");
            kputdec(head >> 24);
            kputs(count == 1 ? " port " : " ports ");
            kputdec(first);
            if (count > 1) { kputs(" to "); kputdec(first + count - 1); }
            kputs("\n");
        }
        at = next ? at + next : 0;
    }
    present = 1;
    return 1;
}

/* Wait up to `ms` milliseconds for the operational register `reg` to have `mask` equal to
   `want`: 1 if it did. */
static int wait_op(uint32_t reg, uint32_t mask, uint32_t want, uint32_t ms) {
    for (uint32_t i = 0; i < ms * 10; i++) {
        if ((xhci_mmio_r32(OP(reg)) & mask) == want) return 1;
        xhci_udelay(100);
    }
    return (xhci_mmio_r32(OP(reg)) & mask) == want;
}

void xhci_before_load(void) {
    if (!present) return;
    on = 0;
    uint32_t cmd = xhci_mmio_r32(OP(USBCMD));
    if (cmd & 1) {
        xhci_mmio_w32(OP(USBCMD), cmd & ~1u);
        wait_op(USBSTS, STS_HCH, STS_HCH, 20);       /* a halt takes at most 16 ms (xHCI 5.4.1) */
    }
    xhci_bus_master(0);
}

int xhci_after_load(uint64_t base) {
    if (!present) return 0;
    xbase = base;
    /* Word i at byte 8i; in the input contexts (pages 32 to 47), a word at byte 64c + 16u + 8w
       of its page goes to 32c + 16u + 8w when contexts are 32 bytes, and past a context's
       first 32 bytes there is nothing (the boot content has only zeros there). */
    for (uint64_t i = 0; i < 64 * 512; i++) {
        uint64_t w = xhci_boot_word(i), page = i / 512, at = base + 8 * i;
        if (page >= 32 && page < 48 && !csz) {
            uint64_t b = (i % 512) * 8, c = b / 64, r = b % 64;
            if (r >= 32) {
                if (w) kpanic("xHCI boot content past a 32-byte context");
                continue;
            }
            at = base + page * PAGE + 32 * c + r;
        }
        volatile uint32_t *p = xhci_phys32(at);
        p[0] = (uint32_t)w;
        p[1] = (uint32_t)(w >> 32);
    }
    xhci_clean(base, 64 * PAGE);
    /* Reset: it must be halted first (it is: it never ran, or xhci_before_load stopped it). */
    if (!wait_op(USBSTS, STS_HCH, STS_HCH, 20)) {
        kputs("leanos: xHCI: refused: the controller did not halt; the USB-A ports are off\n");
        return 0;
    }
    xhci_mmio_w32(OP(USBCMD), 2);                        /* HCRST */
    xhci_udelay(1000);
    if (!wait_op(USBCMD, 2, 0, 1000) || !wait_op(USBSTS, STS_CNR, 0, 1000)) {
        kputs("leanos: xHCI: refused: the controller did not come out of its reset; the USB-A ports are off\n");
        return 0;
    }
    xhci_bus_master(1);
    on = 1;
    kputs("leanos: xHCI: its memory stored at ");
    kputhex(base);
    kputs(", the controller reset, bus mastering on\n");
    return 1;
}

static void w64(uint64_t off, uint64_t v) {      /* low word, then high */
    xhci_mmio_w32(off, (uint32_t)v);
    xhci_mmio_w32(off + 4, (uint32_t)(v >> 32));
}

/* Register `reg` (`xSpace`, `xOff`): the capability registers, the operational ones (from
   CAPLENGTH), the runtime ones (from RTSOFF), the doorbells (from DBOFF). */
static uint64_t reg_at(uint64_t reg) {
    uint64_t space = reg >> 16, off = reg & 0xffff;
    if (space > 3) kpanic("an xHCI register the kernel should never have passed");
    return (space == 0 ? 0 : space == 1 ? caplen : space == 2 ? rtsoff : dboff) + off;
}

int xhci_request(uint64_t op, uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint32_t *v) {
    if (!on) return 0;
    if (op == 1) {                                        /* read */
        *v = xhci_mmio_r32(reg_at(a));
    } else if (op == 2) {                                 /* write; CRCR and ERDP take 64 bits */
        uint64_t at = reg_at(a);
        if (a == (0x10000 | CRCR) || a == (0x20000 | RT_ERDP)) w64(at, b);
        else xhci_mmio_w32(at, (uint32_t)b);
    } else if (op == 3) {                                 /* run: the DMA bases, then Run/Stop */
        w64(OP(DCBAAP), a);
        w64(OP(CRCR), b);
        xhci_mmio_w32(rtsoff + RT_ERSTSZ, 1);
        w64(rtsoff + RT_ERSTBA, c);
        w64(rtsoff + RT_ERDP, d);
        xhci_mmio_w32(OP(USBCMD), xhci_mmio_r32(OP(USBCMD)) | 1);
    } else if (op == 4) {
        /* A TRB, in three steps, each made visible before the next: the guard's control word
           (a No-Op with the other cycle bit), the parameter and status, the control word. So
           the controller reads the old TRB, a No-Op, or the new one (`xhci_guard_safe`). */
        volatile uint32_t *p = xhci_phys32(a);
        p[3] = (uint32_t)(d >> 32);
        xhci_barrier();
        xhci_clean(a, 16);
        p[0] = (uint32_t)b;
        p[1] = (uint32_t)(b >> 32);
        p[2] = (uint32_t)c;
        xhci_barrier();
        xhci_clean(a, 16);
        p[3] = (uint32_t)d;
        xhci_barrier();
        xhci_clean(a, 16);
    } else if (op == 5) {
        /* 16 bytes of an input context: `a` is its page plus 64c + 16u; the controller's
           contexts are 64 or 32 bytes (the kernel allows only u = 0 and 1, which both have). */
        uint64_t page = a & ~(uint64_t)(PAGE - 1), in = a & (PAGE - 1);
        uint64_t at = page + in / 64 * (csz ? 64 : 32) + in % 64;
        volatile uint32_t *p = xhci_phys32(at);
        p[0] = (uint32_t)b;
        p[1] = (uint32_t)(b >> 32);
        p[2] = (uint32_t)c;
        p[3] = (uint32_t)(c >> 32);
        xhci_barrier();
        xhci_clean(at, 16);
    } else if (op == 6) {
        /* The driver's range, and what only the controller writes: the event ring (page 2)
           and the device contexts (pages 16 to 31), so the driver reads what it wrote. */
        xhci_flush(a, b);
        xhci_flush(xbase + 2 * PAGE, PAGE);
        xhci_flush(xbase + 16 * PAGE, 16 * PAGE);
    } else {
        kpanic("an xHCI request the kernel should never have made");
    }
    return 1;
}
