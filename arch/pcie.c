/*
 * The BCM2711's PCIe bridge, and the one device behind it on a Pi 4: the VL805 xHCI controller
 * (bus 1, device 0, function 0), the four USB-A ports. Brought up once at boot, with the MMU
 * still off, following Linux's drivers/pci/controller/pcie-brcmstb.c for the BCM2711 (as the
 * Circle bare-metal library ports it): the bridge reset and its PERST# line, the link, an
 * outbound window for the VL805's registers, an inbound window that maps bus address x to
 * physical address x for the first 4 GiB (the Lean kernel's addresses are physical, and the
 * frame pool is in the first GiB), no MSI and no legacy interrupt (the driver polls). Then the
 * firmware loads the VL805's own firmware (mailbox tag 0x00030058), and the VL805 gets its
 * registers at the start of the outbound window, with memory decoding on and bus mastering
 * still off: arch/xhci.c turns that on only after the xHCI memory is stored and the controller
 * reset.
 *
 * PCIe configuration space stays here: no task can reach it (an MSI address would be a DMA
 * write too). The VL805's registers are mapped for the kernel only, as device memory, at
 * their physical address (arch/kmain.c, `pcie_window`), and reached only through arch/xhci.c.
 *
 * Also the functions arch/xhci.c reaches the hardware through (arch/xhci.h).
 */
#include "arch.h"
#include "xhci.h"

#define PCIE_BASE 0xFD500000UL         /* the bridge's registers (Linux: pcie@7d500000) */
#define PCIE_BUSADDR 0xF8000000UL      /* ... as the PCIe bus sees it */
#define PCIE_WINDOW 0x4000000UL        /* 64 MiB (the Pi firmware's device tree) */
#define INBOUND 0x100000000UL          /* bus 0 to 4 GiB = physical 0 to 4 GiB */

/* Bridge registers (the names are Broadcom's, as Linux has them). */
#define RC_CFG_VENDOR_SPECIFIC_REG1 0x0188
#define RC_CFG_PRIV1_ID_VAL3 0x043c
#define MISC_MISC_CTRL 0x4008
#define MISC_CPU_2_PCIE_MEM_WIN0_LO 0x400c
#define MISC_CPU_2_PCIE_MEM_WIN0_HI 0x4010
#define MISC_RC_BAR1_CONFIG_LO 0x402c
#define MISC_RC_BAR2_CONFIG_LO 0x4034
#define MISC_RC_BAR2_CONFIG_HI 0x4038
#define MISC_RC_BAR3_CONFIG_LO 0x403c
#define MISC_PCIE_STATUS 0x4068
#define MISC_REVISION 0x406c
#define MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT 0x4070
#define MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI 0x4080
#define MISC_CPU_2_PCIE_MEM_WIN0_LIMIT_HI 0x4084
#define MISC_HARD_PCIE_HARD_DEBUG 0x4204
#define INTR2_CPU_BASE 0x4300
#define EXT_CFG_DATA 0x8000
#define EXT_CFG_INDEX 0x9000
#define RGR1_SW_INIT_1 0x9210
#define CAP_REGS 0x00ac                /* the bridge's PCI Express capability */

static uint32_t rd(uint64_t off) { return mmio_r32(PCIE_BASE + off); }
static void wr(uint64_t off, uint32_t v) { mmio_w32(PCIE_BASE + off, v); }
static uint16_t rd16(uint64_t a) { return *(volatile uint16_t *)a; }
static void wr16(uint64_t a, uint16_t v) { *(volatile uint16_t *)a = v; }
static uint8_t rd8(uint64_t a) { return *(volatile uint8_t *)a; }

/* Set a field of a bridge register, then read it back (the write has landed). */
static void field(uint64_t off, uint32_t mask, int shift, uint32_t v) {
    wr(off, (rd(off) & ~mask) | ((v << shift) & mask));
    (void)rd(off);
}

/* The VL805's configuration space: bus 1, device 0, function 0, through the index register. */
static uint64_t vl805_cfg(void) {
    wr(EXT_CFG_INDEX, 1u << 20);
    return PCIE_BASE + EXT_CFG_DATA;
}

static void say(const char *s) { kputs("leanos: PCIe: "); kputs(s); }

/* Bring the bridge and the VL805 up: 1 if the VL805's registers are now at PCIE_CPU, with
   their size in *bar, its vendor and device in *id and its revision in *rev. Else it says why
   and the USB-A ports stay off. */
int pcie_start(uint64_t *bar, uint32_t *id, uint32_t *rev) {
    uint32_t v = rd(MISC_REVISION) & 0xffff;
    if (v == 0 || v == 0xffff) {
        say("no bridge answers at 0xfd500000; the USB-A ports are off\n");
        return 0;
    }
    /* Reset the bridge, with the fundamental reset (PERST#) held, then out of reset; the
       SerDes powered. */
    field(RGR1_SW_INIT_1, 0x2, 1, 1);
    field(RGR1_SW_INIT_1, 0x1, 0, 1);
    delay_us(200);
    field(RGR1_SW_INIT_1, 0x2, 1, 0);
    field(MISC_HARD_PCIE_HARD_DEBUG, 0x08000000, 27, 0);
    delay_us(200);
    uint32_t bridge_rev = rd(MISC_REVISION) & 0xffff;
    /* SCB access, configuration reads of absent devices as errors (all ones), 128-byte
       bursts. */
    uint32_t t = rd(MISC_MISC_CTRL);
    t = (t & ~0x1000u) | 0x1000u;
    t = (t & ~0x2000u) | 0x2000u;
    t &= ~0x300000u;
    wr(MISC_MISC_CTRL, t);
    /* Inbound (RC_BAR2): bus 0 to 4 GiB is physical 0 to 4 GiB; the size code is log2 - 15. */
    wr(MISC_RC_BAR2_CONFIG_LO, 32 - 15);
    wr(MISC_RC_BAR2_CONFIG_HI, 0);
    field(MISC_MISC_CTRL, 0xf8000000u, 27, 32 - 15);   /* SCB0: 4 GiB */
    field(MISC_RC_BAR1_CONFIG_LO, 0x1f, 0, 0);         /* no PCIe to GISB window */
    field(MISC_RC_BAR3_CONFIG_LO, 0x1f, 0, 0);         /* no PCIe to SCB window */
    /* The bridge's interrupts: cleared and masked (nothing here takes them). */
    wr(INTR2_CPU_BASE + 0x8, 0xffffffff);
    (void)rd(INTR2_CPU_BASE + 0x8);
    wr(INTR2_CPU_BASE + 0x10, 0xffffffff);
    (void)rd(INTR2_CPU_BASE + 0x10);
    /* Gen 2 at most (link capability and link control 2). */
    wr(CAP_REGS + 0x0c, (rd(CAP_REGS + 0x0c) & ~0xfu) | 2);
    wr16(PCIE_BASE + CAP_REGS + 0x30, (uint16_t)((rd16(PCIE_BASE + CAP_REGS + 0x30) & ~0xfu) | 2));
    /* Let the VL805 out of reset, give it 100 ms (the PCIe CEM specification), then wait up
       to half a second more for the link. */
    field(RGR1_SW_INIT_1, 0x1, 0, 0);
    delay_us(100000);
    uint64_t until = deadline_us(500000);
    while ((rd(MISC_PCIE_STATUS) & 0x30) != 0x30 && !passed(until)) delay_us(1000);
    uint32_t status = rd(MISC_PCIE_STATUS);
    if ((status & 0x30) != 0x30) {
        say("no link (status ");
        kputhex(status);
        kputs("); the USB-A ports are off\n");
        return 0;
    }
    if (!(status & 0x80)) {
        say("the bridge is in endpoint mode; the USB-A ports are off\n");
        return 0;
    }
    /* Outbound window 0: CPU PCIE_CPU.. is bus PCIE_BUSADDR.., 64 MiB, in MiB units. */
    uint64_t base_mb = PCIE_CPU >> 20, limit_mb = (PCIE_CPU + PCIE_WINDOW - 1) >> 20;
    wr(MISC_CPU_2_PCIE_MEM_WIN0_LO, (uint32_t)PCIE_BUSADDR);
    wr(MISC_CPU_2_PCIE_MEM_WIN0_HI, (uint32_t)(PCIE_BUSADDR >> 32));
    field(MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT, 0xfff0, 4, (uint32_t)base_mb);
    field(MISC_CPU_2_PCIE_MEM_WIN0_BASE_LIMIT, 0xfff00000u, 20, (uint32_t)limit_mb);
    field(MISC_CPU_2_PCIE_MEM_WIN0_BASE_HI, 0xff, 0, (uint32_t)(base_mb >> 12));
    field(MISC_CPU_2_PCIE_MEM_WIN0_LIMIT_HI, 0xff, 0, (uint32_t)(limit_mb >> 12));
    /* The bridge shows the class of a PCI-to-PCI bridge; little-endian inbound data; the
       reference clock gated by CLKREQ#. */
    field(RC_CFG_PRIV1_ID_VAL3, 0xffffff, 0, 0x060400);
    field(RC_CFG_VENDOR_SPECIFIC_REG1, 0xc, 2, 0);
    field(MISC_HARD_PCIE_HARD_DEBUG, 0x2, 1, 1);
    uint16_t lnksta = rd16(PCIE_BASE + CAP_REGS + 0x12);
    uint32_t speed = lnksta & 0xf, width = (lnksta >> 4) & 0x3f;
    say(speed == 1 ? "link up, 2.5 GT/s x" : speed == 2 ? "link up, 5.0 GT/s x" : "link up, ? GT/s x");
    kputdec(width);
    kputs(" (bridge revision ");
    kputhex(bridge_rev);
    kputs(")\n");

    /* The bridge itself (bus 0): secondary and subordinate bus 1, a memory window of 1 MiB at
       the start of the outbound window, CRS visibility, memory decoding and forwarding on. */
    if (rd(0x08) >> 8 != 0x060400 || (rd8(PCIE_BASE + 0x0e) & 0x7f) != 1) {
        say("the bridge does not say it is a PCI-to-PCI bridge; the USB-A ports are off\n");
        return 0;
    }
    mmio_w8(PCIE_BASE + 0x0c, 64 / 4);
    mmio_w8(PCIE_BASE + 0x19, 1);
    mmio_w8(PCIE_BASE + 0x1a, 1);
    wr16(PCIE_BASE + 0x20, (uint16_t)(PCIE_BUSADDR >> 16));
    wr16(PCIE_BASE + 0x22, (uint16_t)(PCIE_BUSADDR >> 16));
    mmio_w8(PCIE_BASE + 0x3e, 0x01);
    mmio_w8(PCIE_BASE + CAP_REGS + 0x1c, 0x10);
    wr16(PCIE_BASE + 0x04, 0x0002 | 0x0004 | 0x0040 | 0x0100);

    /* The VL805's firmware: on a board with no EEPROM for it, the VideoCore firmware loads
       it after the reset (Linux: drivers/reset/reset-raspberrypi.c). Its address is
       bus << 20 | device << 15 | function << 12. */
    const uint32_t addr = 0x100000;
    uint32_t o[1] = {0};
    if (mbox_tag(0x00030058, &addr, 1, o, 1)) say("the firmware loaded the VL805's firmware (tag 0x30058)\n");
    else say("the firmware did not answer tag 0x30058 (a VL805 with an EEPROM loads its own)\n");
    delay_us(10000);

    uint64_t cfg = vl805_cfg();
    uint32_t ids = mmio_r32(cfg + 0x00), class_rev = mmio_r32(cfg + 0x08);
    if (ids == 0xffffffff || ids == 0) {
        say("no device on bus 1; the USB-A ports are off\n");
        return 0;
    }
    if (class_rev >> 8 != 0x0c0330 || (rd8(cfg + 0x0e) & 0x7f) != 0) {
        say("the device on bus 1 is not an xHCI controller (class ");
        kputhex(class_rev >> 8);
        kputs("); the USB-A ports are off\n");
        return 0;
    }
    /* Its BAR 0 (64-bit memory): sized, then placed at the start of the window. */
    wr16(cfg + 0x04, 0);                                   /* decoding off while it moves */
    mmio_w32(cfg + 0x10, 0xffffffff);
    mmio_w32(cfg + 0x14, 0xffffffff);
    uint32_t lo = mmio_r32(cfg + 0x10), hi = mmio_r32(cfg + 0x14);
    uint64_t size = (uint64_t)(~(lo & ~0xfu)) + 1;
    if ((lo & 0x7) != 0x4 || hi != 0xffffffff || size > 0x100000 || size < 0x1000) {
        say("the VL805's registers are not a 64-bit BAR of 4 KiB to 1 MiB; the USB-A ports are off\n");
        return 0;
    }
    mmio_w32(cfg + 0x10, (uint32_t)PCIE_BUSADDR);
    mmio_w32(cfg + 0x14, (uint32_t)(PCIE_BUSADDR >> 32));
    mmio_w8(cfg + 0x0c, 64 / 4);
    /* No MSI or MSI-X: off after the reset, and kept off (an MSI is a DMA write). */
    if (rd16(cfg + 0x06) & 0x10) {
        uint32_t at = rd8(cfg + 0x34) & 0xfc;
        for (int k = 0; at && k < 48; k++) {
            uint32_t cap = rd8(cfg + at);
            if (cap == 0x05) wr16(cfg + at + 2, rd16(cfg + at + 2) & ~1u);
            if (cap == 0x11) wr16(cfg + at + 2, rd16(cfg + at + 2) & ~0x8000u);
            at = rd8(cfg + at + 1) & 0xfc;
        }
    }
    /* Memory decoding on, parity and SERR reporting, legacy interrupts off; bus mastering
       stays off until arch/xhci.c has stored its memory and reset it. */
    wr16(cfg + 0x04, 0x0002 | 0x0040 | 0x0100 | 0x0400);
    *bar = size;
    *id = ids;
    *rev = class_rev & 0xff;
    return 1;
}

/* ---- what arch/xhci.c reaches the hardware through ---- */

uint32_t xhci_mmio_r32(uint64_t off) { return mmio_r32(PCIE_CPU + off); }
void xhci_mmio_w32(uint64_t off, uint32_t v) { mmio_w32(PCIE_CPU + off, v); }
volatile uint32_t *xhci_phys32(uint64_t pa) { return (volatile uint32_t *)pa; }   /* identity-mapped */

void xhci_clean(uint64_t pa, uint64_t len) {
    for (uint64_t a = pa & ~63UL; a < pa + len; a += 64) __asm__ volatile("dc cvac, %0" :: "r"(a) : "memory");
    DSB(sy);
}

void xhci_flush(uint64_t pa, uint64_t len) {
    for (uint64_t a = pa & ~63UL; a < pa + len; a += 64) __asm__ volatile("dc civac, %0" :: "r"(a) : "memory");
    DSB(sy);
}

void xhci_barrier(void) { DSB(sy); }

void xhci_bus_master(int on) {
    uint64_t cfg = vl805_cfg();
    uint16_t cmd = rd16(cfg + 0x04);
    wr16(cfg + 0x04, (uint16_t)(on ? cmd | 0x0004 : cmd & ~0x0004u));
    (void)rd16(cfg + 0x04);
}

void xhci_udelay(uint64_t us) { delay_us(us); }
