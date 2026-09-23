/*
 * The machine layer: boots the board, owns the hardware, and carries out what the Lean
 * kernel decides. It makes no access decisions of its own. The only state it keeps
 * beyond hardware is each task's saved registers.
 *
 * Trusted, not proved (see TRUST.md). The rule for this file: if a check here would ever
 * change an outcome, the check belongs in LeanOS/Kernel.lean instead. The checks it does
 * make (frame and page bounds when writing page tables) are there only to stop the
 * machine if this layer and the Lean kernel ever disagree.
 */
#include <lean/lean.h>
#include "arch.h"

/* ---- the Lean kernel (LeanOS/Kernel.lean) ---- */
lean_object *initialize_leanos_LeanOS_Kernel(uint8_t builtin);
lean_object *leanos_init(lean_object *fb_base);
lean_object *leanos_syscall(lean_object *s, lean_object *num, lean_object *a0, lean_object *a1,
                            lean_object *a2, lean_object *a3, lean_object *a4);
lean_object *leanos_tick(lean_object *s);
lean_object *leanos_fault(lean_object *s);
lean_object *leanos_clear_result(lean_object *s, lean_object *j);
lean_object *leanos_verify(lean_object *s, lean_object *i, lean_object *w0, lean_object *w1, lean_object *w2,
                           lean_object *w3, lean_object *w4, lean_object *w5, lean_object *w6, lean_object *w7);
lean_object *leanos_cur(lean_object *s);
uint8_t leanos_ready(lean_object *s, lean_object *i);
uint8_t leanos_dead(lean_object *s, lean_object *i);
lean_object *leanos_ntasks(lean_object *s);
lean_object *leanos_result_len(lean_object *s, lean_object *j);
lean_object *leanos_result(lean_object *s, lean_object *j, lean_object *k);
lean_object *leanos_kernel_l1(lean_object *k);
lean_object *leanos_l1(lean_object *l2, lean_object *k);
lean_object *leanos_l2(lean_object *l3, lean_object *k);
lean_object *leanos_l3(lean_object *s, lean_object *i, lean_object *k);
lean_object *leanos_reply_out_va(lean_object *r);
lean_object *leanos_reply_out_len(lean_object *r);
uint8_t leanos_reply_remap(lean_object *r);
lean_object *leanos_reply_load(lean_object *r);
lean_object *leanos_reply_io(lean_object *r);
lean_object *leanos_reply_load_len(lean_object *r);
lean_object *leanos_reply_power(lean_object *r);
uint8_t leanos_open_slot(lean_object *i);
lean_object *leanos_reply_io_block(lean_object *r);
lean_object *leanos_io_failed(lean_object *s);
int sd_init(void);
uint64_t sd_partition(void);
int sd_part_read(uint64_t block, void *dst);
int sd_part_write(uint64_t block, const void *src);
uint8_t leanos_autostart(lean_object *i);
lean_object *leanos_reply_state(lean_object *r);
lean_object *leanos_reply_unmask(lean_object *r);
lean_object *leanos_irq(lean_object *s, lean_object *n);
lean_object *leanos_irq_line_count(lean_object *unused);
lean_object *leanos_irq_line(lean_object *k);
lean_object *leanos_fb_width(lean_object *unused);
lean_object *leanos_fb_height(lean_object *unused);
lean_object *leanos_fb_pages(lean_object *unused);

uint64_t rt_heap_live(void);
uint64_t rt_heap_peak(void);

/* The kernel state. This layer holds one reference to it; exported Lean functions consume
   their arguments, so a query passes a fresh reference (`K1`) and an update hands the
   state over and takes the new one back. */
static lean_object *K;
#define K1 (lean_inc(K), K)

/* Lean returns numbers as boxed scalars. Every number the kernel returns is small; a
   big one would mean the runtime and the kernel disagree, so stop. */
static uint64_t nat(lean_object *o) {
    if (!lean_is_scalar(o)) kpanic("kernel returned a number outside the small range");
    return lean_unbox(o);
}

/* A user register becomes a Lean Nat, which this runtime keeps as a small number: below
   2^63, with no big numbers behind it (rt/runtime.c stops the machine on one). So what a
   task passes must not only fit, but keep fitting through whatever the kernel computes
   from it, or one system call with a huge argument would stop the machine.

   Message words (send and call: x1-x3; reply: x1-x3) are data the kernel only carries,
   never computes with: they keep their low 63 bits. Every other argument is an index, an
   address, a count, a length, a time or a set of rights, and none is valid at 2^40 or
   more; those clamp to 2^40, which every call refuses (a 2^40 ms sleep is 34 years), and
   which keeps every sum and product the kernel makes from arguments far below 2^63.
   test/fuzz.sh throws such arguments at every call. */
#define ARG_MAX (1ULL << 40)
static lean_object *arg(uint64_t v) { return lean_box(v < ARG_MAX ? v : ARG_MAX); }
static lean_object *msg_word(uint64_t v) { return lean_box(v & ~(1ULL << 63)); }
static int carries_words(uint64_t num) { return num == 8 || num == 10 || num == 11; }

static uint64_t cur_task(void) { return nat(leanos_cur(K1)); }
static int ready(uint64_t i) { return leanos_ready(K1, lean_box(i)); }

/* ---- console ---- */

/* PL011 at 115200 8N1. The Pi 4 feeds the UART a 48 MHz clock: 48e6 / (16 * 115200)
   = 26.0417, so the divisor is 26 + 3/64. */
/* Route the PL011 to the header's pins 8 and 10 (GPIO 14 TXD, 15 RXD): function ALT0, no
   pull on TX, a pull-up on RX so an unconnected line reads idle. On a Pi 4 the firmware
   gives the PL011 to Bluetooth otherwise; doing it here needs no device-tree overlay. */
#define GPIO_BASE (PERIPHERAL_BASE + 0x200000)
static void uart_pins(void) {
    uint32_t sel = mmio_r32(GPIO_BASE + 0x04);                 /* GPFSEL1: pins 10-19 */
    sel &= ~((7u << 12) | (7u << 15));
    sel |= (4u << 12) | (4u << 15);                            /* ALT0 for 14 and 15 */
    mmio_w32(GPIO_BASE + 0x04, sel);
    uint32_t pull = mmio_r32(GPIO_BASE + 0xe4);                /* pulls, pins 0-15 */
    pull &= ~((3u << 28) | (3u << 30));
    pull |= 1u << 30;                                          /* 15: pull-up */
    mmio_w32(GPIO_BASE + 0xe4, pull);
}

static void uart_init(void) {
    uart_pins();
    mmio_w32(UART0 + 0x30, 0);          /* CR: off while configuring */
    mmio_w32(UART0 + 0x44, 0x7ff);      /* ICR: clear pending interrupts */
    mmio_w32(UART0 + 0x24, 26);         /* IBRD */
    mmio_w32(UART0 + 0x28, 3);          /* FBRD */
    mmio_w32(UART0 + 0x2c, 0x70);       /* LCRH: 8 bits, FIFOs on */
    mmio_w32(UART0 + 0x30, 0x301);      /* CR: UART, transmit, receive on */
}

void kputc(char c) {
    while (mmio_r32(UART0 + 0x18) & (1 << 5)) {}
    mmio_w8(UART0, (uint8_t)c);
}
void kputs(const char *s) {
    while (*s) {
        if (*s == '\n') kputc('\r');
        kputc(*s++);
    }
}
void kputhex(uint64_t v) {
    kputs("0x");
    int started = 0;
    for (int i = 60; i >= 0; i -= 4) {
        int d = (v >> i) & 15;
        if (d || started || i == 0) { kputc("0123456789abcdef"[d]); started = 1; }
    }
}
void kputdec(uint64_t v) {
    char b[21];
    int i = 20;
    b[i] = 0;
    do { b[--i] = '0' + v % 10; v /= 10; } while (v);
    kputs(b + i);
}

void poweroff(void) {
#ifdef LEANOS_QEMU
    /* Semihosting SYS_EXIT, so a test run under QEMU ends with a status. */
    static const uint64_t block[2] = {0x20026 /* ADP_Stopped_ApplicationExit */, 0};
    register uint64_t x0 __asm__("x0") = 0x18;
    register const uint64_t *x1 __asm__("x1") = block;
    __asm__ volatile("hlt #0xf000" :: "r"(x0), "r"(x1) : "memory");
#endif
    /* A Pi has no power switch the kernel can reach; stop here. */
    for (;;) __asm__ volatile("wfi");
}

/* Restart the whole machine through the power-management block's watchdog: a full reset
   in a few ticks. The same on a Pi 4 and on QEMU's model of it. */
#define PM_BASE (PERIPHERAL_BASE + 0x100000)
#define PM_RSTC (PM_BASE + 0x1c)
#define PM_WDOG (PM_BASE + 0x24)
#define PM_PASSWORD 0x5a000000u
static void restart(void) {
    mmio_w32(PM_WDOG, PM_PASSWORD | 10);
    mmio_w32(PM_RSTC, PM_PASSWORD | (mmio_r32(PM_RSTC) & ~0x30u) | 0x20u);
    for (;;) __asm__ volatile("wfi");
}

/* ---- the panic screen ----
 * A Pi on a desk has a monitor, not a serial cable: when the kernel stops, it says why on
 * the screen too, in the same 5x7 font the programs use, drawn straight into the
 * framebuffer. Nothing else runs by then, so nothing else is drawing. */
#include "font.h"

static uint32_t *panic_fb;

static void panic_text(uint32_t w, uint32_t x, uint32_t y, uint32_t scale, const char *t, uint32_t c) {
    for (; *t; t++, x += 6 * scale) {
        unsigned ch = (unsigned char)*t;
        if (ch < 32 || ch > 126) ch = '?';
        if (x + 6 * scale > w - 40) { x = 40; y += 10 * scale; }
        const unsigned char *g = font5x7[ch - 32];
        for (uint32_t r = 0; r < 7 * scale; r++)
            for (uint32_t k = 0; k < 5 * scale; k++)
                if (g[r / scale] & (16 >> (k / scale))) panic_fb[(y + r) * w + x + k] = c;
    }
}

static void panic_screen(const char *msg) {
    if (!panic_fb) return;
    const uint32_t w = (uint32_t)nat(leanos_fb_width(lean_box(0)));
    const uint32_t h = (uint32_t)nat(leanos_fb_height(lean_box(0)));
    for (uint32_t i = 0; i < w * h; i++) panic_fb[i] = 0x1a1c26;
    for (uint32_t i = 0; i < w * 6; i++) panic_fb[i] = 0xe0483e;
    panic_text(w, 40, 60, 4, "leanos stopped", 0xffffff);
    panic_text(w, 40, 120, 2, msg, 0xffb4a8);
    panic_text(w, 40, 160, 2, "The kernel met something it cannot safely go on from,", 0xc8cad4);
    panic_text(w, 40, 184, 2, "and stopped rather than guess. It wrote nothing after this.", 0xc8cad4);
    panic_text(w, 40, 208, 2, "Switch the Pi off and on to start again.", 0xc8cad4);
    /* The framebuffer is cached memory: push the picture out to where the GPU reads it. */
    for (uint64_t a = (uint64_t)panic_fb; a < (uint64_t)(panic_fb + w * h); a += 64)
        __asm__ volatile("dc cvac, %0" :: "r"(a) : "memory");
    __asm__ volatile("dsb sy" ::: "memory");
}

void kpanic(const char *msg) {
    kputs("\nleanos: PANIC: ");
    kputs(msg);
    kputs("\n");
    panic_screen(msg);
    poweroff();
}

/* ---- framebuffer ----
 * Asked of the VideoCore firmware through the mailbox, once, at boot, before anything
 * else runs. The mailbox is a DMA path (the firmware writes wherever the request says), so
 * it never leaves this layer: user space only ever sees the resulting pages, as frame
 * capabilities the Lean kernel hands out. The request is fixed: `fbWidth` x `fbHeight`,
 * 32 bits per pixel, from LeanOS/Kernel.lean. */

#define MBOX (PERIPHERAL_BASE + 0xB880)

static volatile uint32_t mbox_buf[36] __attribute__((aligned(16)));

static uint64_t fb_alloc(void) {
    const uint32_t FB_W = (uint32_t)nat(leanos_fb_width(lean_box(0)));
    const uint32_t FB_H = (uint32_t)nat(leanos_fb_height(lean_box(0)));
    const uint64_t FB_PAGES = nat(leanos_fb_pages(lean_box(0)));
    int i = 0;
    mbox_buf[i++] = 0;                  /* size, set below */
    mbox_buf[i++] = 0;                  /* request */
    mbox_buf[i++] = 0x48003; mbox_buf[i++] = 8; mbox_buf[i++] = 0;  /* physical size */
    mbox_buf[i++] = FB_W; mbox_buf[i++] = FB_H;
    mbox_buf[i++] = 0x48004; mbox_buf[i++] = 8; mbox_buf[i++] = 0;  /* virtual size */
    mbox_buf[i++] = FB_W; mbox_buf[i++] = FB_H;
    mbox_buf[i++] = 0x48005; mbox_buf[i++] = 4; mbox_buf[i++] = 0;  /* depth */
    mbox_buf[i++] = 32;
    mbox_buf[i++] = 0x48006; mbox_buf[i++] = 4; mbox_buf[i++] = 0;  /* pixel order: BGR, */
    mbox_buf[i++] = 0;                                              /* so 0x00RRGGBB words */
    mbox_buf[i++] = 0x40001; mbox_buf[i++] = 8; mbox_buf[i++] = 0;  /* allocate */
    mbox_buf[i++] = 4096; mbox_buf[i++] = 0;
    mbox_buf[i++] = 0x40008; mbox_buf[i++] = 4; mbox_buf[i++] = 0;  /* pitch */
    mbox_buf[i++] = 0;
    mbox_buf[i++] = 0;                  /* end tag */
    mbox_buf[0] = i * 4;

    uint32_t msg = (uint32_t)(uint64_t)mbox_buf | 8; /* channel 8: properties */
    while (mmio_r32(MBOX + 0x38) & 0x80000000) {}    /* write mailbox full */
    mmio_w32(MBOX + 0x20, msg);
    for (;;) {
        while (mmio_r32(MBOX + 0x18) & 0x40000000) {} /* read mailbox empty */
        if (mmio_r32(MBOX) == msg) break;
    }
    uint64_t base = mbox_buf[23] & 0x3FFFFFFF;       /* bus address to physical */
    if (mbox_buf[1] != 0x80000000 || mbox_buf[5] != FB_W || mbox_buf[6] != FB_H ||
        mbox_buf[15] != 32 || mbox_buf[24] < FB_PAGES * PAGE_SIZE || mbox_buf[28] != FB_W * 4 ||
        base == 0 || (base & (PAGE_SIZE - 1)))
        return 0;
    return base;
}

/* ---- memory management unit ----
 * The Lean kernel computes every translation-table word (`l1Word`, `l2Word`, `l3Word` in
 * LeanOS/Kernel.lean); this layer only stores them. LeanOS/Tables.lean proves that, stored
 * this way, the tables give user mode exactly the task's mappings (`walk_eq_view`),
 * assuming the MMU is configured as LeanOS/Arm.lean describes, which `mmu_init` does:
 * 4 KiB granule, 39-bit addresses (T0SZ = 25), TTBR0 only (EPD1 = 1), WXN off.
 * Every task has its own tables and address-space number (ASID = task + 1). Kernel
 * addresses are identity-mapped, so a table's address here is its physical address. */

static uint64_t kl1[512] __attribute__((aligned(4096)));
static uint64_t tl1[MAX_TASKS][512] __attribute__((aligned(4096)));
static uint64_t tl2[MAX_TASKS][512] __attribute__((aligned(4096)));
static uint64_t tl3[MAX_TASKS][USER_PAGES] __attribute__((aligned(4096))); /* 16 tables each */

static uint64_t word(lean_object *w) {
    if (!lean_is_scalar(w)) kpanic("table word outside the small range");
    return lean_unbox(w);
}

static void tlb_flush_all(void) {
    DSB(ishst);
    __asm__ volatile("tlbi vmalle1is" ::: "memory");
    DSB(ish);
    ISB();
}

static void mmu_init(void) {
    for (uint64_t k = 0; k < 512; k++) kl1[k] = word(leanos_kernel_l1(lean_box(k)));

    /* Memory attribute 0: device nGnRE. 1: normal, write-back. 2: normal, not cached. */
    SYSREG_WRITE(mair_el1, (0x04UL << 0) | (0xffUL << 8) | (0x44UL << 16));
    uint64_t tcr = 25                /* T0SZ: 39-bit addresses */
                 | (1UL << 8)        /* inner write-back walks */
                 | (1UL << 10)       /* outer write-back walks */
                 | (3UL << 12)       /* inner shareable */
                 | (0UL << 14)       /* 4 KiB granule */
                 | (1UL << 23)       /* EPD1: no TTBR1 walks, the kernel lives in the low half */
                 | (1UL << 32);      /* 36-bit physical addresses */
    SYSREG_WRITE(tcr_el1, tcr);
    SYSREG_WRITE(ttbr0_el1, (uint64_t)kl1);
    ISB();
    tlb_flush_all();
    uint64_t sctlr = SYSREG_READ(sctlr_el1);
    sctlr &= ~(1UL << 19);                    /* WXN off, as the model assumes */
    sctlr |= (1 << 0) | (1 << 2) | (1 << 12); /* MMU, data cache, instruction cache */
    SYSREG_WRITE(sctlr_el1, sctlr);
    ISB();
}

/* Task i's level-1 and level-2 tables never change. Set once at boot. */
static void tables_init(uint64_t i) {
    uint64_t l2 = (uint64_t)tl2[i], l3 = (uint64_t)tl3[i];
    for (uint64_t k = 0; k < 512; k++) {
        tl1[i][k] = word(leanos_l1(lean_box(l2), lean_box(k)));
        tl2[i][k] = word(leanos_l2(lean_box(l3), lean_box(k)));
    }
}

/* Rewrite task i's level-3 tables from the Lean state. Only level 3 changes, so the
   kernel's own entries stay valid even when i is the task whose address space is live. */
static void build_user_pages(uint64_t i) {
    for (uint64_t k = 0; k < USER_PAGES; k++) tl3[i][k] = word(leanos_l3(K1, lean_box(i), lean_box(k)));
    tlb_flush_all();
}

static void switch_to(uint64_t i) {
    SYSREG_WRITE(ttbr0_el1, (uint64_t)tl1[i] | ((i + 1) << 48));
    ISB();
}

/* ---- interrupts and the timer ---- */

static uint64_t timer_interval;

static void timer_rearm(void) {
    SYSREG_WRITE(cntp_tval_el0, timer_interval);
    SYSREG_WRITE(cntp_ctl_el0, 1);
}

static void gic_enable(uint32_t id) { mmio_w32(GICD + 0x100 + 4 * (id / 32), 1u << (id % 32)); }
static void gic_disable(uint32_t id) { mmio_w32(GICD + 0x180 + 4 * (id / 32), 1u << (id % 32)); }

static void irq_init(void) {
    mmio_w32(GICD + 0x000, 1);                          /* distributor on */
    mmio_w8(GICD + 0x400 + TIMER_IRQ, 0x80);            /* priority */
    gic_enable(TIMER_IRQ);
    /* The lines the manifest hands to tasks as interrupt capabilities. */
    uint64_t lines = nat(leanos_irq_line_count(lean_box(0)));
    for (uint64_t k = 0; k < lines; k++) {
        uint32_t id = (uint32_t)nat(leanos_irq_line(lean_box(k)));
        if (id < 32 || id >= 1020) kpanic("interrupt line out of range");
        mmio_w8(GICD + 0x400 + id, 0x80);               /* priority */
        mmio_w8(GICD + 0x800 + id, 1);                  /* deliver to core 0 */
        gic_enable(id);
    }
    mmio_w32(GICC + 0x004, 0xff);                       /* accept every priority */
    mmio_w32(GICC + 0x000, 1);                          /* CPU interface on */
    uint64_t freq = SYSREG_READ(cntfrq_el0);
    if (freq == 0) freq = 54000000;                     /* the Pi 4's crystal, if firmware left it unset */
    timer_interval = freq / 100;                        /* 10 ms time slice */
    timer_rearm();
}

/* ---- tasks ---- */

static struct frame saved[MAX_TASKS];
static uint64_t code_len[MAX_TASKS], asset_len[MAX_TASKS];
static int started[MAX_TASKS];      /* loaded at least once */
static uint64_t ntasks;
static uint64_t syscalls, ticks, device_irqs;

/* Take one interrupt from the controller. The timer ends a time slice; any other line is
   masked until its holder acknowledges it, and the Lean kernel decides who to wake. */
static void handle_irq(void) {
    uint32_t iar = mmio_r32(GICC + 0x00c);
    uint32_t id = iar & 0x3ff;
    if (id == TIMER_IRQ) {
        ticks++;
        timer_rearm();
        K = leanos_tick(K);
    } else if (id < 1020) {
        device_irqs++;
        gic_disable(id);
        K = leanos_irq(K, lean_box(id));
    }
    if (id < 1020) mmio_w32(GICC + 0x010, iar);
}

extern const uint64_t user_progs[], user_prog_ends[];
extern const uint64_t user_assets[], user_asset_ends[];
extern const uint64_t open_assets[], open_assets_end[];   /* the fonts for the open slots */

static void sync_icache(uint64_t start, uint64_t len) {
    for (uint64_t a = start & ~63UL; a < start + len; a += 64)
        __asm__ volatile("dc cvau, %0" :: "r"(a) : "memory");
    DSB(ish);
    __asm__ volatile("ic iallu" ::: "memory");
    DSB(ish);
    ISB();
}

/* Load an open slot with the `len` bytes at `va` in the current task's memory (the task
   that started it): the Lean kernel checked every page of them is mapped readable there,
   in the address space as rebuilt after the start. Frames cleared first, as for any start. */
static void load_image(uint64_t i, uint64_t va, uint64_t len) {
    uint64_t base = FRAME_BASE + FRAMES_PER_TASK * i * PAGE_SIZE;
    memset((void *)base, 0, FRAMES_PER_TASK * PAGE_SIZE);
    if (len > CODE_PAGES * PAGE_SIZE) kpanic("program image larger than the code run");
    memcpy((void *)base, (const void *)va, len);
    sync_icache(base, len);
    code_len[i] = len;
    /* the shared fonts, at the start of the spare run, where built-in programs find theirs */
    uint64_t alen = open_assets_end[0] - open_assets[0];
    if (alen > SPARE_PAGES * PAGE_SIZE) kpanic("the open slots' assets are larger than the spare run");
    memcpy((void *)(base + SPARE_FIRST * PAGE_SIZE), (const void *)open_assets[0], alen);
    asset_len[i] = alen;
    memset(&saved[i], 0, sizeof saved[i]);
    saved[i].elr = USER_BASE;
    saved[i].sp = USER_BASE + USER_PAGES * PAGE_SIZE;
    saved[i].spsr = 0;
    started[i] = 1;
}

/* Load slot i's program into its frames, fresh: every frame cleared (nothing of a previous
   run survives), the code, the assets, and registers that start at the program's entry. */
static void load_program(uint64_t i) {
    uint64_t base = FRAME_BASE + FRAMES_PER_TASK * i * PAGE_SIZE; /* frame 256i, as `frameCaps` says */
    memset((void *)base, 0, FRAMES_PER_TASK * PAGE_SIZE);
    uint64_t len = user_prog_ends[i] - user_progs[i];
    code_len[i] = len;
    if (len > CODE_PAGES * PAGE_SIZE) kpanic("user program larger than its code run");
    memcpy((void *)base, (const void *)user_progs[i], len);
    sync_icache(base, len);
    /* The task's assets (fonts, icons, pictures), if any, at the start of its spare run,
       where `frameCaps` in LeanOS/Kernel.lean puts capability 3. */
    uint64_t alen = user_asset_ends[i] - user_assets[i];
    asset_len[i] = alen;
    if (alen > SPARE_PAGES * PAGE_SIZE) kpanic("assets larger than the spare run");
    memcpy((void *)(base + SPARE_FIRST * PAGE_SIZE), (const void *)user_assets[i], alen);
    memset(&saved[i], 0, sizeof saved[i]);
    saved[i].elr = USER_BASE;
    saved[i].sp = USER_BASE + USER_PAGES * PAGE_SIZE;
    saved[i].spsr = 0; /* EL0, interrupts on */
    started[i] = 1;
}

static const char *const names[] = {"alice", "display", "mallory", "carol", "input",
                                    "terminal", "settings", "security", "fs", "files",
                                    "slot 10", "slot 11", "slot 12", "slot 13", "slot 14", "slot 15",
                                    "apps"};
#define NPROGS 17   /* the kernel image's program table: slots 0-16 (empty for the open slots) */

/* SHA-256 of "abc", from FIPS 180-4: the hash must be right before anything relies on it. */
static void sha256_self_test(void) {
    static const uint32_t want[8] = {0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
                                     0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad};
    struct sha256 h;
    uint32_t got[8];
    sha256_init(&h);
    sha256_update(&h, "abc", 3);
    sha256_final(&h, got);
    for (int i = 0; i < 8; i++)
        if (got[i] != want[i]) kpanic("SHA-256 self-test failed");
}

/* Measure exactly what task i was loaded with, its code then its assets, where they now sit
   in its own frames, and let the Lean kernel decide whether it may run. */
static void measure_and_verify(uint64_t i) {
    struct sha256 h;
    uint32_t d[8];
    sha256_init(&h);
    sha256_update(&h, (const void *)(FRAME_BASE + FRAMES_PER_TASK * i * PAGE_SIZE), code_len[i]);
    sha256_update(&h, (const void *)(FRAME_BASE + (FRAMES_PER_TASK * i + SPARE_FIRST) * PAGE_SIZE), asset_len[i]);
    sha256_final(&h, d);
    K = leanos_verify(K, lean_box(i), lean_box(d[0]), lean_box(d[1]), lean_box(d[2]), lean_box(d[3]),
                      lean_box(d[4]), lean_box(d[5]), lean_box(d[6]), lean_box(d[7]));
    kputs("leanos: ");
    kputs(names[i]);
    if (ready(i) && leanos_open_slot(lean_box(i))) {
        kputs(" runs a program from its starter, not the manifest; sha256 ");
        kputhex(d[0]);
        kputs("...\n");
    } else if (ready(i)) {
        kputs(" verified, sha256 ");
        kputhex(d[0]);
        kputs("...\n");
    } else {
        kputs(" refused: what was loaded does not match the boot manifest\n");
    }
}

static void do_syscall(uint64_t cur) {
    struct frame *f = &saved[cur];
    syscalls++;
    lean_object *(*w)(uint64_t) = carries_words(f->x[8]) ? msg_word : arg;
    lean_object *r = leanos_syscall(K, arg(f->x[8]), arg(f->x[0]), w(f->x[1]), w(f->x[2]),
                                    w(f->x[3]), arg(f->x[4]));
    uint64_t out_va = nat(leanos_reply_out_va((lean_inc(r), r)));
    uint64_t out_len = nat(leanos_reply_out_len((lean_inc(r), r)));
    int remap = leanos_reply_remap((lean_inc(r), r));
    uint64_t unmask = nat(leanos_reply_unmask((lean_inc(r), r)));
    uint64_t load = nat(leanos_reply_load((lean_inc(r), r)));
    uint64_t load_len = nat(leanos_reply_load_len((lean_inc(r), r)));
    uint64_t power = nat(leanos_reply_power((lean_inc(r), r)));
    uint64_t io = nat(leanos_reply_io((lean_inc(r), r)));
    uint64_t io_block = nat(leanos_reply_io_block((lean_inc(r), r)));
    K = leanos_reply_state(r);
    if (unmask) gic_enable((uint32_t)(unmask - 1));

    /* Still in `cur`'s address space, so the range the kernel checked is readable here. */
    for (uint64_t k = 0; k < out_len; k++) {
        char c = ((volatile const char *)out_va)[k];
        if (c == '\n') kputc('\r');
        kputc(c);
    }
    /* Block I/O, still in `cur`'s address space: the kernel checked the 512 bytes at out_va
       are in a page `cur` has mapped writable (read) or readable (write). */
    if (io) {
        int ok = io == 1 ? sd_part_read(io_block, (void *)out_va) : sd_part_write(io_block, (const void *)out_va);
        if (!ok) K = leanos_io_failed(K);
    }
    /* The display server asked (only it can: `only_display_powers`). Every file is already
       on the card: the file server writes each change through before it answers. */
    if (power == 1) {
        kputs("leanos: switching off, as the display server asked\n");
        poweroff();
    } else if (power == 2) {
        kputs("leanos: restarting, as the display server asked\n");
        restart();
    }
    if (load) {
        /* `start`: the Lean kernel has already taken back every capability and mapping that
           reached the slot's frames. Rebuild every task's tables from that state before the
           frames are cleared and loaded, then measure what was loaded. */
        uint64_t k = load - 1;
        if (k >= ntasks || k == cur) kpanic("start of a slot the kernel should have refused");
        for (uint64_t i = 0; i < ntasks; i++) build_user_pages(i);
        if (load_len) load_image(k, out_va, load_len);
        else if (k < NPROGS && !leanos_open_slot(lean_box(k))) load_program(k);
        else kpanic("start of an open slot without a program");
        kputs("leanos: ");
        kputs(names[k]);
        kputs(" started\n");
        measure_and_verify(k);
        build_user_pages(k);
    } else if (remap) build_user_pages(cur);
}

/* Load the result registers the Lean kernel left for task j (the outcome of its last
   system call, or a message it was waiting for), then tell the kernel they are loaded. */
static void load_result(uint64_t j) {
    uint64_t n = nat(leanos_result_len(K1, lean_box(j)));
    if (n == 0) return;
    if (n > 31) kpanic("too many result registers");
    for (uint64_t k = 0; k < n; k++) saved[j].x[k] = nat(leanos_result(K1, lean_box(j), lean_box(k)));
    K = leanos_clear_result(K, lean_box(j));
}

/* ---- the kernel stack ----
 * The Lean kernel recurses once per list element (a task's mappings, at most USER_PAGES of
 * them), so the stack is sized for that (arch/kernel.ld). Nothing proves the bound, so it is
 * checked instead: the stack is painted at boot, and every return to user mode checks that
 * the bottom of the paint is intact. Running past it stops the machine rather than letting
 * the stack grow into the kernel's other data. */
extern char __stack_bottom[], __stack_top[];
#define STACK_PAINT 0x5a5a5a5a5a5a5a5aUL
#define STACK_GUARD 512   /* bytes at the bottom that must stay painted */

static void stack_paint(void) {
    uint64_t sp;
    __asm__ volatile("mov %0, sp" : "=r"(sp));
    for (uint64_t *p = (uint64_t *)__stack_bottom; (uint64_t)p < sp - 256; p++) *p = STACK_PAINT;
}

static void stack_check(void) {
    for (uint64_t *p = (uint64_t *)__stack_bottom; (char *)p < __stack_bottom + STACK_GUARD; p++)
        if (*p != STACK_PAINT) kpanic("kernel stack overflow");
}

static uint64_t stack_peak(void) {
    uint64_t *p = (uint64_t *)__stack_bottom;
    while ((char *)p < __stack_top && *p == STACK_PAINT) p++;
    return (uint64_t)(__stack_top - (char *)p);
}

static void report(const char *what) {
    kputs(what);
    kputs(" (");
    kputdec(syscalls);
    kputs(" system calls, ");
    kputdec(ticks);
    kputs(" timer ticks, ");
    kputdec(device_irqs);
    kputs(" device interrupts, kernel heap ");
    kputdec(rt_heap_live());
    kputs(" bytes live, ");
    kputdec(rt_heap_peak());
    kputs(" peak, stack ");
    kputdec(stack_peak());
    kputs(" bytes peak)\n");
}

/* No task is ready. If every task has stopped, power off. Otherwise wait for an interrupt:
   the timer, or a device whose holder is waiting for it. WFI wakes on a pending interrupt
   even though the kernel runs with interrupts masked. */
static uint64_t idle_until_ready(void) {
    static int reported;
    uint64_t next = cur_task();
    while (!ready(next)) {
        uint64_t waiting = 0;
        for (uint64_t i = 0; i < ntasks; i++)
            if (started[i] && !leanos_dead(K1, lean_box(i))) waiting++;
        if (waiting == 0) {
            report("leanos: every task has finished");
            poweroff();
        }
        if (!reported) {
            reported = 1;
            kputs("leanos: idle, ");
            kputdec(waiting);
            report(waiting == 1 ? " task waiting" : " tasks waiting");
        }
        __asm__ volatile("wfi");
        handle_irq();
        next = cur_task();
    }
    return next;
}

static const char *fault_name(uint64_t ec) {
    switch (ec) {
    case 0x07: return "floating point use";
    case 0x20: return "instruction fetch not allowed";
    case 0x24: return "data access not allowed";
    case 0x22: return "misaligned program counter";
    case 0x26: return "misaligned stack pointer";
    case 0x0e: return "illegal execution state";
    case 0x00: return "undefined instruction";
    default: return "exception";
    }
}

void trap(struct frame *f, uint64_t kind) {
    uint64_t cur = cur_task();
    if (kind >= 2) {
        kputs("\nleanos: exception in the kernel, kind ");
        kputdec(kind);
        kputs(" esr ");
        kputhex(SYSREG_READ(esr_el1));
        kputs(" elr ");
        kputhex(SYSREG_READ(elr_el1));
        kputs(" far ");
        kputhex(SYSREG_READ(far_el1));
        kpanic("stopping");
    }
    saved[cur] = *f;

    if (kind == 0) {
        uint64_t esr = SYSREG_READ(esr_el1), ec = esr >> 26;
        if (ec == 0x15) {
            do_syscall(cur);
        } else {
            kputs("leanos: ");
            kputs(cur < ntasks ? names[cur] : "task");
            kputs(" stopped: ");
            kputs(fault_name(ec));
            kputs(" at ");
            kputhex(ec == 0x20 || ec == 0x24 ? SYSREG_READ(far_el1) : f->elr);
            kputs("\n");
            K = leanos_fault(K);
        }
    } else {
        handle_irq();
    }

    uint64_t next = idle_until_ready();
    load_result(next);
    switch_to(next);
    *f = saved[next];
    stack_check();
}

void kmain(void) {
    stack_paint();
    uart_init();
    kputs("leanos \xc2\xa9 2026 Keith Adler\n");
    kputs("leanos: Raspberry Pi 4, booting on ");
    uint64_t el = SYSREG_READ(CurrentEL) >> 2;
    kputs(el == 1 ? "EL1" : "EL?");
    kputs("\n");
    /* User mode may read the virtual counter (and its frequency) to keep time: animations
       need it, and a task could already time itself by counting loops. */
    SYSREG_WRITE(cntkctl_el1, 1UL << 1);

    /* The Lean kernel comes up first: it says what screen to ask for, and computes the
       tables the MMU is turned on with. */
    lean_object *res = initialize_leanos_LeanOS_Kernel(1);
    if (!lean_io_result_is_ok(res)) kpanic("Lean module initialization failed");
    lean_dec(res);

    uint64_t fb = fb_alloc();
    panic_fb = (uint32_t *)fb;
    if (fb) {
        kputs("leanos: framebuffer ");
        kputdec(nat(leanos_fb_width(lean_box(0))));
        kputs("x");
        kputdec(nat(leanos_fb_height(lean_box(0))));
        kputs(" at ");
        kputhex(fb);
        kputs("\n");
    } else kputs("leanos: no framebuffer\n");

    mmu_init();
    kputs("leanos: MMU on\n");
    if (!sd_init()) kputs("leanos: no SD card\n");
    else {
        uint64_t blocks = sd_partition();
        if (blocks) {
            kputs("leanos: SD card ready, data partition of ");
            kputdec(blocks / 2048);
            kputs(" MiB\n");
        } else kputs("leanos: SD card has no data partition (type 0xDA); files stay in memory\n");
    }

    K = leanos_init(lean_box(fb));
    ntasks = nat(leanos_ntasks(K1));
    if (ntasks > MAX_TASKS || ntasks > sizeof names / sizeof names[0]) kpanic("the manifest has more tasks than the machine layer supports");
    kputs("leanos: Lean kernel initialized, ");
    kputdec(ntasks);
    kputs(" tasks\n");

    memset((void *)FRAME_BASE, 0, NFRAMES * PAGE_SIZE);
    sha256_self_test();
    /* The programs that start at boot. The apps wait in their slots until started. */
    for (uint64_t i = 0; i < ntasks; i++)
        if (leanos_autostart(lean_box(i))) {
            load_program(i);
            measure_and_verify(i);
        }
    for (uint64_t i = 0; i < ntasks; i++) {
        tables_init(i);
        build_user_pages(i);
    }
    irq_init();

    if (!ready(cur_task())) K = leanos_tick(K);
    uint64_t first = idle_until_ready();
    switch_to(first);
    enter_user(&saved[first]);
}
