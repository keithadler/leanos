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
lean_object *leanos_init(lean_object *unused);
lean_object *leanos_syscall(lean_object *s, lean_object *num, lean_object *a0, lean_object *a1,
                            lean_object *a2, lean_object *a3, lean_object *a4);
lean_object *leanos_tick(lean_object *s);
lean_object *leanos_fault(lean_object *s);
lean_object *leanos_clear_result(lean_object *s, lean_object *j);
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
lean_object *leanos_reply_state(lean_object *r);

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

/* A user register becomes a Lean Nat. Values at or above 2^62 are clamped to 2^62; every
   system call rejects anything that large, so the clamp never changes an outcome. */
static lean_object *arg(uint64_t v) {
    const uint64_t cap = 1ULL << 62;
    return lean_box(v < cap ? v : cap);
}

static uint64_t cur_task(void) { return nat(leanos_cur(K1)); }
static int ready(uint64_t i) { return leanos_ready(K1, lean_box(i)); }

/* ---- console ---- */

/* PL011 at 115200 8N1. The Pi 4 feeds the UART a 48 MHz clock: 48e6 / (16 * 115200)
   = 26.0417, so the divisor is 26 + 3/64. */
static void uart_init(void) {
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

void kpanic(const char *msg) {
    kputs("\nleanos: PANIC: ");
    kputs(msg);
    kputs("\n");
    poweroff();
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
static uint64_t tl3[MAX_TASKS][512] __attribute__((aligned(4096)));

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

    /* Memory attribute 0: device nGnRE. Attribute 1: normal, write-back. */
    SYSREG_WRITE(mair_el1, (0x04UL << 0) | (0xffUL << 8));
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

/* Rewrite task i's level-3 table from the Lean state. Only level 3 changes, so the
   kernel's own entries stay valid even when i is the task whose address space is live. */
static void build_user_pages(uint64_t i) {
    for (uint64_t k = 0; k < 512; k++) tl3[i][k] = word(leanos_l3(K1, lean_box(i), lean_box(k)));
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

static void irq_init(void) {
    mmio_w32(GICD + 0x000, 1);                          /* distributor on */
    mmio_w8(GICD + 0x400 + TIMER_IRQ, 0x80);            /* priority */
    mmio_w32(GICD + 0x100, 1u << TIMER_IRQ);            /* enable the timer interrupt */
    mmio_w32(GICC + 0x004, 0xff);                       /* accept every priority */
    mmio_w32(GICC + 0x000, 1);                          /* CPU interface on */
    uint64_t freq = SYSREG_READ(cntfrq_el0);
    if (freq == 0) freq = 54000000;                     /* the Pi 4's crystal, if firmware left it unset */
    timer_interval = freq / 100;                        /* 10 ms time slice */
    timer_rearm();
}

/* ---- tasks ---- */

static struct frame saved[MAX_TASKS];
static uint64_t ntasks;
static uint64_t syscalls, ticks;

extern const uint64_t user_progs[], user_prog_ends[];

static void sync_icache(uint64_t start, uint64_t len) {
    for (uint64_t a = start & ~63UL; a < start + len; a += 64)
        __asm__ volatile("dc cvau, %0" :: "r"(a) : "memory");
    DSB(ish);
    __asm__ volatile("ic iallu" ::: "memory");
    DSB(ish);
    ISB();
}

static void load_programs(void) {
    memset((void *)FRAME_BASE, 0, NFRAMES * PAGE_SIZE);
    for (uint64_t i = 0; i < ntasks; i++) {
        uint64_t len = user_prog_ends[i] - user_progs[i];
        if (len > PAGE_SIZE) kpanic("user program larger than its code frame");
        uint64_t code = FRAME_BASE + 4 * i * PAGE_SIZE; /* frame 4i, as `mkTask` says */
        memcpy((void *)code, (const void *)user_progs[i], len);
        sync_icache(code, len);
        saved[i].elr = USER_BASE;
        saved[i].sp = USER_BASE + USER_PAGES * PAGE_SIZE;
        saved[i].spsr = 0; /* EL0, interrupts on */
    }
}

static const char *const names[] = {"alice", "server", "mallory", "carol"};

static void do_syscall(uint64_t cur) {
    struct frame *f = &saved[cur];
    syscalls++;
    lean_object *r = leanos_syscall(K, arg(f->x[8]), arg(f->x[0]), arg(f->x[1]), arg(f->x[2]),
                                    arg(f->x[3]), arg(f->x[4]));
    uint64_t out_va = nat(leanos_reply_out_va((lean_inc(r), r)));
    uint64_t out_len = nat(leanos_reply_out_len((lean_inc(r), r)));
    int remap = leanos_reply_remap((lean_inc(r), r));
    K = leanos_reply_state(r);

    /* Still in `cur`'s address space, so the range the kernel checked is readable here. */
    for (uint64_t k = 0; k < out_len; k++) {
        char c = ((volatile const char *)out_va)[k];
        if (c == '\n') kputc('\r');
        kputc(c);
    }
    if (remap) build_user_pages(cur);
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

static void finish(void) {
    uint64_t waiting = 0;
    for (uint64_t i = 0; i < ntasks; i++)
        if (!leanos_dead(K1, lean_box(i))) waiting++;
    if (waiting == 0) kputs("leanos: every task has finished (");
    else {
        kputs("leanos: no task can run: ");
        kputdec(waiting);
        kputs(" waiting for a message that will not come (");
    }
    kputdec(syscalls);
    kputs(" system calls, ");
    kputdec(ticks);
    kputs(" timer ticks, kernel heap ");
    kputdec(rt_heap_live());
    kputs(" bytes live, ");
    kputdec(rt_heap_peak());
    kputs(" peak)\n");
    poweroff();
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
            kputs(cur < 4 ? names[cur] : "task");
            kputs(" stopped: ");
            kputs(fault_name(ec));
            kputs(" at ");
            kputhex(ec == 0x20 || ec == 0x24 ? SYSREG_READ(far_el1) : f->elr);
            kputs("\n");
            K = leanos_fault(K);
        }
    } else {
        uint32_t iar = mmio_r32(GICC + 0x00c);
        if ((iar & 0x3ff) == TIMER_IRQ) {
            ticks++;
            timer_rearm();
            K = leanos_tick(K);
        }
        mmio_w32(GICC + 0x010, iar);
    }

    uint64_t next = cur_task();
    if (!ready(next)) finish(); /* schedule found no ready task */
    load_result(next);
    switch_to(next);
    *f = saved[next];
}

void kmain(void) {
    uart_init();
    kputs("leanos: Raspberry Pi 4, booting on ");
    uint64_t el = SYSREG_READ(CurrentEL) >> 2;
    kputs(el == 1 ? "EL1" : "EL?");
    kputs("\n");

    /* The Lean kernel comes up first: it computes the tables the MMU is turned on with. */
    lean_object *res = initialize_leanos_LeanOS_Kernel(1);
    if (!lean_io_result_is_ok(res)) kpanic("Lean module initialization failed");
    lean_dec(res);

    mmu_init();
    kputs("leanos: MMU on\n");

    K = leanos_init(lean_box(0));
    ntasks = nat(leanos_ntasks(K1));
    if (ntasks > MAX_TASKS || ntasks > 4) kpanic("the manifest has more tasks than the machine layer supports");
    kputs("leanos: Lean kernel initialized, ");
    kputdec(ntasks);
    kputs(" tasks\n");

    load_programs();
    for (uint64_t i = 0; i < ntasks; i++) {
        tables_init(i);
        build_user_pages(i);
    }
    irq_init();

    uint64_t first = cur_task();
    switch_to(first);
    enter_user(&saved[first]);
}
