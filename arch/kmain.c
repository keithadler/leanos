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
lean_object *leanos_init(lean_object *n);
lean_object *leanos_syscall(lean_object *s, lean_object *num, lean_object *a0, lean_object *a1);
lean_object *leanos_tick(lean_object *s);
lean_object *leanos_fault(lean_object *s);
lean_object *leanos_cur(lean_object *s);
uint8_t leanos_alive(lean_object *s, lean_object *i);
lean_object *leanos_ntasks(lean_object *s);
lean_object *leanos_nmaps(lean_object *s, lean_object *i);
lean_object *leanos_map(lean_object *s, lean_object *i, lean_object *k);
lean_object *leanos_reply_status(lean_object *r);
lean_object *leanos_reply_value(lean_object *r);
lean_object *leanos_reply_out_va(lean_object *r);
lean_object *leanos_reply_out_len(lean_object *r);
uint8_t leanos_reply_remap(lean_object *r);
uint8_t leanos_reply_resched(lean_object *r);
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
static int alive(uint64_t i) { return leanos_alive(K1, lean_box(i)); }

/* ---- console ---- */

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
    /* PSCI SYSTEM_OFF through the hypervisor call QEMU's virt board provides. */
    register uint64_t x0 __asm__("x0") = 0x84000008;
    __asm__ volatile("hvc #0" : "+r"(x0));
    for (;;) __asm__ volatile("wfi");
}

void kpanic(const char *msg) {
    kputs("\nleanos: PANIC: ");
    kputs(msg);
    kputs("\n");
    poweroff();
}

/* ---- memory management unit ----
 * 4 KiB pages, 39-bit addresses, translation starts at level 1 (1 GiB per entry).
 *   L1[0]  0x0000_0000  devices (UART, GIC), kernel only
 *   L1[1]  0x4000_0000  all RAM, kernel only, never executable from user mode
 *   L1[2]  0x8000_0000  the task's user window, built from its mappings in the Lean state
 * Every task has its own tables and address-space number (ASID = task + 1); the kernel
 * entries are the same in all of them. */

#define PTE_VALID (1UL << 0)
#define PTE_TABLE (1UL << 1)
#define PTE_PAGE (1UL << 1)
#define PTE_ATTR(i) ((uint64_t)(i) << 2)
#define PTE_AP_EL0_RW (1UL << 6)
#define PTE_AP_EL0_RO (3UL << 6)
#define PTE_SH_INNER (3UL << 8)
#define PTE_AF (1UL << 10)
#define PTE_NG (1UL << 11)
#define PTE_PXN (1UL << 53)
#define PTE_UXN (1UL << 54)
#define ATTR_DEVICE 0
#define ATTR_NORMAL 1

static uint64_t kl1[512] __attribute__((aligned(4096)));
static uint64_t tl1[MAX_TASKS][512] __attribute__((aligned(4096)));
static uint64_t tl2[MAX_TASKS][512] __attribute__((aligned(4096)));
static uint64_t tl3[MAX_TASKS][512] __attribute__((aligned(4096)));

static void tlb_flush_all(void) {
    DSB(ishst);
    __asm__ volatile("tlbi vmalle1is" ::: "memory");
    DSB(ish);
    ISB();
}

static void mmu_init(void) {
    kl1[0] = 0x00000000UL | PTE_VALID | PTE_ATTR(ATTR_DEVICE) | PTE_AF | PTE_PXN | PTE_UXN;
    kl1[1] = 0x40000000UL | PTE_VALID | PTE_ATTR(ATTR_NORMAL) | PTE_SH_INNER | PTE_AF | PTE_UXN;

    SYSREG_WRITE(mair_el1, (0x04UL << (8 * ATTR_DEVICE)) | (0xffUL << (8 * ATTR_NORMAL)));
    uint64_t tcr = 25                /* T0SZ: 39-bit addresses */
                 | (1UL << 8)        /* inner write-back walks */
                 | (1UL << 10)       /* outer write-back walks */
                 | (3UL << 12)       /* inner shareable */
                 | (0UL << 14)       /* 4 KiB granule */
                 | (1UL << 23)       /* no TTBR1 walks: the kernel lives in the low half */
                 | (1UL << 32);      /* 36-bit physical addresses */
    SYSREG_WRITE(tcr_el1, tcr);
    SYSREG_WRITE(ttbr0_el1, (uint64_t)kl1);
    ISB();
    tlb_flush_all();
    uint64_t sctlr = SYSREG_READ(sctlr_el1);
    sctlr |= (1 << 0) | (1 << 2) | (1 << 12); /* MMU, data cache, instruction cache */
    SYSREG_WRITE(sctlr_el1, sctlr);
    ISB();
}

/* Task i's top two levels never change: the kernel's two entries and a path to the
   task's level-3 table. Set once at boot. */
static void tables_init(uint64_t i) {
    memset(tl1[i], 0, 4096);
    memset(tl2[i], 0, 4096);
    tl1[i][0] = kl1[0];
    tl1[i][1] = kl1[1];
    tl1[i][2] = (uint64_t)tl2[i] | PTE_VALID | PTE_TABLE;
    tl2[i][0] = (uint64_t)tl3[i] | PTE_VALID | PTE_TABLE;
}

/* Rebuild task i's user pages from its mappings in the Lean state. The Lean kernel has
   already decided every entry; this only encodes them. Only the level-3 table is
   rewritten, so the kernel's own mappings stay valid even when i is the task whose
   address space is live. */
static void build_user_pages(uint64_t i) {
    uint64_t *l3 = tl3[i];
    memset(l3, 0, 4096);
    uint64_t n = nat(leanos_nmaps(K1, lean_box(i)));
    for (uint64_t k = 0; k < n; k++) {
        uint64_t m = nat(leanos_map(K1, lean_box(i), lean_box(k)));
        uint64_t vpn = m & 0xffff, frame = (m >> 16) & 0xffff, bits = m >> 32;
        if (vpn >= USER_PAGES || frame >= NFRAMES) kpanic("mapping out of range");
        if (!(bits & 1)) continue; /* the MMU cannot express write or execute without read */
        uint64_t pte = (FRAME_BASE + frame * PAGE_SIZE) | PTE_VALID | PTE_PAGE |
                       PTE_ATTR(ATTR_NORMAL) | PTE_SH_INNER | PTE_AF | PTE_NG | PTE_PXN;
        pte |= (bits & 2) ? PTE_AP_EL0_RW : PTE_AP_EL0_RO;
        if (!(bits & 4)) pte |= PTE_UXN;
        l3[vpn] = pte;
    }
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
    timer_interval = SYSREG_READ(cntfrq_el0) / 100;     /* 10 ms time slice */
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

static const char *const names[] = {"alice", "bob", "carol"};

static void do_syscall(uint64_t cur) {
    struct frame *f = &saved[cur];
    syscalls++;
    lean_object *r = leanos_syscall(K, arg(f->x[8]), arg(f->x[0]), arg(f->x[1]));
    uint64_t status = nat(leanos_reply_status((lean_inc(r), r)));
    uint64_t value = nat(leanos_reply_value((lean_inc(r), r)));
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
    f->x[0] = status;
    f->x[1] = value;
    if (remap) build_user_pages(cur);
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
            kputs(cur < 3 ? names[cur] : "task");
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
    if (!alive(next)) {
        kputs("leanos: every task has finished (");
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
    switch_to(next);
    *f = saved[next];
}

void kmain(void) {
    kputs("leanos: booting on ");
    uint64_t el = SYSREG_READ(CurrentEL) >> 2;
    kputs(el == 1 ? "EL1" : "EL?");
    kputs("\n");

    mmu_init();
    kputs("leanos: MMU on\n");

    lean_object *res = initialize_leanos_LeanOS_Kernel(1);
    if (!lean_io_result_is_ok(res)) kpanic("Lean module initialization failed");
    lean_dec(res);

    ntasks = 3;
    K = leanos_init(lean_box(ntasks));
    if (nat(leanos_ntasks(K1)) != ntasks) kpanic("kernel made the wrong number of tasks");
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
