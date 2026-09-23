// Entry, exception vectors and the return to user mode.
// Trusted, not proved (see TRUST.md). Everything here is mechanism: no decisions.

#define FRAME_SIZE 288

.section .text.boot, "ax"
.global _start
_start:
    // Only core 0 runs the kernel; any other core parks.
    mrs     x0, mpidr_el1
    and     x0, x0, #0xff
    cbnz    x0, park

    // If started at EL2, drop to EL1.
    mrs     x0, CurrentEL
    lsr     x0, x0, #2
    cmp     x0, #2
    b.ne    1f
    mov     x0, #(1 << 31)          // EL1 runs AArch64
    msr     hcr_el2, x0
    mov     x0, #0x3c5              // EL1h, interrupts masked
    msr     spsr_el2, x0
    adr     x0, 1f
    msr     elr_el2, x0
    eret
1:
    ldr     x0, =__stack_top
    mov     sp, x0

    // Floating point: allowed at EL1 (compiled code may use SIMD registers for copies),
    // trapped at EL0, so no user program can see what the kernel left in them.
    mov     x0, #(1 << 20)
    msr     cpacr_el1, x0
    isb

    ldr     x0, =__bss_start
    ldr     x1, =__bss_end
2:  cmp     x0, x1
    b.hs    3f
    str     xzr, [x0], #8
    b       2b
3:
    ldr     x0, =vectors
    msr     vbar_el1, x0
    isb
    bl      kmain
park:
    wfe
    b       park

// ---- exception vectors ----
// Each entry makes room for a frame, saves x0/x1, puts the kind of exception in x1 and
// jumps to the common path. Kinds: 0 sync from EL0, 1 IRQ from EL0, 2 sync from EL1,
// 3 IRQ from EL1, 4 anything else.

.macro VENTRY kind
    .balign 0x80
    sub     sp, sp, #FRAME_SIZE
    stp     x0, x1, [sp, #0]
    mov     x1, #\kind
    b       trap_common
.endm

.section .text
.balign 0x800
.global vectors
vectors:
    VENTRY 4    // current EL, SP0: sync
    VENTRY 4    //   irq
    VENTRY 4    //   fiq
    VENTRY 4    //   serror
    VENTRY 2    // current EL, SPx: sync
    VENTRY 3    //   irq
    VENTRY 4    //   fiq
    VENTRY 4    //   serror
    VENTRY 0    // lower EL, AArch64: sync
    VENTRY 1    //   irq
    VENTRY 4    //   fiq
    VENTRY 4    //   serror
    VENTRY 4    // lower EL, AArch32: sync
    VENTRY 4    //   irq
    VENTRY 4    //   fiq
    VENTRY 4    //   serror

trap_common:
    stp     x2, x3, [sp, #16]
    stp     x4, x5, [sp, #32]
    stp     x6, x7, [sp, #48]
    stp     x8, x9, [sp, #64]
    stp     x10, x11, [sp, #80]
    stp     x12, x13, [sp, #96]
    stp     x14, x15, [sp, #112]
    stp     x16, x17, [sp, #128]
    stp     x18, x19, [sp, #144]
    stp     x20, x21, [sp, #160]
    stp     x22, x23, [sp, #176]
    stp     x24, x25, [sp, #192]
    stp     x26, x27, [sp, #208]
    stp     x28, x29, [sp, #224]
    mrs     x21, sp_el0
    stp     x30, x21, [sp, #240]
    mrs     x22, elr_el1
    mrs     x23, spsr_el1
    stp     x22, x23, [sp, #256]
    mov     x0, sp                  // trap(struct frame *, kind)
    bl      trap
    b       restore

// enter_user(struct frame *f): start running a task for the first time. Copies the frame
// onto the top of the kernel stack and returns through the same path as a trap.
.global enter_user
enter_user:
    ldr     x1, =__stack_top
    sub     sp, x1, #FRAME_SIZE
    mov     x2, sp
    mov     x3, #(FRAME_SIZE / 8)
4:  ldr     x4, [x0], #8
    str     x4, [x2], #8
    subs    x3, x3, #1
    b.ne    4b
restore:
    ldp     x22, x23, [sp, #256]
    msr     elr_el1, x22
    msr     spsr_el1, x23
    ldp     x30, x21, [sp, #240]
    msr     sp_el0, x21
    ldp     x0, x1, [sp, #0]
    ldp     x2, x3, [sp, #16]
    ldp     x4, x5, [sp, #32]
    ldp     x6, x7, [sp, #48]
    ldp     x8, x9, [sp, #64]
    ldp     x10, x11, [sp, #80]
    ldp     x12, x13, [sp, #96]
    ldp     x14, x15, [sp, #112]
    ldp     x16, x17, [sp, #128]
    ldp     x18, x19, [sp, #144]
    ldp     x20, x21, [sp, #160]
    ldp     x22, x23, [sp, #176]
    ldp     x24, x25, [sp, #192]
    ldp     x26, x27, [sp, #208]
    ldp     x28, x29, [sp, #224]
    add     sp, sp, #FRAME_SIZE
    eret

// ---- user programs, embedded in the kernel image ----
.section .rodata
.balign 16
.global user_progs, user_prog_ends
user_progs:
    .quad prog0, prog1, prog2
user_prog_ends:
    .quad prog0_end, prog1_end, prog2_end
.balign 16
prog0: .incbin "build/user/alice.bin"
prog0_end:
.balign 16
prog1: .incbin "build/user/bob.bin"
prog1_end:
.balign 16
prog2: .incbin "build/user/carol.bin"
prog2_end:
