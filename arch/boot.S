// Entry, exception vectors and the return to user mode.
// Trusted, not proved (see TRUST.md). Everything here is mechanism: no decisions.

#define FRAME_SIZE 288

// If this core runs at EL2 (a Pi 4's firmware armstub leaves every core there; so does
// QEMU), set up what EL1 relies on and drop to EL1h, interrupts masked, at `target`. The
// armstub (raspberrypi/tools, armstubs/armstub8.S) sets CNTFRQ_EL0 (54 MHz), CNTVOFF_EL2,
// CPTR_EL3, SCR_EL3 and the GIC, and nothing else of EL2's, so everything EL1 needs from
// EL2 is set here rather than left at reset values the architecture calls UNKNOWN:
//   HCR_EL2      RW (EL1 is AArch64), and nothing trapped or virtualized
//   CNTHCTL_EL2  EL1 may use the physical timer and counter (EL1PCEN, EL1PCTEN)
//   CPTR_EL2     no floating-point or SIMD traps to EL2 (TFP clear; 0x33ff, as Linux sets)
//   HSTR_EL2     no system-register traps to EL2
//   VPIDR_EL2, VMPIDR_EL2  what EL1 reads as MIDR_EL1 and MPIDR_EL1: the real values, so
//                each core's number (this_core, secondary) is its own
//   SCTLR_EL1    reserved-one bits, MMU and caches off
.macro TO_EL1 target
    mrs     x0, CurrentEL
    lsr     x0, x0, #2
    cmp     x0, #2
    b.ne    \target
    mov     x0, #(1 << 31)
    msr     hcr_el2, x0
    mov     x0, #3
    msr     cnthctl_el2, x0
    msr     cntvoff_el2, xzr
    mov     x0, #0x33ff
    msr     cptr_el2, x0
    msr     hstr_el2, xzr
    mrs     x0, midr_el1
    msr     vpidr_el2, x0
    mrs     x0, mpidr_el1
    msr     vmpidr_el2, x0
    ldr     x0, =0x30d00800
    msr     sctlr_el1, x0
    mov     x0, #0x3c5              // EL1h, interrupts masked
    msr     spsr_el2, x0
    adr     x0, \target
    msr     elr_el2, x0
    eret
.endm

.section .text.boot, "ax"
.global _start
_start:
    // Core 0 brings the kernel up. Cores 1-3 wait in the boot stub's spin table (the
    // firmware's armstub on a Pi 4, QEMU's own in emulation) until core 0 hands them
    // `secondary` (kmain.c: start_cores); a core that arrives here anyway parks.
    mrs     x0, mpidr_el1
    and     x0, x0, #0xff
    cbnz    x0, park

    // The kernel is linked to run at 0x80000 (arch/kernel.ld), and the firmware loads it
    // where config.txt's kernel_address says (0x200000 by default for a 64-bit kernel on
    // current firmware, which is why tools/mkpiimage.py sets it). Anywhere else, nothing
    // here can run, not even the UART: turn the green activity light (GPIO 42) on, which
    // this code can do from any address, and stop.
    adr     x1, _start
    ldr     x2, =_start
    cmp     x1, x2
    b.ne    loaded_elsewhere

    TO_EL1  1f
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
    wfi
    b       park

loaded_elsewhere:
    ldr     x0, =0xFE200010         // GPFSEL4: GPIO 42 (bits 6-8) an output
    ldr     w1, [x0]
    bic     w1, w1, #(7 << 6)
    orr     w1, w1, #(1 << 6)
    str     w1, [x0]
    ldr     x0, =0xFE200020         // GPSET1: GPIO 42 (bit 10) high, the light on
    mov     w1, #(1 << 10)
    str     w1, [x0]
    b       park

// Cores 1-3, once core 0 has the kernel up: the same drop to EL1, then this core's MMU
// and caches on, with the values core 0 used (kmain.c: mmu_regs, cleaned out to memory),
// before anything touches memory this core will read back: until then its loads and
// stores bypass the caches, while core 0 runs with them on. Then its own stack (from
// core_stack_top), the vectors, and secondary_main(core).
.global secondary
secondary:
    TO_EL1  5f
5:
    ldr     x1, =mmu_regs
    ldp     x2, x3, [x1]            // MAIR_EL1, TCR_EL1
    ldp     x4, x5, [x1, #16]       // TTBR0_EL1, SCTLR_EL1
    msr     mair_el1, x2
    msr     tcr_el1, x3
    msr     ttbr0_el1, x4
    isb
    tlbi    vmalle1
    ic      iallu
    dsb     nsh
    isb
    msr     sctlr_el1, x5
    isb
    ic      iallu
    dsb     nsh
    isb
    mrs     x0, mpidr_el1
    and     x0, x0, #0xff
    ldr     x1, =core_stack_top
    ldr     x2, [x1, x0, lsl #3]
    cbz     x2, park
    mov     sp, x2
    mov     x1, #(1 << 20)
    msr     cpacr_el1, x1
    isb
    ldr     x1, =vectors
    msr     vbar_el1, x1
    isb
    bl      secondary_main
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

// enter_user(struct frame *f, stack_top): start running a task on this core. Copies the
// frame onto the top of this core's kernel stack and returns through the same path as a trap.
.global enter_user
enter_user:
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
    .quad prog0, prog1, prog2, prog3, prog4, prog5, prog6, prog7, prog8, prog9
    .quad noasset, noasset, noasset, noasset, noasset, noasset, prog16, prog17    // 10-15: open slots
user_prog_ends:
    .quad prog0_end, prog1_end, prog2_end, prog3_end, prog4_end, prog5_end, prog6_end, prog7_end, prog8_end, prog9_end
    .quad noasset, noasset, noasset, noasset, noasset, noasset, prog16_end, prog17_end
.global user_assets, user_asset_ends
user_assets:
    .quad asset0, asset1, noasset, noasset, noasset, asset5, asset6, asset7, noasset, asset9
    .quad noasset, noasset, noasset, noasset, noasset, noasset, asset16, noasset
user_asset_ends:
    .quad asset0_end, asset1_end, noasset, noasset, noasset, asset5_end, asset6_end, asset7_end, noasset, asset9_end
    .quad noasset, noasset, noasset, noasset, noasset, noasset, asset16_end, noasset
// The fonts every program from the SD card gets in its spare run, as the built-in apps get
// their assets: data in the program's own memory, which grants nothing.
.global open_assets, open_assets_end
open_assets:
    .quad open_blob
open_assets_end:
    .quad open_blob_end
.balign 16
asset0: .incbin "build/assets/alice.bin"
asset0_end:
.balign 16
asset1: .incbin "build/assets/display.bin"
asset1_end:
.balign 16
asset5: .incbin "build/assets/terminal.bin"
asset5_end:
.balign 16
asset6: .incbin "build/assets/settings.bin"
asset6_end:
.balign 16
asset7: .incbin "build/assets/security.bin"
asset7_end:
.balign 16
asset9: .incbin "build/assets/files.bin"
asset9_end:
.balign 16
asset16: .incbin "build/assets/launcher.bin"
asset16_end:
.balign 16
open_blob: .incbin "build/assets/open.bin"
open_blob_end:
noasset:
.balign 16
prog0: .incbin "build/user/alice.bin"
prog0_end:
.balign 16
prog1: .incbin "build/user/display.bin"
prog1_end:
.balign 16
prog2: .incbin "build/user/mallory.bin"
prog2_end:
.balign 16
prog3: .incbin "build/user/carol.bin"
prog3_end:
.balign 16
prog4: .incbin "build/user/input.bin"
prog4_end:
.balign 16
prog5: .incbin "build/user/terminal.bin"
prog5_end:
.balign 16
prog6: .incbin "build/user/settings.bin"
prog6_end:
.balign 16
prog7: .incbin "build/user/security.bin"
prog7_end:
.balign 16
prog8: .incbin "build/user/fs.bin"
prog8_end:
.balign 16
prog9: .incbin "build/user/files.bin"
prog9_end:
.balign 16
prog16: .incbin "build/user/launcher.bin"
prog16_end:
.balign 16
prog17: .incbin "build/user/usb.bin"
prog17_end:
