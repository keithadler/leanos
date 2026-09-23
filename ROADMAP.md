# Roadmap

The goal is a first-class operating system with a graphical interface, running on the
Raspberry Pi, whose security rests on proofs rather than review. The rule for getting
there: each stage lands with its theorems. A feature that would need unproved code in the
kernel's decisions waits until it can be proved.

Every stage ends the same way: `make test` passes (proofs, axiom check, boot
transcript), a deliberately broken version of the new code is shown to fail its proofs,
and TRUST.md is updated.

**Target.** Raspberry Pi 4 Model B: a Cortex-A72, the GIC-400 interrupt controller,
PL011 UART, and the VideoCore mailbox for the framebuffer. It is tested on QEMU's
`raspi4b` machine and on real boards. The Pi 5 comes later: its peripherals sit behind
the RP1 chip, which is much less documented, and no emulator models it.

## 1. Proved decisions — done

Capabilities, mappings, system calls and scheduling are Lean code in the kernel image.
Isolation, W^X, no amplification, backed mappings, a checked `write`, and a scheduler that
picks live tasks are proved for every reachable state.

## 2. The Pi, with proved hardware tables — done

Port to the Pi 4. The Lean kernel computes every translation-table word the MMU reads,
not just the list of mappings. A model of the Armv8-A stage-1 walk (`LeanOS/Arm.lean`)
turns table memory into what EL0 may do at each virtual address. The theorem: if the
machine layer stores the words Lean computed, user mode can reach exactly the frames its
mappings name, with exactly their rights, and nothing of the kernel's. This takes
page-table encoding off the trusted list.

## 3. Communication — done

Synchronous IPC through endpoint capabilities: send and receive with a few registers and
an optional capability transfer, with tasks blocking and waking. The isolation theorem
changes from "task memory never overlaps" to authority confinement: a task can reach a
frame only if a chain of explicit grants gave it one. (Done with endpoint capabilities
fixed by the boot manifest; creating and passing endpoints waits for stage 5.) A GUI needs this: clients talk to
the display server over IPC and hand it the memory they draw into.

## 4. Drivers in user space — done

Capabilities name runs of frames; each task has 64 frames and a 32 MiB window. The
framebuffer (1024×600, allocated at boot through the mailbox, which stays in trusted C
because it is a DMA path) goes to the display server; the UART's registers and interrupt go
to an input driver. Interrupt capabilities are fixed by the manifest; a fired line is
masked until its holder acknowledges it. Call and reply let clients wait on the display
server without it ever blocking on them. Proved: only the display server reaches the
screen, only the input driver the UART, an interrupt wakes only its holder, replies grant
nothing. The desktop has a boot logo, rounded shadowed windows, a pointer, dragging, and
typing into the focused window.

## 5. Verified boot

Show on the boot screen, step by step, that nothing was tampered with. The Pi 4's bootloader
can verify an RSA signature on the boot image against a key hash burned into the chip's
OTP memory (Raspberry Pi secure boot); leanos then checks each program it starts against a
hash in that signed image before running it, and the progress bar follows those checks.
Proved: the kernel starts a program only if its hash matches the manifest.

## 6. Memory and processes from user space

Untyped memory capabilities and retyping, so a root task builds the system: creating
tasks, handing out frames, and revoking them (a capability derivation tree).

## 7. The GUI

A display server that owns the framebuffer and composites windows; clients draw into
memory they share with it by grant, never into each other's. Proved: a client's pixels
only ever come from memory it was granted. Keyboard and mouse input: the Pi 4's USB goes
through PCIe and the VL805 xHCI controller, which is a large driver, so input starts on
the UART and USB comes after.

## 8. A bounded kernel

Prove how much kernel memory each operation can use, and preallocate per task, so no
system call can exhaust the kernel heap. Replace list-based state where it grows with
the system.

## 9. A system people can use

A shell and file manager in the GUI, a RAM file system then the SD card, a loader for ELF
programs, multiple cores, and the Pi 5.
