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

Capabilities name runs of frames; each task has 256 frames (1 MiB) and a 32 MiB window. The
framebuffer (1024×600, allocated at boot through the mailbox, which stays in trusted C
because it is a DMA path) goes to the display server; the UART's registers and interrupt go
to an input driver. Interrupt capabilities are fixed by the manifest; a fired line is
masked until its holder acknowledges it. Call and reply let clients wait on the display
server without it ever blocking on them. Proved: only the display server reaches the
screen, only the input driver the UART, an interrupt wakes only its holder, replies grant
nothing. The desktop has a boot logo, rounded shadowed windows, a pointer, dragging, and
typing into the focused window.

## 5. Verified boot — in the OS, done; on the chip, next

Done: every task starts unverified; the machine layer measures what it loaded (SHA-256 of
code and assets) and the Lean kernel lets a task run only if that matches the boot
manifest compiled into the kernel. Proved: `only_verified_runs`, `verify_refuses_mismatch`.
The boot screen shows each program's verdict and hash; `make test` flips one bit of a
program in the image and checks it is refused.

Next, on real hardware: sign the boot image for the Pi 4 bootloader's secure-boot mode
(RSA-2048, key hash in the chip's OTP memory, which cannot be undone), so the manifest
itself is covered by the chip's root of trust.

## 6. Memory and processes from user space — starting and stopping, done; building, next

Done: the manifest has eight program slots, and the apps (Terminal, Settings, Security)
wait in theirs until started. A launch capability, fixed by the manifest and held only by
the display server, starts or restarts a slot whose program is not running. Starting
first takes back everything the slot's last run shared: every other task loses its
capabilities to the slot's frames, its mappings of them, grants of them in messages still
waiting to be delivered, and any reply slot it holds for the old run. Then the slot gets
the manifest's fresh task, and the machine layer clears the frames, loads the program and
measures it; it runs only if it matches. Proved: `start_revokes`, `only_display_launches`,
`confined` (every task but the display server reaches only its own memory). To make
revocation exact, every run of frames is proved to stay inside one slot's memory
(`RunOK`). The dock starts apps, a window's close button stops its app, and the display
closes the windows of apps that stop.

Next: untyped memory capabilities and retyping, so a root task builds the system from
user space: creating tasks and endpoints at run time instead of from the manifest, and a
capability derivation tree for revoking what was derived, not just what a slot owns.

## 7. The GUI

A display server that owns the framebuffer and composites windows; clients draw into
memory they share with it by grant, never into each other's. Proved: a client's pixels
only ever come from memory it was granted. Keyboard and mouse input: the Pi 4's USB goes
through PCIe and the VL805 xHCI controller, which is a large driver, so input starts on
the UART and USB comes after.

## 8. A bounded kernel

Prove how much kernel memory each operation can use, and preallocate per task, so no
system call can exhaust the kernel heap. Replace list-based state where it grows with
the system. The kernel stack is the same problem: the Lean kernel recurses once per list
element, and a task can hold up to 8192 mappings. Today the stack is sized for that (2 MiB),
painted at boot and checked on every return to user mode, so an overflow stops the machine
instead of corrupting it; stage 6 found this the hard way, when revocation walked the
display server's 900 mappings and overran the old 64 KiB stack. The fix that belongs here
is to prove a bound, or make the walks iterative.

## 9. A system people can use — files on the SD card, done; the rest, next

Done: a file server in user space, with its own endpoint, keeps up to 48 files of up to
16 KiB in its own memory. Clients (Notes, Terminal, Files) grant it their 4-page buffer
with every request, and it maps, uses, unmaps and drops the buffer before it answers, so
it never holds anyone's memory between requests (`drop`, a new system call, is proved to
only take authority away). The manifest's grant edges now form two stars (apps to the
display server, clients to the file server) and the proofs show memory moves at most one
step. Notes keeps its note across restarts, Terminal has `ls`, `cat`, `write` and `rm`,
and the Files app browses and deletes.

Done too: the SD card. A small SDHCI driver in the machine layer moves one block at a time
by programmed I/O (never DMA, which could write anywhere), and only what the Lean kernel
approved: block capabilities, held only by the file server, name the blocks it may use,
and `block_io_confined` proves every transfer is inside one, into or out of memory the
caller has mapped with the right permission. The file server keeps its table and files on
the card and reads them back at boot, so files and the note survive a restart; with no
card it keeps them in memory.

Next: a journal (so a power cut cannot lose a change halfway), the SD card on real Pi 4
hardware (EMMC2), a loader for ELF programs, multiple cores, and the Pi 5.
