# leanos

A small AArch64 kernel whose decisions are written in Lean 4, compiled into the kernel,
and proved correct.

The part that decides who may touch what is Lean code: capabilities, address spaces,
system calls and the scheduler. It is compiled to C and linked into the kernel image. The
theorems in `LeanOS/Proofs.lean` are about that same code, so there is no separate
specification that could drift from what runs. Underneath, about 1,000 lines of C and
assembly boot the board, write page tables and switch tasks, but make no access decisions.

It runs on QEMU's `virt` machine: three user tasks, preempted by the timer, each in its own
address space.

```
leanos: booting on EL1
leanos: MMU on
leanos: Lean kernel initialized, 3 tasks
alice: wrote secret 0x5ec12e7 to my data page
alice: still working, round 1
bob: I am task 1
bob: map capability 9 (not mine) at page 5 -> refused, no such capability
bob: print 16 bytes of kernel memory at 0x40080000 -> refused, bad argument
bob: print from page 7, which I have not mapped -> refused, bad argument
bob: asked for rwx on my data frame, got capability 4 with rw-
bob: map my spare frame (capability 3) at page 2 -> ok
bob: wrote and read back 42 through page 2
bob: now reading page 3 directly, which is not mapped
leanos: bob stopped: data access not allowed at 0x80003000
carol: asked for write+execute on my data frame, got -w-
carol: jumping into the instruction I wrote in my data page
leanos: carol stopped: instruction fetch not allowed at 0x80001000
alice: still working, round 2
alice: still working, round 3
alice: secret intact, exiting
leanos: every task has finished (25 system calls, 2 timer ticks, kernel heap 4832 bytes live, 5008 peak)
```

## What is proved

For every state the kernel can reach, under any sequence of system calls with any
arguments:

- **Isolation**: no physical frame is visible to two different tasks.
- **W^X**: no page is ever both writable and executable.
- **No amplification**: a derived capability never allows more than its parent.
- **Every mapping is backed** by a capability the task holds, with the same rights.
- **`write` reads only memory the task may read.**
- **The scheduler never picks a stopped task** while a live one exists.

[TRUST.md](TRUST.md) lists exactly what the proofs cover and what is taken on trust (the
Lean compiler, the runtime shim, the page-table encoding, the hardware).

## Build and run

You need Lean via `elan` (the version in `lean-toolchain` is picked up automatically),
Homebrew's `llvm` and `lld` for the cross compiler and linker, and `qemu`.

```bash
make          # build build/leanos.elf and check every proof
```

```bash
make run      # boot it (Ctrl-A X quits QEMU)
```

```bash
make test     # proofs, axiom check, boot, and a check of the transcript
```

To watch a boot from a browser, run `python3 tools/serve.py` and open
http://127.0.0.1:8796. Each press of Boot starts a real QEMU run on your machine and
streams its serial console to the page as it happens.

## How it fits together

| Path | What it is |
|---|---|
| `LeanOS/Kernel.lean` | The kernel's decisions: capabilities, mappings, system calls, scheduler. Compiled into the image. |
| `LeanOS/Proofs.lean` | The theorems about `Kernel.lean`. |
| `rt/runtime.c` | The bare-metal slice of Lean's runtime: allocator, reference counts, closures. |
| `arch/boot.S` | Entry, exception vectors, entering and leaving user mode. |
| `arch/kmain.c` | Boot, MMU, interrupt controller, timer; carries out what the Lean kernel returns. |
| `user/` | The three demo programs. |
| `test/` | The boot transcript check and the axiom check. |
| `tools/serve.py` | The browser console: runs QEMU and streams its serial output. |

A trap works like this: the machine layer saves the task's registers and passes the Lean
kernel its state and the call's arguments. Lean returns a new state and a small list of
things to do: set these return registers, print this range, rebuild this task's page
tables, run that task next. The machine layer does exactly that and returns to user mode.

The kernel image is about 60 KB of code. `Kernel.lean` is a `prelude` module that imports
only `Init.Core`, so only six small standard-library modules are compiled in.

## System calls

| # | Call | Result |
|---|---|---|
| 0 | `write(va, len)` | prints up to 256 bytes of the task's own readable memory |
| 1 | `yield()` | lets the next live task run |
| 2 | `map(cap, page)` | maps a capability's frame at a page of the user window |
| 3 | `unmap(page)` | removes a mapping |
| 4 | `derive(cap, rights)` | a new capability to the same frame with at most those rights |
| 5 | `exit()` | stops the task |
| 6 | `capinfo(cap)` | the rights a capability carries |
| 7 | `whoami()` | the task's number |
