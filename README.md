# leanos

A kernel for the Raspberry Pi 4 whose decisions are written in Lean 4, compiled into the
kernel, and proved correct. It is on its way to being a full operating system with a
graphical interface; [ROADMAP.md](ROADMAP.md) has the plan.

The part that decides who may touch what is Lean code: capabilities, address spaces,
system calls and the scheduler. It is compiled to C and linked into the kernel image. The
theorems in `LeanOS/Proofs.lean` are about that same code, so there is no separate
specification that could drift from what runs. Underneath, about 1,000 lines of C and
assembly boot the board, write page tables and switch tasks, but make no access decisions.

Today it boots the Pi 4 (tested on QEMU's `raspi4b` machine) and runs four user tasks,
preempted by the timer, each in its own address space, passing messages through the
kernel.

```
leanos: Raspberry Pi 4, booting on EL1
leanos: MMU on
leanos: Lean kernel initialized, 4 tasks
alice: wrote secret 0x5ec12e7 to my data page
server: waiting for messages
server: from badge 1: 44 0 0, with a frame capability (r--); mapped at page 8, it says: a page alice drew into and shared, read-only
mallory: I am task 2
mallory: map capability 9 (not mine) at page 5 -> refused, no such capability
mallory: print 16 bytes of kernel memory at 0x80000 -> refused, not allowed
mallory: receive on the server's endpoint -> refused, not allowed
mallory: grant my data page to the server -> refused, not allowed
mallory: map the endpoint as memory -> refused, not allowed
mallory: asked for every right on the endpoint, got send
mallory: send 666 to the server -> ok
mallory: reading page 2 directly, which nobody mapped for me
leanos: mallory stopped: data access not allowed at 0x80002000
carol: asked for write+execute on my data frame, got -w-
carol: jumping into the instruction I wrote in my data page
leanos: carol stopped: instruction fetch not allowed at 0x80001000
alice: granted the server read-only capability 5 to my page 2 -> ok
server: from badge 2: 666 0 0
alice: sent the words 7 8 9 -> ok
server: from badge 1: 7 8 9
server: done
alice: secret intact, exiting
leanos: every task has finished (45 system calls, 2 timer ticks, kernel heap 8400 bytes live, 8704 peak)
```

alice draws into a page and grants the server read-only access to it, the way a GUI client
will hand the display server a buffer. mallory may talk to the server but has no right to
receive, grant or read anyone's memory, and the kernel stamps her messages with her badge,
so she cannot pass for alice.

## What is proved

The boot manifest fixes which task can pass memory to which. For every state the kernel
can reach, under any sequence of system calls with any arguments:

- **Authority flow**: a task holds a frame only if a chain of grants from its original
  owner could have given it, never with more rights. For the demo: mallory and carol can
  never hold anyone's memory but their own; alice can share with the server and nobody
  else.
- **No forged identity**: endpoint rights never grow and badges never change.
- **W^X**: no page is ever both writable and executable.
- **Every mapping is backed** by a capability the task holds, with the same rights.
- **`write` reads only memory the task may read.**
- **The scheduler never runs a waiting or stopped task** while a ready one exists.

And down to the hardware: Lean computes every page-table word, and a model of the Armv8-A
MMU proves that user mode reaches exactly its own mappings, nothing of the kernel or the
peripherals, and shares a physical page with another task only along a grant path.
`make mutants` breaks the kernel in 17 ways and checks the proofs catch each one.

[TRUST.md](TRUST.md) lists exactly what the proofs cover and what is taken on trust (the
Lean compiler, the runtime shim, the machine layer, the MMU model, the hardware).

## Build and run

You need Lean via `elan` (the version in `lean-toolchain` is picked up automatically),
Homebrew's `llvm` and `lld` for the cross compiler and linker, and `qemu`.

```bash
make          # build build/kernel8.img and check every proof
```

```bash
make run      # boot it on QEMU's Pi 4 (Ctrl-A X quits)
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
| `LeanOS/Arm.lean` | A model of the MMU's translation walk, as user mode sees it (trusted). |
| `LeanOS/Tables.lean` | The proof that the page-table words give user mode exactly its mappings. |
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
| 1 | `yield()` | lets the next ready task run |
| 2 | `map(cap, page)` | maps a frame capability at a page of the user window |
| 3 | `unmap(page)` | removes a mapping |
| 4 | `derive(cap, rights)` | a new capability to the same object with at most those rights |
| 5 | `exit()` | stops the task |
| 6 | `capinfo(cap)` | the rights a capability carries, and whether it is a frame or an endpoint |
| 7 | `whoami()` | the task's number |
| 8 | `send(cap, w0, w1, w2, grant)` | sends three words, and optionally a frame capability, through an endpoint; waits for a receiver |
| 9 | `recv(cap)` | receives the badge, three words and any granted capability; waits for a sender |

Frame capabilities carry read, write and execute rights. Endpoint capabilities carry
receive, send and grant rights, and a badge the kernel delivers with every message.
