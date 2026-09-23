# leanos

A kernel for the Raspberry Pi 4 whose decisions are written in Lean 4, compiled into the
kernel, and proved correct. It is on its way to being a full operating system with a
graphical interface; [ROADMAP.md](ROADMAP.md) has the plan.

The part that decides who may touch what is Lean code: capabilities, address spaces,
system calls and the scheduler. It is compiled to C and linked into the kernel image. The
theorems in `LeanOS/Proofs.lean` are about that same code, so there is no separate
specification that could drift from what runs. Underneath, about 1,000 lines of C and
assembly boot the board, write page tables and switch tasks, but make no access decisions.

Today it boots the Pi 4 (tested on QEMU's `raspi4b` machine) into a small graphical
desktop. A display server owns the framebuffer; alice draws a window in her own memory
and hands the server a read-only capability to exactly those pages; mallory tries to reach
the screen and everyone else's memory, and cannot.

![The leanos desktop on QEMU's Raspberry Pi 4](docs/screen.png)

The serial console of the same boot:

```
leanos: Raspberry Pi 4, booting on EL1
leanos: framebuffer 640x480 at 0x3c100000
leanos: MMU on
leanos: Lean kernel initialized, 4 tasks
alice: wrote secret 0x5ec12e7 to my data page
mallory: I am task 2
mallory: map capability 9 (not mine) at page 5 -> refused, no such capability
mallory: print 16 bytes of kernel memory at 0x80000 -> refused, not allowed
mallory: receive on the display's endpoint -> refused, not allowed
mallory: send the display a window of my pixels -> refused, not allowed
mallory: map the framebuffer (capability 5, which is the display's) -> refused, no such capability
mallory: map the endpoint as memory -> refused, not allowed
mallory: asked for every right on the endpoint, got send
carol: asked for write+execute on my data frame, got -w-
carol: jumping into the instruction I wrote in my data page
leanos: carol stopped: instruction fetch not allowed at 0x80010000
display: desktop drawn on the 640x480 framebuffer
alice: sent the display a 240x100 window, read-only, 24 pages -> ok
alice: secret intact, exiting
display: alice's window, 240x100 from a read-only capability to 24 pages, drawn at (60, 70)
display: mallory asked for a window but sent no pixels; ignored
mallory: ask the display for a window without pixels -> ok
mallory: writing to the screen's physical address 0x3c100000 directly
leanos: mallory stopped: data access not allowed at 0x3c100000
leanos: idle, 1 task waiting for a message (40 system calls, 2 timer ticks, kernel heap 49296 bytes live, 60160 peak)
```

The kernel stamps every message with the sender's badge, so mallory cannot pass for
alice. Her direct write to the screen's physical address faults, and the pixel she aimed
at still shows the menu bar. `make test` checks that pixel.

## What is proved

The boot manifest fixes which task can pass memory to which. For every state the kernel
can reach, under any sequence of system calls with any arguments:

- **Authority flow**: a task holds a frame only if a chain of grants from its original
  owner could have given it, never with more rights. For the demo: mallory and carol can
  never hold anyone's memory but their own; alice can share with the display server and
  nobody else; only the display server can ever reach the framebuffer.
- **No forged identity**: endpoint rights never grow and badges never change.
- **W^X**: no page is ever both writable and executable.
- **Every mapping is backed** by a capability the task holds, with the same rights.
- **`write` reads only memory the task may read.**
- **The scheduler never runs a waiting or stopped task** while a ready one exists.

And down to the hardware: Lean computes every page-table word, and a model of the Armv8-A
MMU proves that user mode reaches exactly its own mappings, only the frame pool and the
framebuffer (never the kernel or the peripherals), and shares a physical page with another
task only along a grant path. `make mutants` breaks the kernel in 24 ways and checks the
proofs catch each one.

[TRUST.md](TRUST.md) lists exactly what the proofs cover and what is taken on trust (the
Lean compiler, the runtime shim, the machine layer, the MMU model, the hardware).

## Build and run

You need Lean via `elan` (the version in `lean-toolchain` is picked up automatically),
Homebrew's `llvm` and `lld` for the cross compiler and linker, and `qemu`.

```bash
make          # build build/kernel8.img and check every proof
```

```bash
make run      # boot it on QEMU's Pi 4 in a window (close it to quit)
```

```bash
make test     # proofs, axiom check, boot, the transcript, and the pixels on screen
```

To watch a boot from a browser, run `python3 tools/serve.py` and open
http://127.0.0.1:8796. Each press of Boot starts a real QEMU run on your machine, streams
its serial console as it happens, and shows the screen when the system settles.

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
| `user/` | The demo programs: the display server, alice, mallory, carol; `gfx.h` draws, `font5x7.txt` is the font. |
| `test/` | The boot check (transcript and screen), the axiom check, and the mutants. |
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
| 2 | `map(cap, page)` | maps a capability's run of frames at consecutive pages of the user window |
| 3 | `unmap(page, count)` | removes mappings |
| 4 | `derive(cap, rights, offset, count)` | a new capability with at most those rights, to the same endpoint or to a piece of the same run of frames |
| 5 | `exit()` | stops the task |
| 6 | `capinfo(cap)` | the rights a capability carries, whether it names frames or an endpoint, and how many frames |
| 7 | `whoami()` | the task's number |
| 8 | `send(cap, w0, w1, w2, grant)` | sends three words, and optionally a frame capability, through an endpoint; waits for a receiver |
| 9 | `recv(cap)` | receives the badge, three words and any granted capability; waits for a sender |

Frame capabilities name a run of physical frames and carry read, write and execute rights.
Each task starts with 64 frames (code, data, stack and 28 spare pages) and a 32 MiB
window to map them in. Endpoint capabilities carry
receive, send and grant rights, and a badge the kernel delivers with every message.
