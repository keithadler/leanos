# leanos

A kernel for the Raspberry Pi 4 whose decisions are written in Lean 4, compiled into the
kernel, and proved correct. It is on its way to being a full operating system with a
graphical interface; [ROADMAP.md](ROADMAP.md) has the plan.

The part that decides who may touch what is Lean code: capabilities, address spaces,
system calls and the scheduler. It is compiled to C and linked into the kernel image. The
theorems in `LeanOS/Proofs.lean` are about that same code, so there is no separate
specification that could drift from what runs. Underneath, about 1,000 lines of C and
assembly boot the board, write page tables and switch tasks, but make no access decisions.

Today it boots the Pi 4 (tested on QEMU's `raspi4b` machine) to a graphical desktop at
1024×600, set in Inter, over an indigo-to-teal dot pattern, with a dock of Fluent icons. You can type into a window and drag it around. A display server in user space
owns the screen; an input driver in user space owns the serial port and its interrupt;
alice's Notes app draws in her own memory and lends the display a read-only view of it.
mallory tries to reach the screen, the keyboard and everyone's memory, and cannot.

![The leanos boot screen](docs/logo.png)

![The leanos desktop after typing into Notes and dragging it](docs/screen.png)

The serial console of that boot, with `make test` typing "Hi!" and dragging the window:

```
leanos © 2026 Keith Adler
leanos: Raspberry Pi 4, booting on EL1
leanos: framebuffer 1024x600 at 0x3c100000
leanos: MMU on
leanos: Lean kernel initialized, 5 tasks
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
input: listening on the UART
display: boot logo drawn
display: desktop drawn on the 1024x600 framebuffer
display: alice opened a 300x200 window from a read-only capability to 59 pages
display: mallory asked for a window but sent no pixels; ignored
mallory: ask the display for a window without pixels -> ok
mallory: writing to the screen's physical address 0x3c100000 directly
leanos: mallory stopped: data access not allowed at 0x3c100000
alice: opened a 300x200 window, read-only, 59 pages -> ok
leanos: idle, 3 tasks waiting (47 system calls, 170 timer ticks, 0 device interrupts, kernel heap 109744 bytes live, 136368 peak)
display: key 'H' to alice
display: key 'i' to alice
display: key '!' to alice
display: moved alice's window to (276, 208)
```

alice, mallory and carol are test personas: a legitimate app, an attacker, and a program
trying to run code it wrote. They exercise the protections; [ROADMAP.md](ROADMAP.md)
replaces the fixed demo with an init task and real apps.

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
- **Replies grant nothing** and wake only the task waiting for them.
- **Devices and interrupts stay with their owners**: only the display server can reach the
  screen, only the input driver the UART and its interrupt, and an interrupt wakes only a
  holder of its capability.

And down to the hardware: Lean computes every page-table word, and a model of the Armv8-A
MMU proves that user mode reaches exactly its own mappings, only the frame pool and the
framebuffer (never the kernel or the peripherals), and shares a physical page with another
task only along a grant path. `make mutants` breaks the kernel in 31 ways and checks the
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
make run      # boot it on QEMU's Pi 4, headless: serial here, screen in the browser console
```

```bash
make test     # proofs, axiom check, boot, the transcript, and the pixels on screen
```

To run it in a browser, start `python3 tools/serve.py` and open http://127.0.0.1:8796.
Boot starts QEMU's Pi 4 with no window of its own; the page shows its screen live (through
noVNC, over a localhost-only WebSocket) and streams the serial console alongside. Click the
screen to type or drag windows: the page sends keys and mouse over the Pi's serial line,
where leanos's input driver reads them (QEMU's Pi 4 has no USB).

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
| `user/` | The display server, the input driver, alice's Notes, and the test tasks mallory and carol; `gfx.h` draws, `font5x7.txt` is the font. |
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
| 9 | `recv(cap)` | receives the badge, three words, any granted capability and, for a call, a reply slot; waits for a sender |
| 10 | `call(cap, w0, w1, w2, grant)` | like send, then waits for the receiver's reply |
| 11 | `reply(slot, w0, w1, w2)` | answers a caller; carries no capability and never blocks |
| 12 | `irqwait(cap)` | waits for the interrupt an interrupt capability names |
| 13 | `irqack(cap)` | lets that interrupt fire again |

Capabilities come in three kinds. Frame capabilities name a run of physical frames and carry read, write and execute rights.
Each task starts with 64 frames (code, data, stack and 28 spare pages) and a 32 MiB
window to map them in. Endpoint capabilities carry
receive, send and grant rights, and a badge the kernel delivers with every message.
Interrupt capabilities name an interrupt line; like endpoints, they are fixed by the boot
manifest.

## License

MIT, © 2026 Keith Adler. See [LICENSE](LICENSE). The font and icons keep their own licenses (OFL, MIT), listed in [THIRD_PARTY.md](THIRD_PARTY.md); nothing GPL-licensed goes into the system image.
