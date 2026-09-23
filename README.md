# leanos

A kernel for the Raspberry Pi 4 whose decisions are written in Lean 4, compiled into the
kernel, and proved correct. It is on its way to being a full operating system with a
graphical interface; [ROADMAP.md](ROADMAP.md) has the plan.

The part that decides who may touch what is Lean code: capabilities, address spaces,
system calls and the scheduler. It is compiled to C and linked into the kernel image. The
theorems in `LeanOS/Proofs.lean` are about that same code, so there is no separate
specification that could drift from what runs. Underneath, about 1,250 lines of C and
assembly boot the board, write page tables and switch tasks, but make no access decisions.

Today it boots the Pi 4 (tested on QEMU's `raspi4b` machine) to a graphical desktop at
1024×600, set in Inter, over an indigo-to-teal dot pattern, with a dock of Fluent icons. You can type into a window and drag it around. A display server in user space
owns the screen; an input driver in user space owns the serial port and its interrupt;
alice's Notes app draws in her own memory and lends the display a read-only view of it.
mallory tries to reach the screen, the keyboard and everyone's memory, and cannot.

The dock starts apps: **Files** lists and shows what the file server holds, **Terminal**
answers from the kernel (`whoami`, `caps`, `boot`, `uptime`) and the file server (`ls`,
`cat`, `write`, `rm`), **Settings** changes the background, and **Security** shows every
program's boot check and what is proved. Notes saves its note to the file server, so it
is back when Notes starts again. An app is loaded and checked against the manifest each
time it starts; closing its window stops it, and starting it again first takes back
everything its last run shared. The file server keeps files on the SD card, so they are
still there after a restart, and holds a client's memory only while it answers that
client's request.

![The leanos boot screen](docs/logo.png)

![The leanos desktop with Notes, Terminal, Files and Security open, on the Graphite background](docs/screen.png)

The serial console of that boot, with `make test` typing "Hi!" and dragging the window:

```
leanos © 2026 Keith Adler
leanos: Raspberry Pi 4, booting on EL1
leanos: framebuffer 1024x600 at 0x3c100000
leanos: MMU on
leanos: SD card ready
leanos: Lean kernel initialized, 10 tasks
leanos: alice verified, sha256 0x9fffc938...
leanos: display verified, sha256 0x8383eed9...
leanos: mallory verified, sha256 0x2dbdf014...
leanos: carol verified, sha256 0x1c54ae17...
leanos: input verified, sha256 0x7b5792ff...
leanos: fs verified, sha256 0xb50707da...
alice: wrote secret 0x5ec12e7 to my data page
mallory: I am task 2
mallory: map capability 9 (not mine) at page 5 -> refused, no such capability
mallory: print 16 bytes of kernel memory at 0x80000 -> refused, not allowed
mallory: receive on the display's endpoint -> refused, not allowed
mallory: send the display a window of my pixels -> refused, not allowed
mallory: map the framebuffer (capability 5, which is the display's) -> refused, no such capability
mallory: map the endpoint as memory -> refused, not allowed
mallory: asked for every right on the endpoint, got send
mallory: read block 0 of the SD card through capability 20, which I do not have -> refused, no such capability
mallory: read block 0 of the SD card through my endpoint capability -> refused, not allowed
carol: asked for write+execute on my data frame, got -w-
carol: jumping into the instruction I wrote in my data page
leanos: carol stopped: instruction fetch not allowed at 0x80010000
input: listening on the UART
fs: made a new file system on the SD card; ready, 1 file
alice: no saved note yet
display: boot checks shown: 6 verified, 0 refused
display: boot logo drawn
display: desktop drawn on the 1024x600 framebuffer
display: alice opened a 300x200 window from a read-only capability to 59 pages
display: mallory asked for a window but sent no pixels; ignored
mallory: ask the display for a window without pixels -> ok
mallory: writing to the screen's physical address 0x3c100000 directly
leanos: mallory stopped: data access not allowed at 0x3c100000
alice: opened a 300x200 window, read-only, 59 pages -> ok
leanos: idle, 4 tasks waiting (100 system calls, 155 timer ticks, 0 device interrupts, kernel heap 148960 bytes live, 175584 peak, stack 66976 bytes peak)
display: key 'H' to alice
display: key 'i' to alice
display: key '!' to alice
display: moved alice's window to (276, 208)
```

And `make test` using the apps: typing into Notes, closing it and starting it again (the
note comes back from the file server), Terminal (`caps`, `boot`, `write`, `ls`), Settings,
closing Terminal and starting it again, Files, then Security. Keystrokes are left out.

```
display: closed alice's window
alice: window closed, exiting
leanos: alice started
leanos: alice verified, sha256 0x9fffc938...
alice: wrote secret 0x5ec12e7 to my data page
display: start Notes -> ok
alice: loaded notes.txt, 2 bytes
alice: opened a 300x200 window, read-only, 59 pages -> ok
leanos: terminal started
leanos: terminal verified, sha256 0xc817d2c5...
display: start Terminal -> ok
terminal: opened a window -> ok
terminal: caps -> 7 capabilities
terminal: boot -> 7 verified
terminal: write hello.txt -> ok
terminal: ls -> 3 files
leanos: settings started
leanos: settings verified, sha256 0xac41809c...
display: start Settings -> ok
settings: opened a window -> ok
display: background 1, as Settings asked
settings: background set to Graphite -> ok
display: closed Terminal's window
terminal: window closed, exiting
leanos: terminal started
leanos: terminal verified, sha256 0xc817d2c5...
display: start Terminal -> ok
terminal: opened a window -> ok
terminal: caps -> 7 capabilities
terminal: write fast.txt -> ok
terminal: cat fast.txt -> 36 bytes
leanos: files started
leanos: files verified, sha256 0x8e4f96ff...
display: start Files -> ok
files: listed 4 files
files: showing welcome.txt (169 bytes)
files: opened a window -> ok
files: listed 4 files
files: showing hello.txt (19 bytes)
leanos: security started
leanos: security verified, sha256 0x5de181c6...
display: start Security -> ok
security: opened a window -> ok
security: 10 verified, 0 refused, 0 not loaded
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
- **Only verified code runs**: every task starts unverified; the kernel lets it run only if
  the SHA-256 of what it was loaded with matches the boot manifest, and nothing can make a
  refused task run later. The boot screen shows each verdict. `make test` flips one bit of a
  program in the image and checks it is refused, at boot and when an app is started.
- **The disk belongs to the file server**: no other task can ever hold a capability to
  any block of the SD card. Block I/O touches only blocks the caller holds, with the right
  it needs, and only 512 bytes in one page the caller has mapped writable (for a read) or
  readable (for a write).
- **Memory moves at most one step**: from an app to the display server, or from a file
  server client to the file server. Every other task only ever reaches its own memory,
  and neither server can pass on what it was given. `drop` only ever takes authority away.
- **Starting an app takes back its memory**: only the display server can start programs,
  and only the apps. Before an app's slot is loaded again, no other task keeps a
  capability to its frames, a mapping of them, a waiting message that would grant one, or
  a reply meant for the old run.
- **Devices and interrupts stay with their owners**: only the display server can reach the
  screen, only the input driver the UART and its interrupt, and an interrupt wakes only a
  holder of its capability.

And down to the hardware: Lean computes every page-table word, and a model of the Armv8-A
MMU proves that user mode reaches exactly its own mappings, only the frame pool and the
framebuffer (never the kernel or the peripherals), and shares a physical page with another
task only along a grant path. `make mutants` breaks the kernel in 52 ways and checks the
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
make run      # boot it on QEMU's Pi 4, headless, with build/sd.img as its SD card
```

```bash
make test     # proofs, axiom check, boot, the apps, the transcript, the pixels on screen, and tampered images
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
| `user/` | The display server, the input driver, the file server (`fs.c`), the apps (alice's Notes, Terminal, Settings, Security, Files), and the test tasks mallory and carol; `gfx.h` draws, `assets.h` reads fonts and icons, `app.h` and `fs.h` are the client sides of the window and file protocols. |
| `test/` | The boot check (transcript and screen), the apps, tampering, the axiom check, and the mutants. |
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
| 14 | `bootinfo(task)` | whether that task's code matched the boot manifest, the start of its hash, and whether it is running |
| 15 | `start(cap)` | starts the program slot a launch capability names, if it is not running: takes back what its last run shared, then has it loaded and checked |
| 16 | `drop(cap)` | lets go of a capability, and of every page seen only through it; later capabilities move down one place |
| 17 | `blockread(cap, index, va)` | reads one 512-byte block of the SD card, from a block capability, into the task's own writable memory |
| 18 | `blockwrite(cap, index, va)` | writes 512 bytes of the task's own readable memory to one block |

Capabilities come in four kinds. Frame capabilities name a run of physical frames and carry read, write and execute rights.
Each task starts with 256 frames (16 code, 8 data, 4 stack and 228 spare pages) and a 32 MiB
window to map them in. Endpoint capabilities carry
receive, send and grant rights, and a badge the kernel delivers with every message.
Interrupt capabilities name an interrupt line, launch capabilities a program slot, and
block capabilities a run of the SD card's blocks; like endpoints, they are fixed by the
boot manifest.

## License

MIT, © 2026 Keith Adler. See [LICENSE](LICENSE). The fonts and icons keep their own licenses (OFL, MIT), listed in [THIRD_PARTY.md](THIRD_PARTY.md); nothing GPL-licensed goes into the system image.
