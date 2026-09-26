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
`raspi4b` machine; the first boot on a real board is next. The Pi 5 comes later: its peripherals sit behind
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
fixed by the boot manifest; creating and passing endpoints waits for stage 6.) A GUI needs this: clients talk to
the display server over IPC and hand it the memory they draw into.

Done later: fair receive. A receive took the lowest-numbered task waiting to send, so
programs in low slots that kept a server busy could starve one in a higher slot: two `files`
programs from the card in slots 10 and 11 kept a third in slot 12 from finishing a single
file round, and five busy programs kept a sixth in slot 15 from the display (the Apps
launcher, task 16, would wait the same way). Now each endpoint remembers the task whose
message it took last (`served`, one entry for each of the three endpoints), and a receive
looks for a waiting sender from the task after it on, wrapping around, as the scheduler
does. A send that finds its receiver already waiting moves nothing: the receiver waits only
when nobody waits to send, so nobody is passed over. Proved, in `LeanOS/Fair.lean`: a
receive takes the first waiting sender in that order (`recv_in_turn`) and misses nobody
(`recv_misses_nobody`), nothing else moves what an endpoint remembers
(`served_only_by_recv`), and while a task stays blocked sending, its endpoint takes fewer
than 18 messages (`recv_bounded_wait`). Six new mutants are caught: a search from task 0
again, from the task served last instead of the one after, one task short, or skipping every
other task; a receive that forgets whom it served, or remembers it for the wrong endpoint.
`test/fair.sh` runs both cases. With the old kernel, slot 12 did no file round in 117 s
while slot 10 did 3,100, and slot 15 not 16 busy rounds in 39 s while slot 10 did 672; now
slot 12 does its first 4 file rounds while slot 10 does 4, and slot 15 its first 16 busy
rounds while slot 10 does 16.

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
only ever come from memory it was granted. Keyboard and mouse input: the UART first, then
USB. USB, part 1, done: a user-space driver (slot 17) for the Pi 4's DWC2 (the USB-C port;
what QEMU emulates), with hubs and boot-protocol keyboards and mice. It reaches the
controller only through `usb`, and the kernel checks each DMA transfer against the
driver's own frames: `usb_dma_own_memory` proves the controller never touches anyone
else's memory, with no IOMMU. Part 2, next: the USB-A ports, which are a VL805 xHCI
controller behind the BCM2711's PCIe bridge (no QEMU model: only testable on a Pi). xHCI
reads rings of descriptors from memory, so its DMA needs a different check: the rings kept
in memory only the kernel writes, or a bounce buffer.

Drawing speed (the display server logs it on every boot, and `make test` checks a drag
frame stays under 20 ms). Measured under QEMU on the development Mac, one window open:

| | before | after |
|---|---|---|
| a full redraw of the screen | ~50 ms | ~11 ms |
| a click on a window | ~50 ms (a full redraw) | ~4 ms |
| one frame of a window drag | ~35 ms | ~4.5 ms |

What changed: blending with two multiplies on packed channels instead of three divides;
rounded rectangles that walk only the clipped part; shadows drawn in one pass from a
distance table, skipping everything the window will cover; a background that precomputes
its glow per column and looks at the dot grid only on rows that have dots; and a click that
redraws the two windows whose look changed instead of the whole screen. The output matches
the old drawing to within rounding (at most 5 of 255 on a channel, in the shadows).

Done for speed: the display never reads the screen. A real Pi 4 maps the framebuffer
uncached, and blending (shadows, anti-aliased corners and text, the menu bar's and the
dock's glass) read back every pixel it changed. A cached back buffer of the whole screen
(2.4 MB) would not fit the display's 1 MiB; a band does. The display now composites each
rectangle it redraws a band of rows at a time (32 rows of the full width, more of a
narrower rectangle) in 128 KiB of its own memory, pages 168 to 199 of its spare run,
between its assets and its window table, and copies each finished band out row after row
in 16-byte stores. The screens are the same, pixel for pixel: 26 screens compared before
and after (the boot checks, the desktop, drags, off the screen's edges too, menus,
minimize, zoom, the dock's labels, a new background, the shutdown screen), identical but
for the boot screen's hash of the display's own code. Counted with Notes' window open:

| | screen reads before | after | screen writes before | after |
|---|---|---|---|---|
| a full redraw | 118,956 | 0 | 806,882 | 614,400 |
| a click on a window | 49,840 | 0 | 235,749 | 112,516 |
| one frame of a window drag | 15,968 | 0 | 172,992 | 84,115 |

Each pixel is now written once, in order (a full redraw is 153,600 stores). Under QEMU,
where the framebuffer is ordinary memory, the copying costs about a tenth of the drawing
time; a shadow's table made once per radius, one multiply per background pixel instead of
two, and the dock asking the kernel which apps run once per rectangle instead of once per
band more than pay for it. Alternating the old display and the new, a full redraw takes
about 6 ms instead of 7, a click 1.7 ms instead of 2.4, and a drag frame 1.4 ms instead of
2.1 (host timings vary; counted in instructions, 6 to 9% fewer).

Next for speed: measure it on a Pi 4. And a window its program redraws is composited
whole, with its shadow, however little of it changed.

Fixed: the desktop froze with 8 windows waiting. The display holds each waiting window's
call until it has an event, and the kernel gives a task 8 reply slots for its 12 windows.
With 8 held, the next call (Notes asking for a window, from the dock) made every receive
fail as full; the display retried for ever and no key or click reached anyone. It now holds
at most 7, so a call always finds a slot free: past that, the window that has waited
longest is answered with no event and its program asks again a moment later (`app_wait`,
every 100 ms), answered at once while the slots stay taken. `test/freeze.sh` opens Notes
with 8 windows waiting and then shows all 12 (11 waiting), checks keys and clicks still
reach the apps, and that nothing spins; with the old display it freezes.

Fixed: a slot started again while the display still knew its last run. Starting a slot
frees the reply slots held for the last run and takes back the pixels it lent; the display
forgot a stopped program's window only after the next message, so a program that stopped
by itself while Terminal was loading another kept its window: the new program's wait was
held on the dead window, and the display stopped when it drew the old pixels. Now the
display forgets stopped programs' windows before it answers any call, and Terminal and Apps
call it just before they start a slot. Should a start still get past it, a call arriving
in a reply slot it thought it held, or fewer capabilities than it counts, shows the display
what it missed, and it forgets that run unanswered and undrawn. `test/restart.sh` kills a
waiting program and runs another in its slot, then has one stop by itself inside Terminal's
load, and checks each program gets only its own keys and clicks.

## 8. A bounded kernel

Prove how much kernel memory each operation can use, and preallocate per task, so no
system call can exhaust the kernel heap. Replace list-based state where it grows with
the system.

Done: the kernel stack. The Lean kernel recursed once per list element, and a task can hold
8192 mappings, so each core had a 2 MiB stack; stage 6 found this the hard way, when
revocation walked the display server's 900 mappings and overran the old 64 KiB stack. Now
every walk over a task's mappings or capabilities (`dropRange`, `runMaps`, `app`, `snoc`,
`len`, `removeNth`, `keepBacked`, `dropCaps`, `dropMaps`) has a twin in `Kernel.lean` that
carries its result so far and calls itself only last, which Lean compiles to a loop, and a
`@[csimp]` theorem proves the two equal, so the compiler runs the loop while every proof
stays about the original definition. What recursion is left walks short lists: the 18
tasks, a task's reply slots, the pending interrupt lines. `test/stack.sh` has a program map
all 8192 pages of its window and makes the kernel walk them end to end: the stack's peak
went from 918,384 bytes to 2,128. Each core's stack is 64 KiB again, still painted and
checked on every return to user mode, and the 7.75 MiB this frees went to the kernel heap.

Done: the stack's bound, from the code. `tools/stackcheck.py` computes how deep each kernel
stack can go, and `make test` fails if that is over half the stack (`test/stackcheck.sh`).
Each C file of the kernel is compiled again with `-fstack-usage` and the shipped flags, so
clang reports every function's frame; the tool checks the code is the shipped code, reads
the calls from the linked image, and walks the graph from `kmain`, `secondary_main` and
`trap` (below the 288-byte register frame of an exception). Every recursion it finds must
be in its table with a bound (the task list, 19 calls deep with the empty tail, for
`revokeAll`, `wakeSleepers`, `setNth` and `mkTasksFrom`; a task's reply slots, 9, for
`placeCaller` and `forgetCaller`; the pending lines, 3, for `dropLine`), from
`state_bounded` and `task_bounded`. Indirect calls are traced to the addresses loaded
before them: the runtime's one-time initializers at each of their calls, and `trap`'s
conversion of message words; a call through a pointer from memory, a jump that is not a
jump table, or a frame of variable size fails. The worst case is 5,824 bytes: 2,912 for
the deepest system call (`start` taking back a slot's memory from every task), and a kernel
exception on top of it. That is 2.7 times the deepest measured (2,144) and under a tenth
of the 64 KiB stack. It rests on clang's frame sizes (checked against each function's
own stack adjustments), on the call graph read from the image, and on each walk running
over the list its bound is about, which is read from the code, not proved (TRUST.md).

Done: the kernel's state is bounded (`LeanOS/Bounds.lean`). No sequence of system calls,
with any arguments, makes a list in the state grow past a fixed length. In every reachable
state every task holds at most 64 capabilities, 8192 mappings, 8 reply slots and 7 result
registers (`task_bounded`). The mappings needed a new invariant: no two of a task's
mappings are for the same virtual page. `map` keeps it by dropping the old mappings of the
range before it adds the new run, `start` resets a slot to its manifest's pages, and
everything else only removes mappings; with every mapping in the 8192-page window
(`maps_in_range`), there can be no more than 8192. With the machine layer's inputs as they
are (a measurement is the eight words of a SHA-256, and only the manifest's two interrupt
lines fire), the rest is bounded too: 18 tasks, at most one pending entry per interrupt
line, eight words per measurement, eight USB channel shadows of each kind, three other
cores, and (since fair receive, stage 3) one last-served task per endpoint (`state_bounded`).
In all, the state is at most 447,559 heap objects
(`stateSize_le`), which under the runtime's object layout is at most 22.8 MiB of the
60.8 MiB kernel heap (TRUST.md has the arithmetic, and what it trusts). Five new mutants
break a bound (a `map` that keeps the old mappings of the pages it maps, a `derive` or a
grant past 64 capabilities, a call past 8 reply slots, an interrupt queued twice), and the
proofs reject each. Before, no proof caught the `derive`, the grant or the call, and the
other two only broke a proof script, not a stated theorem.

What is proved is the live state between two kernel entries. Next here: the memory a
step uses while it computes the next state, which may briefly hold an old and a new copy
of what it changes (argued in TRUST.md, not proved); that the runtime frees garbage as
soon as nothing holds it (its reference counting, trusted); and preallocating each
task's share when it starts.

Done too: page tables in one pass. The machine layer asked Lean for a task's 8192 level-3
words one at a time (`l3Word`), and each answer walked the task's mappings from the start,
so one task's tables took 8192 walks, and starting any program rebuilt the tables of all
18 tasks. Now one call returns the whole table (`l3Table`): 8192 zeros, then each mapping's
word at its page, the mappings taken last to first so the first mapping of a page is the
one that stays. `l3Table_spec` proves every word equal to `l3Word`'s, so every theorem in
`Tables.lean` holds for what the MMU reads (`Stored.installed`), and three new mutants (the
last mapping kept, a word one entry along, page 0 where nothing is mapped) are caught.
Measured under QEMU on the development Mac, with the kernel's own counter (the last two
rows by the host's clock):

| | before | after |
|---|---|---|
| starting an app (the tables of all 18 tasks) | 144 to 330 ms | 3 to 9 ms |
| the same, with a task holding all 8192 mappings | 832 ms | 10 ms |
| the tables of that task alone | 624 ms | 5.6 ms |
| every table built from boot to the desktop (88) | 1.14 s | 21 ms |
| `deep` mapping its window (38 calls, each a rebuild) | 6 s | 0.12 s |
| `test/stack.sh`, `test/apps.sh`, start to end | 14 s, 32 s | 4 s, 24 s |

Starting a program still rebuilds every task's tables, not only those of the tasks that
lost a mapping: the kernel does not say which did, and it now takes a few milliseconds.

Done too: the trusted base at its limits. `test/chaos.sh` runs one program from the card
(`user/progs/chaos.c`) under seven names into all six open slots, again and again: every
per-task limit at once (64 capabilities and 8192 mappings each, more windows waiting on
the display than it has reply slots), every way a program ends (it exits, it faults, `kill` while it waits on the
display, in the middle of a round, asleep), thirty restarts of one slot beside five stopped
programs that still hold 8192 mappings each, windows until the display refuses one, four
busy programs on the four cores, and grants nobody asked for. The machine layer reports the
kernel heap after every start, and with the same programs in the same slots that number is
the same to the byte after all thirty restarts, and at the end back at its baseline but for
192 bytes: the display's list of reply slots, grown once to its bound of 8 (the peak:
5.8 MB). Nothing in the runtime or the machine layer gave way. The file server did: it kept a
capability granted by a plain send, which it does not answer, and 58 of them left no room
for the one every file request carries, so no file could be read or written again until a
restart. It lets go of them now.

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
caller has mapped with the right permission.

Done too: a real file system on the card (`user/fs.c`, and `tools/mksd.py` writes the same
format): a superblock, a write-ahead journal, a bitmap of 4 KiB clusters, inodes with
direct, indirect and double-indirect clusters, and folders. Every change is one
transaction (journal, checksummed commit, then home), replayed or dropped at start; the
tree is checked and repaired at every start; files are read and written at any offset, so
a file can be as large as the card (512 MiB for now) and a program as large as its code run
(`user/elfload.h` loads it piece by piece). Terminal has folders (`mkdir`, `cd`, `pwd`,
`mv`), and Files opens them. `test/crash.sh` cuts the power in the middle of writes twelve
times; `test/bigprog.sh` runs a 41 KiB program and reads back a 250 KiB file. And the
journal's protocol is modeled in Lean (`LeanOS/JournalModel.lean`) with the proof that a
cut after any number of block writes, then recovery, gives the state before or after the
change (`crash_atomic`); four mutants of the model are caught.

Done too: files for programs from the card. The open slots hold the file server's endpoint,
each with its own badge (`file_server_knows_the_sender`), and the file server lets a program
reach only its own folder, `apps/NAME`, and what Terminal, Files or Apps gave it
(`run edit notes.txt`). The tour's first page asks for your note and is refused. `edit`, a
text editor on the card, edits what it was given and saves by itself.

Done too: the network, over a USB network adapter (CDC Ethernet; QEMU's `usb-net`, or a
real adapter on the Pi 4's USB-C port). The USB driver serves it on endpoint 2 with a
small stack (ARP, IPv4, ICMP, UDP, DHCP, DNS, a TCP client, HTTP/1.0 GET); Terminal has
`ip`, `ping` and `get`. For it the kernel gained `recvt` (receive with a deadline; the tick
theorem now covers receivers that time out), the DMA check takes only the driver's own
frames, and the grant-edge proofs carry a third server. Next here: TCP that takes data out
of order, a listening socket, and the Pi 4's own Ethernet (GENET).

Done too: stopping a program that does not answer. `stop` (26), through a launch
capability, marks the slot's program stopped; `sysStop_only` and `only_launchers_stop` say
it reaches only the named program and only from the tasks that may start it. Terminal has
`kill SLOT`; the display server takes the window back.

Done too: the network for programs from the card, by consent, and a browser. Every open
slot holds a send capability to the network service (the grant-edge proofs now list them);
the USB driver answers a slot only if Terminal allowed the program there with `run -net`,
tied to the hash the kernel measured, so a different program in that slot is refused.
`web` is a text browser on the card (headings, lists, numbered links, no scripts).

Done too: the time of day. The kernel keeps when tick 0 was in Unix seconds (`wall`), set
only through a time capability the USB driver alone holds (`only_usb_driver_sets_time`); the
driver asks a time server over NTP after DHCP. Next here: NTP answers checked against more
than one server.

Done too: a time zone. Settings steps through the zones people live in, UTC-12 to UTC+14 with
the half and quarter hours (UTC-3:30, UTC+5:30, UTC+5:45), and tells the display server,
which takes a zone only from Settings' badge. The menu bar shows the date and time in it at
once, and Clock asks the display for it every second, over the endpoint every window already
has. No kernel change and no new capability: the display cannot write the card, so it asks
Apps, which can, to keep the zone in `timezone.txt`, as it already asks Apps to start the
dock's programs; at boot Apps reads it back and hands it to the display, which takes that
once. The time itself stays UTC, set only by the USB driver. `test/timezone.sh` checks what
the menu bar and Clock show against the time each read, across midnight, and after a restart.
The background is kept the same way now, with the zone, in `settings.txt`; a card with only
the older `timezone.txt` still gives its zone back, and the next save moves it over.

Done too: copy and paste, with one rule: text moves between programs only by the user's
hand. The display server keeps the clipboard, up to 4 KiB of text. Ctrl+C, or Copy in the
new Edit menu in the menu bar, asks the window in front for its text, as an event like a
key, and the display takes the answer only from that window's badge, once, and only within
2 seconds; a copy at any other time, from anyone, is refused. Ctrl+V, or Paste, hands the
text to the window in front, and to no other, as a run of events in its queue, 16 bytes
each. There is no request that reads the clipboard. Notes and `edit` copy their text and
paste where the caret is; Terminal copies the line being typed, or what the last command
printed, and pastes onto the command line, where nothing runs until Return. The USB
keyboard now sends Control keys as the serial line does, and the browser console sends
Ctrl+C and Ctrl+V. No kernel change and no new capability: the text travels in message
words over the endpoint every window already has, and nobody lends anybody memory for it.
The rule is the display server's C, trusted, not proved (TRUST.md). `test/clipboard.sh`
copies from Notes into Terminal and checks Terminal got exactly that text, then that
mallory's request for the clipboard and her unasked copy are refused, and so are the tour's,
once with nothing asked of it and once 2.5 seconds after the user pressed Ctrl+C in its
window.

Done too: a command line that edits as a shell's does. Terminal keeps the last 32 commands
for Up and Down (not empty lines, nor one repeated at once), and the line being typed comes
back after them; Left and Right move the cursor, and typing, Backspace and a paste go in
where it is. Tab completes a command's name, or a file or folder name from the file
server's listing, and a second Tab lists what matches. The browser console now sends Tab.
`test/term-history.sh` recalls, edits and runs commands and completes names.

Done too: touchscreens and tablets. The USB driver reads a HID device's report
descriptor when it does not speak the boot protocol, finds the absolute X and Y and the
button or tip switch, and scales them to the screen; a 7-inch 1024x600 HDMI touchscreen
matches the desktop exactly.

Done too: all four cores. Every core runs tasks; one at a time is in the Lean kernel,
under a lock the machine layer takes on the way in. On the way in it tells the kernel which
task this core runs and which the others run (`enter`), and the scheduler never picks one
another core is running (`schedule_not_on_other_core`). Core 0's timer advances the clock;
the others' timers only move their core on to the next task. An idle core sleeps in WFI
and is woken by an interrupt between cores when a task is ready that no core runs. Before
a slot is loaded, a core still running what was there is made to leave it. `make test`
checks that all four cores come up and run tasks.

Done later: a desktop that stays responsive under load. With five programs from the card
that only compute (a loop with no system calls, more programs than cores), every task on the
way from a key to the screen waited for a timer tick to give it a turn: the input driver
woke 5 to 15 ms after the UART's interrupt instead of 0.1 ms, and a key took 31 to 34 ms to
reach the screen instead of 2 (median, emulated time, QEMU on a 10-core Mac). Now the task an
interrupt wakes runs at once on the core that took it, and the one it took the core from runs
after it (`preempt`); a task a send, a call, a receive or a reply wakes runs next on that
core, when the caller stops (`wake`, `schedule`). The timer ignores that choice: every timer
interrupt, on every core, is round robin from the task it picked last (`rotate`, `turn`), a
place in the round a wake-up's pick never moves. Proved: a message wakes a task to run next
(`wake_runs_next`), the scheduler runs it first and only once (`schedule_prefers_woken`,
`schedule_spends_woken`), an interrupt runs its holder at once and never on a core that
already runs it (`irq_runs_holder`, `irq_not_on_other_core`), and, in `LeanOS/Fair.lean`,
nothing but a round robin pick moves the round (`turn_only_by_round_robin`), so while a task
stays ready and no core runs it, fewer than 18 timer interrupts happen (`timer_bounded_wait`):
tasks that keep waking each other cannot keep it waiting. Sixteen new mutants are caught.
Loaded, a key now takes 2.6 ms (up to 15 ms while the host itself is busy), the input driver
wakes in 0.1 ms, and `test/responsive.sh` types 96 keys at once, idle and beside five such
programs, counting the machine's own ticks: 15 against 12 now, 106 against 13 with the old
kernel, which it fails.

Done too: programs from the SD card. They are ELF files on the card (`tools/mksd.py`
writes a card with them, the way programs are copied onto any computer's disk); Terminal's
`run` reads one, checks and flattens it in user space, and starts it with `exec` in one of
two open slots. The manifest fixes what an open slot may hold (its own memory, a window),
not what code it runs, so a program nobody vetted is still confined by every theorem; the
kernel proves the image comes only from memory the loader can read. `ps` lists the slots.

And time: the kernel counts timer ticks, and `sleep(ms)` puts a task to sleep until its
tick comes (`tick_wakes_only_sleepers`). `clock`, on the card, keeps time with it, and asks
the display server for events without blocking (`POLL`) so its close button still works.

And power: the leanos menu (the logo in the menu bar) restarts the machine, through the
watchdog, or switches it off, with a power capability only the display server holds
(`only_display_powers`). Making that test pass found an input bug: after a restart a
leftover byte could sit in the UART with its interrupt already cleared, and block every
key and click after it; the input driver now drains the UART before it waits.

And a card a Pi 4 boots: `make pi-image` builds an image with a FAT boot partition (the
Pi's firmware, `config.txt`, `kernel8.img` built for hardware) and the data partition with
the programs; the machine layer keeps all block I/O inside the data partition, found in the
partition table, and routes the UART to the header pins itself. `make test` checks the FAT
file system is clean and that leanos, booted from the image, reads the data partition and
leaves the boot partition alone. It has not run on a Pi yet.

Ready for that first boot: the machine layer was gone over for what works on QEMU only
because QEMU is lenient, and fixed. `config.txt` now loads the kernel where it is linked
(the firmware's default for a 64-bit kernel is 0x200000, not 0x80000), skips the device
tree and ATAGs, fixes the UART's clock, and sets up the screen, each line explained. The
cores leave EL2 with every EL2 register EL1 relies on set, not left at reset values, and
cores 1-3 turn on their caches before touching their stacks. Every firmware answer is
checked and printed: the framebuffer's size, pitch, pixel order and alpha (one the display
cannot draw on stops the machine with the reason on the screen), the UART's clock, the
counter's rate, the ARM's RAM. The mailbox buffer has its cache lines to itself, the USB
controller's power domain is switched on, and the SD driver follows Linux's and Circle's
setup for EMMC2 (3.3 V I/O, 200 to 400 kHz to identify, 25 MHz after, waits bounded in
time), printing each step. `docs/SETUP.md` lists what a first boot prints at each step and
what to try where it stops.

More on the card: a guided tour (`tour` in Terminal) that really tries a desktop attack on
each page and compares the kernel's answer with a typical Linux desktop; `calc`, `snake`,
`life` and `tiles` (2048); and a user guide. Six open slots now, and the arrow keys reach
programs (the browser console sends them as a terminal would, ESC [ A to D).

Done too: the file server under a fuzzer. `test/fsfuzz.sh` runs `fsfuzz` from the open
slots: fixed requests at every limit and in every way a program might reach past its folder,
a card filled until the file server says full, and random requests checked against a model
of every file, from three programs at once, then a restart after which the card must check
clean and every file be as it was left. It found four bugs in `user/fs.c`, fixed and kept as
regressions: the check at start stopped 32 folders down and freed what was deeper, so after
a restart a name in one program's folder could reach a file made later in another's; a
cluster given out again in the request that freed it kept its old bytes; a full card refused
a rename or a delete that needed no room; and a program's folder that could not be made on a
full card left its inode taken. A change that fails no longer reads all the metadata back
from the card (13 to 17 ms, which any program could make the file server spend in a loop):
the file server keeps a copy of exactly what the card holds and copies that back, in about
45 microseconds, and the fuzzer times failed changes against stats of the same paths. And
the 48 records of what programs were given are 8 for each open slot, taken back when a
program is killed, so one `run` naming many files cannot leave a later program without its
folder (`test/grants.sh`). TRUST.md says what the file server is trusted to do and what the
fuzzer checks.

Done too: the display server under a fuzzer. `test/dfuzz.sh` runs `dfuzz` from the open
slots, two at once: fixed requests for every op and every limit, requests near the limits
checked against the display's rule, floods, random requests, windows until the table is
full; then programs killed while the display holds their call and in the middle, one that
exits and one that faults, with the kernel heap the same after each start; copy and paste
by hand past the clipboard's size, late and after the close button; and screenshots, where
the menu bar and the dock's icons must be untouched with every window up. It found five bugs
in `user/display.c`, fixed and kept as regressions: a window's grant longer than its slot
was mapped over the next window's (its pixels showed in another program's window), and an
icon's over the next icons'; refused windows and raises were logged every time, each line
holding the kernel; a tall window opened over the menu bar; and a narrow window drew its
buttons and title past its frame. A sixth, a program taking another's name through a
made-up icon (so the dock's Clock brought it forward instead of starting Clock), is fixed
too: the display takes a name only from four pages lent with the execute right, which are
only ever the program's own code run, and the loaders run no image that carries an icon
marker of its own (`test/spoof.sh`). TRUST.md says what the display is trusted to do and
what the fuzzer checks.

Done too: a program with several windows. The fuzzer's author found that WAIT and POLL
name no window, so a program heard only its first window's events, and a second window's
close button went nowhere. Now OPEN answers with the window's number, every event carries
it (a program with one window sees no difference), one waiting call hears all of a
program's windows, and CLOSE closes one of the caller's own windows at once. The dock and
RAISE bring all of a program's windows forward. `test/windows.sh` runs a program with three
windows through clicks, keys, copy and paste, both ways of closing one, and closing the
last; dfuzz asks CLOSE for numbers it does not hold and checks every number it is given.

Next: the first boot on real Pi 4 hardware (EMMC2, colors, timings), the USB-A ports
(xHCI on PCIe), the Pi 4's own Ethernet (GENET), a kernel lock finer than the whole kernel
(disk and USB transfers hold it today), and the Pi 5.
