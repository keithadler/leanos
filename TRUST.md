# What is proved, and what is trusted

leanos splits the kernel in two:

- **`LeanOS/Kernel.lean` makes every decision.** It decides which task holds which
  capability, what each task can see at each virtual page, whether a system call succeeds,
  and which task runs next. This code is compiled into the kernel image, and
  `LeanOS/Proofs.lean` proves theorems about it.
- **The machine layer (`arch/`, `rt/`) carries decisions out.** It writes page tables,
  saves and restores registers, prints bytes, and supplies the runtime compiled Lean code
  needs. Its rule is that no check it makes may change an outcome. The checks it does have
  are there only to stop the machine if the two halves ever disagree.

## Proved

These hold for every state the kernel can reach: `init`, then any sequence of system calls
(including starting and restarting programs) with any arguments, timer ticks, faults,
interrupts, result loads, and boot checks with any measurement. They are in
`LeanOS/Proofs.lean`, the bounds on the state in `LeanOS/Bounds.lean`, and fair receive and
fair running in `LeanOS/Fair.lean`.

Tasks can hand each other memory, so the central guarantee is about where memory can go.
The boot manifest (`initCaps` in `Kernel.lean`) fixes which task can send with the grant
right to which (`Edge`). Endpoint capabilities themselves never move.

| Theorem | Statement |
|---|---|
| `frame_flow` | A task holds a frame only if a chain of grant edges leads to it from the frame's owner at boot, and never with more rights than the owner had. |
| `endpoints_fixed` | Endpoint capabilities never gain rights and keep their badge, so no task can forge who it is. |
| `edge_iff`, `reach_iff` | In the manifest the only grant edges are from the apps (Notes, Terminal, Settings, Security, Files, Apps and the open slots) to the display server, from Notes, Terminal, Files, Apps and the open slots to the file server, and from Terminal, Apps and the open slots to the USB driver, which serves the network. Memory moves at most one step: no server can pass on what it was given. |
| `confined` | Every task but the three servers (the display server, the file server and the USB driver) only ever holds its own 256 frames. (`mallory_confined`, `carol_confined`, `alice_confined` are the same for those three.) |
| `server_frames`, `file_server_frames`, `net_server_frames` | The display server holds only its own frames, the framebuffer, and frames the apps granted it; the file server, only its own frames and frames its clients granted it; the USB driver, only its own frames and frames its network clients lent it. |
| `mapping_flow` | A page a task can see belongs, at boot, to a task that can reach it along grant edges. |
| `file_server_knows_the_sender` | Every capability to the file server's endpoint that a task holds with the send right carries that task's own badge, and the kernel delivers the badge with every message: a program in open slot k arrives as k, and cannot pass for Terminal, Files, Apps or Notes. |
| `blocks_fixed`, `disk_only_file_server` | Block capabilities never move and never gain rights: only the file server ever holds one, for the manifest's 1,048,576 blocks (512 MiB; the machine layer keeps every access inside the card's data partition). |
| `block_io_confined`, `block_run_confined` | When a call asks the machine layer for block I/O, it asks for a run of 1 to 32 blocks (`maxRun`), and every block of the run is inside one block capability the caller holds with the right it needs; every byte the run moves, 512 a block, is in the user window, in a page the caller has mapped writable (a read fills it) or readable (a write sends it). `block_io_confined` says the same of the run's first block, as it did when a call moved one block. |
| `drop_only_shrinks` | After `drop`, every task holds a subset of the capabilities and mappings it held before. |
| `maps_backed` | Every page a task can see comes from one of its own capabilities, with that capability's rights. |
| `no_write_execute` | No page is ever both writable and executable. |
| `maps_in_range` | Every mapping is inside the 8192-page user window and the frame pool. |
| `derive_never_amplifies` | A derived capability covers only frames its parent covers (or names the same endpoint), keeps its badge, and allows nothing the parent does not. |
| `write_reads_only_readable` | When `write` asks the machine layer to print user memory, every byte is in a page the calling task has mapped readable. |
| `schedule_picks_ready`, `rotate_picks_ready` | If any task is ready that no other core is running, the scheduler picks such a task, and so does the round robin every timer interrupt runs. |
| `syscall_wall`, `only_usb_driver_sets_time` | Only `setwall` changes the time of day, and only the USB driver, through the time capability it alone was given, ever sets it. |
| `schedule_not_on_other_core`, `enter_only_cores` | The scheduler never picks a task another core is running, so no task runs on two cores at once. Telling the kernel which task each core runs changes nothing else. |
| `wake_runs_next`, `schedule_prefers_woken`, `schedule_spends_woken` | A send, a call, a receive or a reply that wakes a task (one not ready is now) makes it the task to run next on this core, when the caller stops; a call, which waits for the reply, runs it at once (if no other core runs it). When the task running on a core stops, the scheduler picks the task a wake-up chose last, if it may run there, before any task waiting for its turn, and the choice is spent on that one pick. |
| `irq_runs_holder`, `irq_not_on_other_core` | An interrupt that wakes the task waiting for it runs that task at once on the core that took it (unless another core runs it), and the task it took the core from runs after it. An interrupt never gives a core a task another core is running. |
| `reply_grants_nothing` | A reply changes no task's capabilities or mappings. |
| `reply_wakes_only_caller` | A reply wakes only a task waiting for this replier. |
| `only_verified_runs` | Every task that can run in a manifest slot was loaded with exactly the code and assets the manifest names. The six open slots (10 to 15) run whatever program Terminal or Apps starts them with; that program is measured and shown, and holds only what the manifest gives the slot. |
| `verify_refuses_mismatch` | A task in a manifest slot whose measurement differs from the manifest is stopped for good. |
| `exec_reads_only_readable` | When a program image is loaded, the slot is an open slot, the image is at most 64 KiB, and every byte comes from a page the loader has mapped readable (in its address space as it is after the start). |
| `irqs_fixed` | Interrupt capabilities never move: a task holds one only if it held it at boot. |
| `only_display_powers` | When a call asks the machine layer to switch off or restart, the caller is the display server. |
| `clock_monotone`, `syscall_now`, `tick_now`, `time_reads_clock`, `clockOf_spec` | The clock never goes back: no system call changes it, and a timer tick moves it on by exactly one. `time` returns it, as milliseconds and as hours, minutes and seconds that add up to it, and changes nothing else. |
| `sleep_on_time` | `sleep` never ends early, and is at most one tick late. |
| `tick_wakes_only_sleepers` | If a timer tick changes a task's status, the task was asleep until at most that tick, and is now ready. |
| `irq_wakes_holder` | An interrupt wakes only a task given that interrupt's capability at boot. |
| `uart_confined`, `uart_irq_only_input` | Only the input driver can ever hold the UART's registers or its interrupt. |
| `only_settings_touches_board`, `board_needs_right`, `board_requests_listed`, `cpu_never_overclocked` | Only Settings reads or changes the board, through its board capability with the right the request needs, and only with a listed request: read the board or the sensors, the activity light off or on, or the CPU at 600, 1000 or 1500 MHz, never above. |
| `only_usb_driver_drives_usb`, `usb_writes_safe`, `usb_dma_confined`, `usb_dma_own_memory` | Only the USB driver reaches the USB controller. A plain register write it passes on never starts a channel, sets a DMA address or transfer size, forces device mode or turns on descriptor DMA; a transfer starts only inside one run of the driver's own frames, so the controller only ever touches memory the manifest gave the driver. |
| `start_revokes` | When `start` has the machine layer load slot `k`, the slot holds the manifest's fresh, unverified task, and no other task holds a capability to or a mapping of any of the slot's frames, is waiting to send a message granting one, or holds a reply slot for the old run. |
| `task_bounded` | Every task holds at most 64 capabilities, at most 8192 mappings (no two for the same virtual page), at most 8 reply slots and at most 7 result registers. |
| `state_bounded`, `stateSize_le` | When the machine layer calls the kernel as it does (`Driven`: a boot check hands over the eight words of a SHA-256, as `exVerify` does, and only the lines in `irqLines` fire), the state also has exactly 18 tasks, each measured with at most eight words, at most one pending entry per interrupt line, eight DMA addresses and eight transfer sizes for the USB channels, three other cores, and one last-served task for each of the three endpoints: in all, at most 447,559 heap objects. (The scheduler's two task numbers, whom a wake-up chose and where the round robin is, take none.) What that means in bytes is below, under `rt/runtime.c`. |
| `launch_fixed`, `only_display_launches` | Launch capabilities never move: only the display server starts the manifest's apps, and only Terminal and Apps start the open slots. Nothing can restart the display server, the input driver, the file server or the tests. |
| `sysStop_only`, `only_launchers_stop` | A stop changes only the program it names, and only the display server (the apps it starts), Terminal or Apps (the open slots) can stop one: nothing can stop the display server, the input driver, the file server, the USB driver or the tests. |

Fair receive, in `LeanOS/Fair.lean`. Several tasks can be blocked sending to one endpoint
(the display server's, the file server's or the network service's) while its server is
busy. Each endpoint remembers the task whose message it took last, and a receive looks for
a waiting sender from the task after it on, wrapping around after the last task. A step
"takes task k's message on e" when it is the running task's `recv` or `recvt` through a
capability to endpoint e with the receive right, that search finds k, and the message is
delivered (`Takes`).

| Theorem | Statement |
|---|---|
| `recv_in_turn` | When a receive on endpoint e takes task k's message: k was blocked sending to e; none of the tasks the search looked at before k (from the one after the task e served last, up to k, wrapping around) was; e now remembers k, and every other endpoint what it remembered before; and k is no longer blocked sending. |
| `recv_misses_nobody` | A receive finds no message to take (so it waits, or times out) only if no task is blocked sending to its endpoint. |
| `served_only_by_recv` | Every step of the kernel either leaves what each endpoint remembers unchanged, or takes a waiting message as above. |
| `recv_wait_ahead`, `recv_bounded_wait` | Bounded waiting. Take any run of steps from a reachable state during which task j stays blocked sending to endpoint e, in every state of the run. Then the run takes at most as many messages on e as there are tasks between the one e served last and j (`recv_wait_ahead`), so fewer than 18 (`recv_bounded_wait`): once a server has taken 18 messages on its endpoint, every task that was waiting to send to it when the first was taken has been served, or has stopped waiting some other way. |

These are about the order in which a server's waiting senders are served. They do not say
that a server ever calls `recv`, which is its own code, or that a sender is ever scheduled.
A send that finds its receiver already waiting is delivered at once and moves nothing: a
server waits only when nobody is waiting to send to it, so it passes nobody over.

Fair running, also in `LeanOS/Fair.lean`. A task a message or an interrupt woke runs first
(above), for one pick. Otherwise the round robin picks: the first task that may run on the
core after the one it picked last (`KState.turn`), wrapping around (`rotate`). A wake-up's
pick leaves the round where it was, and every timer interrupt, on every core, is a round
robin pick (`tick` on core 0, `rotate` on the others). A task is "waiting to run" when it is
ready, no other core runs it, and it is not the task of the core in the kernel (`Waiting`).

| Theorem | Statement |
|---|---|
| `turn_only_by_round_robin` | Every step of the kernel either leaves the round where it was, or is a round robin pick (`RoundRobin`): the round robin's search, from the task after the one it picked last, found a task that may run here, which now runs here, and the round is at it. |
| `rr_behind_lt` | A round robin pick that leaves task j waiting moves the round strictly closer to j. |
| `run_wait_behind`, `run_bounded_wait` | Bounded waiting. Take any run of steps from a reachable state during which task j stays waiting to run, in every state of the run. Then the round robin picks other tasks at most as many times as it looks at tasks before j, so fewer than 18 times, however often wake-ups run other tasks first. |
| `timer_round_robin`, `timer_bounded_wait` | Every timer interrupt that leaves j waiting is such a pick. So while a task stays ready and no core runs it, fewer than 18 timer interrupts happen, on all the cores together: with each core's timer every 10 ms, a ready task waits less than 180 ms even if only core 0 takes them. |

These are about the kernel's choice. That the machine layer runs the task the kernel picks,
says truly what the other cores run, and takes a timer interrupt on each core every 10 ms is
the machine layer's part (below).

Revocation rests on one more invariant: every run of frames a task holds stays inside one
slot's memory (`RunOK`), so taking back the runs that start in a slot takes back exactly
that slot's frames and nothing else.

And down to the hardware, in `LeanOS/Tables.lean`. The Lean kernel computes every
translation-table word. If the machine layer stores those words (the `Stored`
hypotheses, which give the `Installed` ones every theorem below assumes), then under the
MMU model in `LeanOS/Arm.lean`:

| Theorem | Statement |
|---|---|
| `l3Table_spec`, `l3Table_size`, `Stored.installed`, `stored_iff_installed` | The level-3 table Lean returns for a task in one call, built in one pass over its mappings, has 8192 words, and holds at each index the word `l3Word` gives for that page (the first mapping of the page, or nothing), so tables stored from it are `Installed`; `Stored` asks nothing more than that. |
| `walk_eq_view` | For every virtual address, what user mode may do there is exactly what the task's mappings say, and nothing outside the 32 MiB user window. |
| `physOf_inj` | Different frames are different physical pages: the framebuffer never overlaps the pool. |
| `el0_no_write_execute` | No address user mode can reach is both writable and executable. |
| `el0_flow`, `el0_shared` | A physical page user mode can reach came along grant edges from its owner; two tasks share a page only if one owner reaches both. |
| `el0_mallory_isolated` | mallory's user mode never reaches a page any other task can reach. |
| `el0_only_pool_fb_uart` | User mode reaches only the frame pool, the framebuffer and the UART's page. |
| `el0_uart_only_input` | Only the input driver's user mode can touch the UART's registers. |

`make mutants` breaks the kernel in 133 specific ways (a `derive` that amplifies, forges a
badge or cuts past the end of a run, a send without the grant right, an endpoint granted like a frame, a manifest that
gives mallory one more right, the framebuffer or a launch capability, a framebuffer address that overlaps the
pool, a kernel page-table entry missing its execute-never bit, a level-3 table that keeps the
wrong mapping of a page or maps page 0 where nothing is mapped, a `start` that forgets to take back
mappings, capabilities, waiting grants or reply slots, a `map` that keeps the old mappings of the pages
it maps, a `derive`, a grant or a call past its limit, a receive that searches from task 0 again, from the
task it served last, or one task short, or forgets whom it served, a scheduler that ignores whom a wake-up
chose or keeps choosing it, a timer that follows a wake-up's choice, a round robin that forgets where it is,
an interrupt that waits for its holder's turn or runs it on a core already running it, a block run
that checks its capability or its memory for the first block or page only, one block short or long, or
without the right, and so on) and
checks that the proofs reject every one.

`make test` checks that each theorem rests only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and never on `sorry`.

## Trusted, not proved

Each item below is assumed correct. A bug in any of them could break a guarantee even
though every proof checks.

**Tools**
- Lean's kernel, which checks the proofs.
- Lean's compiler, which turns `Kernel.lean` into C. The proofs are about the Lean
  definitions, and this compiler is what makes the running code match them. Where
  `Kernel.lean` gives a loop for one of its list walks, the compiler runs the loop in its
  place only because a `@[csimp]` theorem proves the two equal (`dropRange_eq_dropRangeTR`
  and eight more, checked for axioms with the rest).
- The C that the same compiler generates for the seven standard-library modules the kernel
  imports (`Init.Prelude`, `Coe`, `Notation`, `SizeOf`, `Tactics`, `Core`, and
  `Data.Array.Set`, for writing one word of the level-3 table).
- clang and ld.lld.

**`rt/runtime.c` (~450 lines)**: the part of Lean's runtime compiled code needs, rewritten
for bare metal: allocator, reference counting, closures, arrays. Its limits:
- Numbers must stay below 2^63. A larger one stops the machine and never gives a wrong
  answer. Two standard-library constants (`UInt64.size`, `USize.size`) are built at
  startup as opaque placeholders, and any arithmetic on one stops the machine.
- One core at a time: the machine layer's kernel lock keeps every other core out while
  one runs compiled Lean code or the runtime, which are not safe to run on two cores at
  once (reference counts and the allocator are not atomic).
- Freeing: an object whose count reaches zero frees its children through a fixed stack of
  4096 entries, never by recursion. Children go on it last field first, so of a list cell
  the element is freed before the rest of the list, and a list of any length needs only a
  few entries (`test/stack.sh` frees a task's 8192 mappings at once). A structure that
  still ran past the stack would stop the machine, not corrupt it.
- The kernel heap has a fixed size: from the end of the kernel image and its stacks
  (`__heap_start`, `arch/kernel.ld`; 0x331000 in this build) to the frame pool at 64 MiB
  (`FRAME_BASE`, `arch/arch.h`), 63,762,432 bytes (60.8 MiB). `stateSize_le` proves that
  the kernel's state, between two kernel entries, is at most 447,559 heap objects, whatever
  the tasks do. What that is in bytes rests on the runtime's object layout, which is
  trusted, not proved:
  - A number below 2^63 is stored in the pointer itself (`lean_box`), not on the heap, and
    so are a `Bool` and a constructor without fields. Every number in the state stays below
    2^63 (above; a larger one stops the machine), so the state's numbers take no heap. The
    count relies on this: a larger number would be an object of its own.
  - An object with n pointer fields and b bytes of scalars asks for 8 + 8n + b bytes, which
    `lean.h` passes to `malloc` with 8 bytes more; `malloc` rounds that up to a multiple of
    16 and adds a 16-byte header. So a list cell, an `Obj`, a `Rights`, an `Option`'s `some`
    and a `Status` with fields take 48 bytes each, a `Cap` or a `Mapping` 64, a `Task` or a
    `Msg` 80, and the one `KState` 112 (as the generated C allocates them:
    `lean_alloc_ctor(0, 6, 0)` for a task, and so on).

  So the state takes at most 447,558 × 80 + 112 = 35,804,752 bytes (34.1 MiB). Counting
  each kind at its own size, the bounds of `state_bounded` give less: a task at most
  1,325,600 bytes with its list cell (1,310,720 of them for 8192 mappings of 160 bytes
  each: the cell, the `Mapping` and its `Rights`), 18 tasks 23,860,800, and the whole state
  23,862,064 bytes (22.8 MiB), 37% of the heap. For scale: in `test/stack.sh`, with one
  task holding all 8192 mappings, the heap's peak is 1,448,480 bytes. In `test/chaos.sh`,
  with six programs from the card each holding 64 capabilities and 8192 mappings at once,
  then one slot restarted 30 times beside five of them, it is 5,787,136 bytes. The machine
  layer reports the heap after every start (`leanos: kernel heap N bytes live`), and with
  the same programs in the same slots that number is the same to the byte every time: what
  a stopped, faulted or exited program held is all freed when its slot starts again.

  Not proved: the memory a step uses while it computes the next state. A step builds the
  new state from the old; compiled Lean updates an object in place when nothing else holds
  it, and copies it otherwise, so until the step ends it may hold an old and a new copy of
  what it changes (for `start`, every task's lists). Two whole states (45.5 MiB) would still
  fit, but that is an argument, not a proof. Garbage is freed as soon as its reference
  count reaches zero (`lean_dec_ref_cold`; Lean's data has no cycles), so it does not pile
  up from one step to the next; that is the runtime's code, trusted. The allocator never
  gives memory back to its bump pointer: a freed block waits on its size's free list, so
  the heap must hold each size's peak, and the state uses four sizes (48, 64, 80 and 112
  bytes). The machine layer's own objects (each call's `Reply`, 160 bytes, and the
  constants built once at boot) come on top. If the heap runs out anyway, the kernel
  panics, which denies service but never breaks isolation.

**`arch/boot.S`, `arch/kmain.c` and `arch/bootcon.c` (~2,200 lines)**
- Storing the tables: `mmu_init`, `tables_init` and `build_user_pages` must store each
  word Lean computes at its index, in the page-aligned arrays whose addresses they pass to
  Lean (a level-1 table, a level-2 table, and 16 level-3 tables in one array). For level 3,
  `build_user_pages` asks Lean once per task for the whole table (`l3Table`, an array of
  8192 words, `l3Table_size`) and must store word k of it at index k, reading the array as
  the runtime lays it out (`lean_array_get_core`). This is exactly the `Stored`
  hypothesis, and `Stored.installed` turns it into the `Installed` one the theorems
  assume. The kernel is identity-mapped,
  so those addresses are physical. TTBR0 must point at the task's level-1 table, and the
  TLB must be invalidated after every change (`tlb_flush_all`).
- MMU configuration: TCR_EL1 and SCTLR_EL1 must be set as `LeanOS/Arm.lean` assumes (4 KiB
  granule, T0SZ = 25, EPD1 = 1, WXN = 0). `mmu_init` sets each of these explicitly.
- Trap entry and exit, the saved-register copy, and the switch between address spaces
  (TTBR0, with one ASID per task).
- Result registers: after every kernel entry, `load_result` copies the registers the Lean
  kernel left for the task about to run into its saved frame, then tells the kernel.
- `do_syscall` reads the buffer for `write` while the calling task's address space is
  still active. The proof covers which pages may be read. That the read happens in the
  right address space is this code's job.
- The runtime keeps Lean numbers below 2^63 and has no big numbers: one would stop the
  machine. So `arg` in `arch/kmain.c` clamps every argument that is an index, address,
  count, length, time or set of rights to 2^40, which every call refuses, and which keeps
  every sum and product the kernel makes from arguments far below 2^63. Message words
  (send, call and reply) are only carried, never computed with, and keep their low 63
  bits; the top bit is dropped. That the clamp never changes an outcome is argued here, not
  proved. `test/fuzz.sh` runs 20,000 calls with edge-case arguments against it; before
  this rule, one call with two arguments near 2^62 stopped the machine, and one unmap of
  2^40 pages kept the kernel busy for hours (`dropRange` now walks the task's mappings,
  not the range).
- The board's settings: `board_request` in `arch/kmain.c` carries out the only requests the
  kernel proves can arrive (read the board, read the sensors, the activity light on GPIO 42,
  the CPU at 600, 1000 or 1500 MHz) through the firmware's mailbox. What the firmware
  answers is passed back unexamined, and what the firmware does with a clock request (it
  may cap it further, for heat or power) is the firmware's.
- The clock's link to real time: `now` counts ticks of 10 ms, and the machine layer keeps
  that count with the counter. Each core's timer is set to an absolute value on the counter
  (CNTP_CVAL), its next tick, not to an interval from when the last one was taken, and when
  core 0's interrupt comes late it passes the kernel one tick for every interval that ended
  (at most 100 at once; a longer gap, a stalled host, is let go). Before, a late interrupt
  pushed every later tick back, and under QEMU the clock ran about a quarter slow;
  `test/clock.sh` now checks the kernel's clock against the counter to within 30 ms. That the
  interval is right is argued, not proved; the proofs are about the count.
- The USB controller: `usb_request` in `arch/kmain.c` carries out only what `sysUsb`
  returned. It writes a checked physical address with the controller's bus offset
  (0xC0000000, the VideoCore's view of RAM, which QEMU's model also maps), and keeps the
  cache out of the way: a started range is cleaned and invalidated before the start, and
  invalidated again when the driver next reads that channel's interrupt register. That the
  DWC2 in buffer DMA mode touches no memory but HCDMA to HCDMA plus the transfer size (and
  at most one packet more, which the kernel's check includes) is the controller's
  documented behavior, trusted, not proved; so is that nothing else in its register page
  can make it DMA once device mode, descriptor DMA and the descriptor-list registers are
  refused. On a Pi 4 the DWC2 is the USB-C port; the USB-A ports need a separate xHCI
  driver, whose DMA (rings of descriptors in memory) this scheme does not cover yet.
- The time of day: that the time server's answer is right is trusted, not proved (SNTP, one
  question, no authentication: anyone on the network path could send a wrong time). The
  proofs say only who can set it and that it then moves with the kernel's own clock.
- The time zone changes only what the menu bar and Clock show; the kernel's time stays UTC.
  The display server keeps it, and the background, and takes a new one of either only from
  Settings' badge (and, for each, once at boot from Apps, which reads back what it saved on
  the card in `settings.txt`, or an older card's `timezone.txt`, unless Settings has chosen
  one since), a zone a quarter hour between -12:00 and +14:00, a background one of the
  three. That rule is the display server's C (`on_set` in `user/display.c`), trusted, not
  proved.
- The clipboard, and its rule that text moves between programs only by the user's hand, is
  the display server's C (`copy_ask`, `on_copy` and `paste_to` in `user/display.c`),
  trusted, not proved. What it guarantees: it takes a copy only after Ctrl+C (or Edit,
  Copy) comes from the input driver or the USB driver, only from the badge of the window
  that was in front then (the kernel sets badges: `endpoints_fixed`), only until that copy
  ends, and only within 2 seconds of asking; it hands what was copied only to the window in
  front when Ctrl+V (or Edit, Paste) comes, after the events already waiting for it; no
  request returns it; and no memory is lent for any of it, so the proofs about what each
  task holds are unchanged. What it does not guarantee: what text a program answers with
  (the window asked may copy anything it likes), what a program does with a paste (it sees
  all of it, and can keep it or send it on over any channel it has), or that the keys came
  from a person (the input and USB drivers are trusted to report what was typed, and on
  QEMU the host's serial bridge is too). The display sees every copy and paste, as it
  already sees every key and every window's pixels. The clipboard lives only in its memory
  and is gone when leanos restarts.
- The display server's reply slots. It holds a waiting program's call (OP_WAIT) until it has
  an event for any of its windows, one call per program however many windows it has, and
  the kernel gives it 8 reply slots (`task_bounded`) for up to 12 windows. It holds at most
  7, so a new call always finds one free; past that, the program that has waited longest is
  answered with no event and asks again a moment
  later (`app_wait` in `user/app.h`, every 100 ms), and is answered at once, with its
  events or none, while the slots stay taken. That rule is the display server's C
  (`on_wait` and `park_oldest` in `user/display.c`), trusted, not proved. Before it, with 8
  windows waiting, the next call made every receive the display tried fail as full, and no
  key or click reached anyone again until a restart (`test/freeze.sh`). A program that asks
  again at once, not after a moment, spins with the display while it is parked: that costs
  time, not authority.
- The display server's records of a program whose slot starts again. Starting a slot frees
  every reply slot held for its last run, for the next caller to take, and takes back the
  pixels that run lent the display (`start_revokes`). The display cannot ask which run a
  program is: bootinfo says only not started, running or stopped, and the same program
  measures the same. So it keeps its records true this way: before it answers any call it
  forgets the windows of stopped programs, answering any call it held for them; Terminal
  and Apps, which hold the open slots' launch capabilities, call it after they find a slot
  stopped and just before they start it (`app_before_start` in `user/app.h`); and it starts
  the built-in apps itself, after dropping their windows. Then no answer meant for a
  window's last run reaches the next caller, and it never draws pixels it no longer has.
  Should a start ever get past it all the same, what the kernel hands it shows it: a call
  that arrives in a reply slot it thought it held means that record is of a dropped call,
  and is forgotten unanswered (`claim_slot`); holding fewer capabilities than it counts
  means a slot was started again, and it forgets that slot's windows without touching them
  (`lost_runs`: the slot whose grants number what is missing, or whose program's hash
  changed; if it cannot tell, it lets every granted capability go and closes every
  window). Trusted C, not proved. Before it, a program that stopped by itself while
  Terminal was loading another left its window behind: the next program started in its
  slot had its wait held on the dead window, and the display stopped when it drew the old
  pixels (`test/restart.sh`).
- What else the display server is trusted to do, tested by `test/dfuzz.sh`, not proved. It
  cannot be restarted, so a crash freezes the machine, and it holds every window's pixels.
  It must answer every message, whatever its op, words and grant hold, with an answer the
  protocol (`user/app.h`) allows, and never stop or hang; map a window's grant only into that
  window's own slot of its address space, and an icon's only into that icon's, so it never
  draws one program's memory as another's window; draw a window, its title bar and its
  title (the program's words) only inside its frame, below the menu bar, with the dock and
  the menu bar on top, as a drag keeps them; drop every grant it does not use; forget a
  stopped program's windows; and log a few lines of any flood, not each request, since a
  line holds the kernel while the serial port takes it. The test runs a fuzzer from the open
  slots (`user/progs/dfuzz.c`), two at once: fixed requests for every op (sizes 0, huge and
  past 16 bits, too few pages and more than a window's slot, no grant, the code run and the
  stack as pixels, an endpoint as the grant, a window taller than the room, one a pixel wide;
  icons with bad markers, sizes and page counts, and not from the loader's four pages; SET,
  START, RAISE and PENDING a card program may not make; ZONE; unknown ops; grants by plain
  send; CLOSE of window numbers it does not hold, another program's among them, and past the
  table; a window closed twice, and a wait after closing its only window), without a window
  and with one, and with several (every window's number the lowest it does not hold, every
  event for a window of its own); windows and icons near every limit checked against
  the rule; floods; thousands of random requests, calls and plain sends; windows until the
  table is full. Then one is killed while the display holds its call, one killed in the
  middle, one exits and one faults just after grants sent by plain send, and the kernel heap
  after each start of the slot must be the same; and copy and paste by hand into one window:
  an answer past the clipboard's 4 KiB, a late one and one after the close button must be
  refused, and the paste must be exactly what was taken. While the two fuzz, the user's hand
  does 30 things at random: Ctrl+O, the yellow and green buttons of the window in front, and
  the fuzzers' and Terminal's dock icons; then a fuzzer's windows are minimized before it is
  killed. The screen is checked too: with
  every fuzzer window up, the menu bar and the dock's opaque icon pixels are as at the end,
  and a window a pixel wide changes nothing past its frame and shadow. The seed is printed,
  so a run can be repeated. What it does not show: that its requests reach every path
  through the code, events from the input and USB drivers other than a few keys and clicks
  (`test/restart.sh` and `test/freeze.sh` check which window gets them), or a display that
  holds a program's pixels and draws them wrongly without drawing past its frame. It found
  five bugs, now fixed and kept in its fixed requests:
  - A window took a grant of any size and the display mapped all of it at the window's
    slot, so a small window from a grant of 200 pages reached 16 pages into the next
    window's slot: that window then showed this program's pixels (a red band over the top of
    Terminal, in the test's first form). A grant longer than a window's slot is refused.
  - An icon took a grant of four pages or more, and a longer one reached over the next
    windows' icons the same way. An icon's grant must be its four pages.
  - A window the display refused, and a RAISE that found its window, were each logged every
    time: 601 and 400 lines in one run, each holding the kernel while the serial port took
    it. Each program's are now logged three times at most, as its other refusals are.
  - A window taller than the room between the menu bar and the dock was placed with its
    title bar, and the title its program chose, over the menu bar. It now opens below the
    menu bar, where a drag keeps it, and reaches under the dock instead.
  - A window narrower than its buttons and title drew them past its frame, over whatever
    was beside it, where a click reaches another window. They are now drawn only inside the
    frame (a window 12 pixels wide or less has no close button to click; `kill` stops it).
  It found a sixth, now fixed as the next entry says (`test/spoof.sh`): the name a window
  took from its icon was whatever name any four pages with the icon's marker held, so a
  program could take another's. It found a limit too, now lifted as the entry after next
  says: a program with several windows heard only its first window's events.
- A program's several windows (`test/windows.sh`). A program may open up to the table's 12
  windows. OPEN answers each with a number, 0 for its first, then the lowest the program is
  not using; WAIT and POLL answer with the oldest event for any of its windows, the number
  in the kind word from bit 8 up, so a program with one window sees exactly what it saw
  before. CLOSE (12) takes one of the caller's own windows off the screen and out of the
  table at once, and drops what it lent for it; a window whose close button was clicked
  leaves the table when its program hears that EV_CLOSE. The display finds the window by the
  caller's badge, which the kernel sets (`endpoints_fixed`), and the number together, so a
  program can close, and hear the events of, only its own windows; a number it does not
  hold is refused (the whole word counts: 2^32 is not 0). A click on a
  running program in the dock, RAISE (Terminal's `run`), or a pinned program's icon brings
  all its windows forward, the one of them in front last in front, and its minimized ones
  back (next entry); the dock shows one icon per program. Keys, copy and paste go to the window in front, and the program learns which
  from the event. Trusted C (`on_wait`, `next_event`, `on_close` in `user/display.c`), not
  proved; the grants a window takes, the icon and name rules and the 7 held calls are as
  for one window.
- Minimize, zoom and the next window (`test/winmgmt.sh`), all the display server's; no
  program changes and the protocol is the same. A window's yellow button (or Window,
  Minimize) takes it out of the display's stack of windows: it is not drawn, no click finds
  it, and keys, copy and paste, which go only to the window in front, go to the next one
  down. Nothing else about it changes: its program keeps running and waiting, what it lent
  (its pixels, its icon) stays lent and mapped, its waiting call is held as any other (the 7
  held calls), a redraw it asks for is not drawn, and it may close the window, which goes as
  any other. While minimized it hears no event but EV_CLOSE (when it closes that window, or
  stops) and EV_LAUNCH if it is Apps (the display's own request to start a pinned program or
  save the settings, which the user asked for elsewhere; it is not input to the window);
  events queued before the click are still handed out. Its program's dock icon (built-in,
  pinned or from the card) and RAISE (`run` in Terminal and Apps) bring back all its
  minimized windows, where they were, in front; its dot in the dock is amber while any is
  minimized. No request minimizes a window; RAISE, which anyone may send, brings back the
  minimized windows of the program it names, as it already brought its windows forward. A
  slot started again while its window is minimized: the window is forgotten as any other of
  the last run (previous entries). A new window is placed where it covers least of the
  windows shown, not of the minimized ones. The green button (or Window, Zoom) moves a
  window to the middle of the room between the menu bar and the dock, in front, and a second
  click moves it back (after a drag, it zooms from where it was dragged): a program draws its
  window at one size, so zoom moves, never resizes. Ctrl+O (byte 15, from the serial line,
  the browser console or a USB keyboard; no app uses it) or Window, Next window, sends the
  window in front to the back, so the next comes to the front. Every one of these is logged
  once per click or key. Trusted C (`minimize`, `zoom`, `next_window` and `raise_program` in
  `user/display.c`), not proved; `test/dfuzz.sh` does them at random while two fuzzers make
  their requests.
- A window's name. The display names the window of a program from the card after the file
  it was run from, and RAISE, `run` and the dock's pinned programs look for that name: while
  a window is named clock, clicking Clock in the dock or typing `run clock` brings that
  window forward instead of starting Clock. So the name must be the one the loader wrote,
  and no program may write one. What is enforced:
  - The loaders, Terminal's `run` and Apps (`elf_load` in `user/elfload.h`), write the
    icon's marker, the icon from NAME.icon and the name of the file they ran at pages 12 to
    15 of the image (`image_add_icon` in `user/elf.h`; an image over 48 KiB gets neither),
    and refuse an image in which a page already starts with the marker (`image_marked`).
  - `app_open` (`user/app.h`) lends those four pages with the code run's read and execute
    rights.
  - The display (`on_icon` in `user/display.c`) takes an icon and a name only from a
    program in an open slot (badges 10 to 15), only from a grant of exactly four pages that
    carries the execute right (it asks `capinfo`), and only if they start with the marker.
    It maps a read-only copy in the grant's place, so nothing a program lends ever runs in
    the display.

  Why a program cannot get around it, from the proofs. A program in an open slot holds
  capabilities only to its own 256 frames (`confined`), each with no more rights than a
  capability to that frame the manifest gave its slot (`frame_flow`), and the manifest gives
  the execute right only on the code run (`frameCaps`: the code run read and execute; the
  data, stack and spare runs read and write). `derive` never adds a right
  (`derive_never_amplifies`): asking for execute on a run that lacks it gives read only.
  So the only pages a program can lend with the execute right are its own code run's. No
  task can write those: by `frame_flow` every capability to them has at most read and
  execute, and every mapping has its capability's rights (`maps_backed`), so no page of a
  code run is ever mapped writable (and none is both, `no_write_execute`). The code run
  holds only the image the loader built, loaded when the slot starts
  (`exec_reads_only_readable`; the machine layer clears the frames first). In that image
  the only page starting with the marker is the loader's, which ends with the name it
  wrote. So a window's name is the name of the file the loader ran, or none.

  What is trusted: the loaders (user-space C in Terminal and Apps, in the kernel image and
  measured) to write the name of the file they ran and to refuse an image with a marker of
  its own; the display's check; and the machine layer's loading of the image. And the name
  is a file name, no more: a program called `evil` cannot make its window `clock`, but any
  file called `clock` that the user runs is `clock` to the display, whatever it holds (a
  program can write files in its own folder, `apps/NAME`, and a user who runs one of them
  by that name runs what it wrote). A window's title (8 bytes) is still the program's own
  words, and its pixels are whatever it draws. `test/spoof.sh`: a program lends a forged
  icon named clock from its spare pages (read-only, read-write, and asking for execute),
  its data pages and its stack, and its code run without the execute right or from pages
  the loader did not write; every claim is refused, while its own name, lent as app_open
  lends it, is taken. A program whose code carries the marker at the start of a page is not
  run. Then Clock in the dock starts the real Clock, `run clock` finds it by its name, and
  after `kill` starts it again. Before the fix, the first claim from the spare pages named
  its window clock, a program with a forged code run named its window clock the same way,
  and the dock's Clock only brought the impostor forward.
- The panic screen: `kpanic` writes the reason to the serial port and the framebuffer,
  with the boot step it stopped in and, for an exception, its class, ELR, FAR and ESR, then
  stops (on a Pi, blinking the step on the green LED). A fault while stopping halts at once.
- The boot console (`arch/bootcon.c`): each boot step is announced before it runs, on the
  serial port and, once the framebuffer exists, drawn on it with the kernel's lines, until
  just before the first task runs; from then on only the panic screen draws. Every pixel it
  draws is cleaned and invalidated out of the cache at once, so no dirty line of the
  kernel's cached view of the framebuffer can land later over what the display server
  draws through its own uncached mapping. It reports and decides nothing. When `kputc`
  gives up on a UART that takes nothing, the console says so on the screen. On a Pi it
  also drives the green activity LED (GPIO 42, the light `_start` turns on when loaded at
  the wrong address) during boot, and blinks a panic's step on it.
- Interrupts stay masked while the kernel runs, so the Lean kernel is never re-entered.
- Four cores (`arch/kmain.c`, "the cores"; `arch/boot.S`, `secondary`). Core 0 boots, then
  hands cores 1-3 their entry through the boot stub's spin table (on a Pi 4 the firmware's
  armstub parks them at EL2, reading 0xe0, 0xe8 and 0xf0 with their caches off, so the
  entries are cleaned to memory before the SEV that wakes them). Every core drops from EL2
  to EL1 in `arch/boot.S`, which sets what EL1 relies on rather than leave it at reset
  values the architecture calls UNKNOWN (the armstub sets none of it): HCR_EL2 (EL1 is
  AArch64, nothing trapped), CNTHCTL_EL2 (EL1 uses the physical timer and counter),
  CPTR_EL2 and HSTR_EL2 (no traps to EL2), and VPIDR_EL2 and VMPIDR_EL2 (so each core reads
  its own number). Each core turns on its own MMU and caches with the same kernel tables:
  core 0 in `mmu_enable_this_core`, cores 1-3 in `secondary`, with core 0's register
  values (`mmu_regs`, cleaned to memory), before they touch their stacks, since until then
  their accesses bypass the caches core 0 runs with. Each has its own timer, its own part
  of the interrupt controller, and its own 64 KiB kernel stack, painted and checked like
  core 0's. The machine layer must:
  - take the kernel lock (`lock`, an exclusive-access spin lock with acquire and release
    semantics) before any Lean call or runtime use, and let go only just before returning
    to user mode, so the Lean kernel's state is never touched by two cores at once;
  - tell Lean, after taking the lock, which task this core runs and which each other core
    runs (`enter_lean`). This is what makes `cur` in every proof the task that made the
    call, and what `schedule_not_on_other_core` rests on;
  - run only a task Lean calls `runnable` for this core (`pick`): after an interrupt, the
    task Lean now names, which may be the one the interrupt woke;
  - before loading a slot, make every other core running that slot's task leave user mode
    (`evict`: a wake-up interrupt, then wait until it is out), and drop what that core was
    doing when it gets the lock. A core whose task was stopped from another core drops the
    call it was making the same way;
  - use TLB maintenance that reaches every core (`tlbi vmalle1is`), since a task may run
    on any core and another core may change its tables.
  Device interrupts go to core 0 only; timer ticks from cores 1-3 only move the round robin
  on (`exRotate`), so `now` counts core 0's ticks. `timer_bounded_wait` counts timer
  interrupts; that each core takes one every 10 ms is this layer's timer programming. Disk, USB and board requests run with the lock held, so
  while one is in progress the other cores wait to enter the kernel. A disk request is a
  run of up to 32 blocks (16 KiB): on the Pi's card, at 25 MHz on one data line, about 6 ms
  of transfer and whatever the card takes to start and to finish writing.
- Interrupt routing: `irq_init` enables exactly the lines Lean lists (`irqLines`); when one
  fires, `handle_irq` masks it before telling Lean, and unmasks it only when a Reply says
  so (an acknowledge from the capability's holder).
- The idle loop waits for interrupts with WFI, without the lock, when no task is ready for its core.
- Measurement: `measure_and_verify` hashes exactly the bytes each task will run from (its
  code, then its assets, where they sit in its own frames) with SHA-256 (`arch/sha256.c`,
  checked against the FIPS 180-4 test vector at every boot) and hands the digest to Lean.
  Lean decides; `only_verified_runs` holds whatever digest it is given.
- Assets: `load_program` copies each task's asset blob (fonts and icons, built by
  `tools/mkassets.py`) into the start of that task's own spare run, next to its code. The
  blob is data the task reads; it grants nothing.
- Power: switching off is the same halt as before (semihosting exit under QEMU; a Pi has
  no power switch the kernel can reach, so it stops). Restarting writes the power-management
  block's watchdog for a full reset (`restart()`); both only when a Reply says so, and
  `only_display_powers` says only the display server's calls can.
- The UART: `uart_pins` routes the PL011 to GPIO 14 and 15, as a Pi 4 needs (its firmware
  gives the PL011 to Bluetooth, on GPIO 30-33), with no device tree involved, and takes
  30-33 off the PL011 so its receive line has one source. `uart_init` divides the clock the
  firmware says the UART has (48 MHz on a Pi 4, `init_uart_clock` in `config.txt`), or
  48 MHz if it does not say. `kputc` writes 32 bits at a time, and its wait for room is
  bounded, so a UART that takes nothing cannot stop the boot.
- The firmware's mailbox (`mbox_call`): a request buffer with its cache lines to itself,
  cleaned before the request and invalidated after, given to the firmware at its
  VideoCore address (0xC0000000 + physical), with every wait bounded in time. At boot,
  `board_check` asks for and prints the board and firmware revisions, the UART's clock,
  the system counter's rate, and the RAM the firmware left the ARM (it stops the machine if
  that does not cover the kernel, its heap and the frame pool), and switches on the USB
  controller's power domain. Every delay and timeout in this layer is measured with the
  system counter at the rate CNTFRQ_EL0 gives (`arch/arch.h`), never in loop turns.
- The load address: the kernel runs only at 0x80000, where `arch/kernel.ld` links it and
  `config.txt` (`kernel_address`) has the firmware load it; `_start` checks, and anywhere
  else lights the activity light and stops, since nothing else can run there.
- Programs from the SD card: for an open slot the machine layer copies the image from the
  starting task's memory (the Reply's `outVa` and `loadLen`, which
  `exec_reads_only_readable` bounds) into the slot's code frames, after rebuilding the
  tables and clearing the frames, and measures it. Parsing ELF happens in Terminal, in user
  space; the kernel only ever sees a flat image.
- Loading on demand: at boot only the programs `autostart` names are loaded; the apps are
  loaded when a `start` Reply names their slot (`load`). The machine layer must then, in
  this order, rebuild every task's tables from the revoked state, clear all 256 of the
  slot's frames, copy in exactly that slot's program and assets, reset its saved
  registers, and measure it, before any task runs again. `start_revokes` says no other
  task can reach those frames once the tables are rebuilt; that the clearing and loading
  touch only the slot's frames is this code's job.
- The SD card (`arch/sd.c`, ~400 lines): an SDHCI driver by programmed I/O only, never
  DMA, because the controller can be told to write anywhere in physical memory. It must
  move exactly the 512 bytes a block at the address a Reply names, to or from exactly the
  run of blocks it names ((io + 1) / 2 blocks from `ioBlock`, read if `io` is odd, written
  if even: the C decodes `ioCount` and `ioWrites` itself), while the calling task's address
  space is live; block numbers are inside the card's data partition (type 0xDA, found in
  the partition table at boot), and a run that does not fit in it fails whole, so the boot
  partition a real Pi starts from is never read or written; `block_run_confined` says those
  are allowed, this code must do nothing else. One block is one command (CMD17, CMD24); a
  run of more is one multi-block command (CMD18, CMD25) with the block count register set
  and auto CMD12 (the controller sends the stop itself after the last block; in SDHCI since
  1.0), word by word through the data port, waiting for the controller's buffer-ready flag
  before each block and at most a second for each. A write is complete only once the card
  is no longer busy after the stop, so no later command overtakes it. A failed transfer is
  logged (the command, the blocks, the interrupt status), the controller's lines are reset,
  a multi-block one is stopped with an explicit CMD12, and Lean is told (`ioFailed`, a
  reachable transition), which gives the caller an I/O error. Tested only on QEMU, where the
  card sits on the older EMMC controller; the Pi 4's slot is on EMMC2, and multi-block
  transfers have not run on the Pi yet. (QEMU's card model moves a multi-block transfer a
  byte at a time, so there runs cost more host time per block than single blocks do; on a
  card, the command and the card's own start-up per command dominate.) The setup follows
  what runs on that chip (Linux's `sdhci-iproc`, Circle's EMMC driver): 32-bit register
  access, a short wait after each write while the card clock is slow, the firmware's base
  clock, an identification clock between 200 and 400 kHz, the card's I/O at 3.3 V (the
  firmware's GPIO expander) and never 1.8 V, 25 MHz on one data line, and waits bounded in
  time. Each step's result is printed, and the report at switch-off counts the block I/O
  calls, the commands sent to the card and the blocks moved.
- The kernel stack: 64 KiB per core. The Lean kernel's walks over a task's mappings and
  capabilities (`dropRange`, `runMaps`, `app`, `snoc`, `len`, `removeNth`, `keepBacked`,
  `dropCaps`, `dropMaps`) run as loops, each proved equal to its definition, so how deep
  the stack goes does not depend on how many a task holds. What recursion is left walks
  short lists: the 18 tasks, a task's reply slots (at most 8), the pending interrupt lines
  (at most two; `task_bounded`, `state_bounded`).
  The deepest use measured is 2,160 bytes, at boot (drawing the boot console); a task
  holding all 8192 mappings needs no more (`test/stack.sh`; it was about 900 KiB before
  the loops).

  The worst case is also computed from the code: `tools/stackcheck.py` (`make stackcheck`,
  and `test/stackcheck.sh` in `make test`) finds how deep the stack can go from each place
  the kernel starts on it: `kmain` on core 0, `secondary_main` on cores 1-3, and `trap`
  below the 288 bytes of registers each exception entry in `arch/boot.S` saves, with one
  kernel exception on top of the deepest of them (another 288 bytes and `trap`, which stops
  the machine). Every recursion it finds must be in its table, with a bound: `revokeAll`,
  `wakeSleepers`, `setNth` and `mkTasksFrom` walk the 18 tasks (19 calls deep, with the empty
  tail), `placeCaller` and `forgetCaller` a task's reply slots (9), `dropLine` the pending
  lines (3). Recursion not in the table, an indirect call it cannot resolve, a frame of
  variable size (alloca, a variable-length array) or a worst case over 32 KiB, half the
  stack, fails the check. The worst case is 6,976 bytes: 3,488 for a system call (`start`
  taking back a slot's memory: `revokeAll` over the tasks, then `forgetCaller` over one
  task's reply slots, then an allocation that can fail into `kpanic`, whose message goes
  through `kputc` into the boot console's recording; the tool cannot see that the
  recording stops when the boot ends, so it counts it), and a kernel exception on top of
  that. What it trusts:
  - clang's frame sizes. Each C file of the kernel (`arch/`, `rt/`, the Lean kernel's and
    the standard library's generated C) is compiled a second time into `build/stack/`, with
    the shipped flags and `-fstack-usage`; the tool checks that each object's code and
    relocations are the shipped object's, that every frame is static, and that each
    function's own stack adjustments add up to clang's number.
  - The call graph, read from `build/leanos.elf` with `llvm-objdump`. Every branch that
    leaves a function must go to a function's start; every `br` must be a jump table, whose
    entries the tool reads from the image and finds inside the function; every `blr` must be
    traced back, through the function's code, to the function addresses put in its register
    (in `trap`, the message-word conversion `arg` or `msg_word`), or be the runtime's
    one-time initialization of closed terms (`lean_obj_once_cold` and its kin), whose
    `init` is traced the same way at each call. A call through a pointer loaded from memory
    fails. Lean closures are never applied: no `lean_apply_*` is in the image. Every C
    function in the image must be reached from the three entries, and the assembly may call
    only them. Called functions keep x19-x28, as the AArch64 calling convention says.
  - The recursion bounds. Each is a proved bound on a list in the state (`state_bounded`:
    18 tasks, at most two pending lines, eight USB shadows, three last-served entries;
    `task_bounded`: at most 8 reply
    slots), but that each walk runs over such a list, or over one no longer, is read from
    `Kernel.lean`, not proved. The panic screen draws with the geometry the firmware
    returned (`fb_alloc` keeps it), so `kpanic` calls nothing in the Lean kernel.
  - Exceptions do not nest further. Every exception entry masks interrupts, SError and FIQ,
    and no code in the image unmasks them (the tool checks nothing writes DAIF), so only a
    synchronous exception can come in the kernel; it goes straight to `kpanic`, whose own
    path is taken not to fault again.
  The check covers the image `make` builds for QEMU; the Pi's (`make pi-image`) differs
  in `poweroff` and in `arch/bootcon.c`'s LED and UART waits (leaf loops, no calls), and
  the bring-up kernel (`make pi-bringup`) also in its blink codes, step times and board
  report. The stack is still painted at boot and its bottom checked on every return to
  user mode, for what the tool trusts: an overflow stops the machine instead of corrupting
  kernel memory silently.
- User mode may read the processor's virtual counter (CNTKCTL_EL1.EL0VCTEN), for
  animations and timeouts. This gives no new power: a task could already time itself by
  counting loops. Timing side channels remain out of scope.

- The framebuffer: `fb_alloc` asks the firmware for 1024 x 600 x 32 through the mailbox,
  once at boot (pixel order BGR, alpha ignored, no virtual offset, page-aligned), prints
  what the firmware returned, and passes the address (the bus address's low 30 bits) to
  Lean only if the reply matches the request: the virtual size, the depth, a row pitch of
  exactly 4096 bytes (the display server draws 1024 x 4 bytes per row into consecutive
  pages), the size, and an address page-aligned, past the frame pool and below 1 GiB. A
  framebuffer that does not match but can be drawn on stops the machine, with the reason on
  it (the panic screen draws at the pitch the firmware returned); none at all leaves leanos
  running without a screen. A pixel order or alpha mode the firmware did not honor is
  reported, not refused.
  The mailbox is a DMA path, so it never leaves this layer. Lean checks the address is
  aligned and past the frame pool before any framebuffer page can be mapped (proved), but
  that the firmware really reserved those pages for the screen, and nothing else uses
  them, is trusted.

**`LeanOS/Arm.lean`**, the model of the MMU. It is about 90 lines, written to be checked
against the Arm Architecture Reference Manual (DDI 0487, chapter D8). Where it simplifies,
it claims more access for user mode than the hardware gives, never less, so the proved
bounds still hold on the real MMU.

**Hardware**: the MMU, GIC and timer behave as the Arm architecture says. So far that means
QEMU's model of them, because leanos has only run under QEMU. QEMU does not model caches,
so the cache maintenance this layer does around DMA (the mailbox, the USB controller), the
framebuffer and the cores' start has never been exercised; nor does it model the SD
controller's timing, row padding in a framebuffer, or the firmware's choices.
`docs/SETUP.md` ("First boot on a real Pi 4") lists what the first boot on a board prints
at each step. Also trusted: the Raspberry Pi firmware and its boot stub, and the
`config.txt` that `tools/mkpiimage.py` writes, which sets how the firmware loads and starts
the kernel.

## Known gaps

- **The manifest is only as trustworthy as the kernel image it is part of.** Verified boot
  here proves that leanos runs only what its own image names. Proving the image itself is
  genuine is the Raspberry Pi 4 bootloader's job in secure-boot mode (an RSA signature over
  the boot image, checked against a key hash burned into the chip's one-time-programmable
  memory). QEMU does not model that, so it is untested; and burning the key is permanent, so
  it will only be done on purpose, on a board set aside for it.

- The kernel maps the first GiB of RAM for itself, read-write and executable at EL1. User
  mode cannot touch it (proved), but a bug in the machine layer could.
- The kernel's own view of memory (EL1 permissions) is not yet modelled; only user
  mode's is.
- No protection against timing or cache side channels.
- Scheduling is proved as the kernel's choice: a live task is always picked, a task a
  wake-up chose runs next, and a ready task is picked within 18 timer interrupts
  (`timer_bounded_wait`). What a task does with its turn is its own code: that a server calls
  `recv`, or answers, is not proved. Time slices are not weighed: the round robin gives
  every ready task the same turn, and only a wake-up runs a task out of turn.
- The framebuffer is the only device memory given to a user task, and it cannot start
  DMA. Devices that can (USB, SD) will need an IOMMU-free answer on the Pi, which has
  none: their drivers will have to stay trusted or be confined by other means.
- Input in the browser: `tools/serve.py` writes the page's keys and mouse into QEMU's serial
  port. That bridge is a development tool on the host, not part of the OS; on a real Pi the
  input driver reads whatever arrives on the UART.
- Colors: the pixel order is set so QEMU shows 0x00RRGGBB correctly. A real Pi 4 may
  swap red and blue; that needs checking on hardware.
- Endpoint, interrupt and launch capabilities are fixed by the boot manifest; tasks cannot
  create or pass them yet (stage 6, next). Granted frames are taken back only when their
  owner's slot is started again; a running app cannot take back one grant on its own yet.
- Which task *runs* is proved only up to the scheduler and the machine layer's timer: a
  started app that is ready is picked within 18 timer interrupts, but nothing proves that the
  display server starts what the user clicked.
- The network stack (`user/netstack.h`, in the USB driver) is trusted C, not proved: it
  sees each network request and Terminal's buffer while it answers it, as the file server
  does. What is proved is where its memory can go: the adapter's DMA only into the driver's
  own frames (`usb_dma_own_memory`, now over `dmaOk`'s own-frames check), and what
  Terminal lends it never further (`net_server_frames`). The USB driver polls its devices
  every 8 ms instead of taking the controller's interrupt, so it can wait for requests
  with `recvt` at the same time.
- The file server decides what each program from the card may reach: its own folder
  (`apps/NAME`) and the paths Terminal, Files or Apps shared with its slot, read and/or
  write. The kernel proves who is asking (`file_server_knows_the_sender`); the rule itself
  is the file server's C (`allowed` in `user/fs.c`), trusted, not proved.
- Notes keeps to its folder by its own code. Notes (task 0) is one of the four programs the
  file server lets reach the whole card (with Terminal, Files and Apps). That it changes only
  `notes/` (and, once, moves the `notes.txt` of an older card to `notes/1.txt`) is its C
  (`user/alice.c`), trusted, not proved. It saves a note whole into `notes/N.txt.tmp` and
  puts it in place with one rename, so after a power cut the note is its last save or the
  one before (each request is whole, by the file server's journal); a `.tmp` that is there
  already is left alone, and `.tmp2` to `.tmp9` used instead. Tested by `test/notes.sh`.
- The file server is trusted with what its clients store: it can read and change any
  file, and it sees each client's buffer while it answers that client. The proofs bound
  what it can *hold* (its own frames, a client's buffer only as that client granted it,
  and its blocks of the card), not what it does with the bytes. It keeps a journal: every
  change is written to the journal with a checksum first, then to its place, so after a
  power cut a change is finished or dropped whole, and the whole tree is checked (and
  repaired, if it ever needs it) at every start. The protocol is proved atomic for a model
  (`LeanOS/Journal.lean`: `crash_atomic`); that `user/fs.c` follows the model is tested
  (`test/crash.sh`), not proved; and both assume the card writes a 512-byte block whole and in the order asked,
  which SD cards generally do but do not promise. The file server writes in runs of up to
  32 blocks, one system call and one command each: the journal's blocks in runs, then the
  commit, a single block on its own, then the blocks' places in runs, then the clear. A
  power cut in the middle of a run can leave any of its blocks written and the rest not, in
  whatever order the card took them, but never a block of a later write, since each write
  completes before the next command. That is no worse than a cut between single-block
  writes: the order that matters is between the phases, never inside one. Before the commit
  no place has been touched and recovery ignores the journal (its header is clear, or its
  checksum does not match what is there), so whichever journal blocks made it does not
  matter; after the commit, recovery writes every place again from the journal, so
  whichever places made it does not matter either. Recovery itself reads the journal whole
  and writes the places in runs; cut there, it runs again at the next start. The model in
  `LeanOS/JournalModel.lean` writes one block at a time, in order, so `crash_atomic` covers a
  torn run only through this argument, not by proof.
- What else the file server is trusted to do, tested by `test/fsfuzz.sh`, not proved: answer
  every request, whatever its words, path, offset and buffer hold, and never stop, since
  nothing can restart it; answer each with the result the protocol (`user/fs.h`) allows;
  refuse a program from the card anything outside its folder and what it was given, and say
  nothing more when it does (no size, no count, its buffer untouched); keep what each file
  holds through failed requests, a full card and restarts; and leave the card so that the
  check at the next start has nothing to repair. The test runs a fuzzer from the open slots
  (`user/progs/fsfuzz.c`). First fixed requests: every operation and numbers that are none;
  paths empty, too long, all '/', with '.', '..', a 0 or bytes outside printable ASCII
  inside, through files, into the top folder and other programs' folders (one whose name
  starts with its own); offsets and lengths at every limit, from a cluster to the double
  indirect clusters, 4 GiB, 2^63 and 2^64 - 1; buffers missing, of the wrong size or
  rights, not mapped, or not memory at all (the kernel refuses to grant those). Then the card
  filled until the file server says full, and emptied. Then random requests in its folder
  checked against a model of every file, from three programs at once, with Terminal writing
  beside them and requests for what is not theirs mixed in. Every answer must be the one
  allowed and come within 2 seconds, none may hold a secret kept outside their folders, and
  after a restart the card must check clean, with every file as the fuzzer left it and
  Notes' and Terminal's files unchanged. The seed is printed, so a run can be repeated. What
  it does not show: that its requests reach every path through the code (nothing measures
  that), or anything about power cuts, which `test/crash.sh` covers. It found four bugs, now
  fixed and kept in its fixed requests:
  - The check at every start walked folders only 32 deep. It freed what was deeper as if it
    were in no folder, but kept the entries that named it, so the next file made anywhere
    could take a freed inode and be reached through a name in another program's folder: a
    folder 34 down, after a restart, read the file Terminal had just written in the top
    folder. The check now walks a tree of any depth, in rounds, without recursion.
  - A cluster freed and given out again in the same request (a file rewritten on a card
    nearly full) was not zeroed when the request still held it in memory: past the end of
    the file, where the file then grew, its old pointers read back instead of zeros.
  - Every write asked for 4 free clusters, even one that needed none, so on a full card a
    rename, deleting an empty file or making a folder where its folder had room was refused
    as full. A write now counts only the clusters it does not have yet.
  - Making a program's folder as it starts (Terminal and Apps share `apps/NAME`) did not
    drop what a failed attempt changed in memory, as every other request does: on a full
    card the inode it took stayed taken, until a later change wrote it to the card and the
    next start repaired it.
- A request that changes something and then fails must leave the file server's copies of
  the metadata (the bitmap and the inodes) as the card holds them. The file server used to
  read them all back from the card after every change that failed, however it failed:
  about 129 blocks, 13 to 17 ms, so any program could slow the file server for everyone
  with a loop of requests that fail. It now keeps a second copy of exactly what those
  blocks hold on the card (the shadow: filled when they are read, and changed a block at a
  time only when that block's write to its place on the card went through) and copies it
  back, with the free clusters counted again: what reading the card again would give,
  about 45 microseconds in QEMU. If a write to the card failed, the shadow no longer says
  what the card holds, and the metadata is read from the card, as before. This is tested,
  not proved: `test/fsfuzz.sh` times 200 failed changes of each kind, and 200 on a full
  card, against 200 stats of the same paths, and allows them 1.5 times as long (they took
  4 to 5 times as long before; now within 10 percent); and a build that read the card after
  each of these copies and compared found no difference, through three runs of the fuzzer.
- The file server keeps 48 records of what the open slots were given (SHARE). One `run`
  could take them all by naming many files, and a program started after it got no folder.
  Each open slot may now hold 8 (its folder and 7 more), and there are 8 for each of the 6,
  so no slot can crowd out another; Terminal's `run` refuses more than 7 files and says so.
  What a slot was given is taken back when Terminal kills its program and before anything
  starts in the slot again. A program that ends by itself keeps its 8 until one of those,
  unused, since no program runs there. `test/grants.sh` refuses a run naming 20 files,
  fills all six slots twice with a program and 7 files each, kills them in a jumbled order
  (each kill takes back 8 at once), and then, with a program that ended by itself holding
  its 8, the table full, starts another in its slot that is given and reaches all it names.
- Capability lists are bounded (64 per task) but a server that is sent grants it does not
  want must drop them, from a plain send as from a call; the display server, the file
  server and the network service do. The file server did not, for a plain send (which
  it does not answer), until `test/chaos.sh` found it: a program from the card sent it 58
  grants that way, its 64 capabilities were full, and since every file request carries a
  grant, from then on no program could read or write a file, and Terminal could run
  nothing, until the machine restarted. A client that floods a server with grants between
  the server's drops is not stopped by the kernel.
- Confinement is about capabilities. A task that holds a frame can still copy its bytes
  into a message it sends, so the proofs bound what each task can *hold*, and a task on a
  grant path (the server, here) is trusted with what passes through it.
