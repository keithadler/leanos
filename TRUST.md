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
`LeanOS/Proofs.lean`.

Tasks can hand each other memory, so the central guarantee is about where memory can go.
The boot manifest (`initCaps` in `Kernel.lean`) fixes which task can send with the grant
right to which (`Edge`). Endpoint capabilities themselves never move.

| Theorem | Statement |
|---|---|
| `frame_flow` | A task holds a frame only if a chain of grant edges leads to it from the frame's owner at boot, and never with more rights than the owner had. |
| `endpoints_fixed` | Endpoint capabilities never gain rights and keep their badge, so no task can forge who it is. |
| `edge_iff`, `reach_iff` | In the manifest the only grant edges are from the apps (Notes, Terminal, Settings, Security, Files) to the display server, and from Notes, Terminal and Files to the file server. Memory moves at most one step: neither server can pass on what it was given. |
| `confined` | Every task but the two servers only ever holds its own 256 frames. (`mallory_confined`, `carol_confined`, `alice_confined` are the same for those three.) |
| `server_frames`, `file_server_frames` | The display server holds only its own frames, the framebuffer, and frames the apps granted it; the file server, only its own frames and frames its clients granted it. |
| `blocks_fixed`, `disk_only_file_server` | Block capabilities never move and never gain rights: only the file server ever holds one, for the manifest's 2048 blocks. |
| `block_io_confined` | When a call asks the machine layer for block I/O, the block is inside a block capability the caller holds with the right it needs, and the 512 bytes are in the user window, in one page the caller has mapped writable (a read fills it) or readable (a write sends it). |
| `drop_only_shrinks` | After `drop`, every task holds a subset of the capabilities and mappings it held before. |
| `maps_backed` | Every page a task can see comes from one of its own capabilities, with that capability's rights. |
| `no_write_execute` | No page is ever both writable and executable. |
| `maps_in_range` | Every mapping is inside the 8192-page user window and the frame pool. |
| `derive_never_amplifies` | A derived capability covers only frames its parent covers (or names the same endpoint), keeps its badge, and allows nothing the parent does not. |
| `write_reads_only_readable` | When `write` asks the machine layer to print user memory, every byte is in a page the calling task has mapped readable. |
| `schedule_picks_ready` | If any task is ready, the scheduler picks a ready task. |
| `reply_grants_nothing` | A reply changes no task's capabilities or mappings. |
| `reply_wakes_only_caller` | A reply wakes only a task waiting for this replier. |
| `only_verified_runs` | Every task that can run in a manifest slot was loaded with exactly the code and assets the manifest names. The two open slots (10, 11) run whatever program Terminal starts them with; that program is measured and shown, and holds only what the manifest gives the slot. |
| `verify_refuses_mismatch` | A task in a manifest slot whose measurement differs from the manifest is stopped for good. |
| `exec_reads_only_readable` | When a program image is loaded, the slot is an open slot, the image is at most 64 KiB, and every byte comes from a page the loader has mapped readable (in its address space as it is after the start). |
| `irqs_fixed` | Interrupt capabilities never move: a task holds one only if it held it at boot. |
| `tick_wakes_only_sleepers` | If a timer tick changes a task's status, the task was asleep until at most that tick, and is now ready. |
| `irq_wakes_holder` | An interrupt wakes only a task given that interrupt's capability at boot. |
| `uart_confined`, `uart_irq_only_input` | Only the input driver can ever hold the UART's registers or its interrupt. |
| `start_revokes` | When `start` has the machine layer load slot `k`, the slot holds the manifest's fresh, unverified task, and no other task holds a capability to or a mapping of any of the slot's frames, is waiting to send a message granting one, or holds a reply slot for the old run. |
| `launch_fixed`, `only_display_launches` | Launch capabilities never move: only the display server starts the manifest's apps, and only Terminal starts the open slots. Nothing can restart the display server, the input driver, the file server or the tests. |

Revocation rests on one more invariant: every run of frames a task holds stays inside one
slot's memory (`RunOK`), so taking back the runs that start in a slot takes back exactly
that slot's frames and nothing else.

And down to the hardware, in `LeanOS/Tables.lean`. The Lean kernel computes every
translation-table word. If the machine layer stores those words (the `Installed`
hypotheses), then under the MMU model in `LeanOS/Arm.lean`:

| Theorem | Statement |
|---|---|
| `walk_eq_view` | For every virtual address, what user mode may do there is exactly what the task's mappings say, and nothing outside the 32 MiB user window. |
| `physOf_inj` | Different frames are different physical pages: the framebuffer never overlaps the pool. |
| `el0_no_write_execute` | No address user mode can reach is both writable and executable. |
| `el0_flow`, `el0_shared` | A physical page user mode can reach came along grant edges from its owner; two tasks share a page only if one owner reaches both. |
| `el0_mallory_isolated` | mallory's user mode never reaches a page any other task can reach. |
| `el0_only_pool_fb_uart` | User mode reaches only the frame pool, the framebuffer and the UART's page. |
| `el0_uart_only_input` | Only the input driver's user mode can touch the UART's registers. |

`make mutants` breaks the kernel in 59 specific ways (a `derive` that amplifies, forges a
badge or cuts past the end of a run, a send without the grant right, an endpoint granted like a frame, a manifest that
gives mallory one more right, the framebuffer or a launch capability, a framebuffer address that overlaps the
pool, a kernel page-table entry missing its execute-never bit, a `start` that forgets to take back
mappings, capabilities, waiting grants or reply slots, and so on) and checks that the proofs reject every one.

`make test` checks that each theorem rests only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and never on `sorry`.

## Trusted, not proved

Each item below is assumed correct. A bug in any of them could break a guarantee even
though every proof checks.

**Tools**
- Lean's kernel, which checks the proofs.
- Lean's compiler, which turns `Kernel.lean` into C. The proofs are about the Lean
  definitions, and this compiler is what makes the running code match them.
- The C that the same compiler generates for the six standard-library modules the kernel
  imports (`Init.Prelude`, `Coe`, `Notation`, `SizeOf`, `Tactics`, `Core`).
- clang and ld.lld.

**`rt/runtime.c` (~440 lines)**: the part of Lean's runtime compiled code needs, rewritten
for bare metal: allocator, reference counting, closures, arrays. Its limits:
- Numbers must stay below 2^63. A larger one stops the machine and never gives a wrong
  answer. Two standard-library constants (`UInt64.size`, `USize.size`) are built at
  startup as opaque placeholders, and any arithmetic on one stops the machine.
- Single core only.
- The heap has a fixed size. A task deriving capabilities up to the limit of 64 each can
  use kernel memory but cannot exhaust it. If the heap runs out, the kernel panics, which
  denies service but never breaks isolation.

**`arch/boot.S` and `arch/kmain.c` (~800 lines)**
- Storing the tables: `mmu_init`, `tables_init` and `build_user_pages` must store each
  word Lean computes at its index, in the page-aligned arrays whose addresses they pass to
  Lean (a level-1 table, a level-2 table, and 16 level-3 tables in one array). This is exactly the `Installed` hypothesis. The kernel is identity-mapped,
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
- User arguments at or above 2^62 are clamped to 2^62 before reaching Lean. Every system
  call rejects values that large, so the clamp never changes an outcome, but that is
  argued here, not proved.
- Interrupts stay masked while the kernel runs, so the Lean kernel is never re-entered.
- Interrupt routing: `irq_init` enables exactly the lines Lean lists (`irqLines`); when one
  fires, `handle_irq` masks it before telling Lean, and unmasks it only when a Reply says
  so (an acknowledge from the capability's holder).
- The idle loop waits for interrupts with WFI when no task is ready.
- Measurement: `measure_and_verify` hashes exactly the bytes each task will run from (its
  code, then its assets, where they sit in its own frames) with SHA-256 (`arch/sha256.c`,
  checked against the FIPS 180-4 test vector at every boot) and hands the digest to Lean.
  Lean decides; `only_verified_runs` holds whatever digest it is given.
- Assets: `load_program` copies each task's asset blob (fonts and icons, built by
  `tools/mkassets.py`) into the start of that task's own spare run, next to its code. The
  blob is data the task reads; it grants nothing.
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
- The SD card (`arch/sd.c`, ~160 lines): an SDHCI driver by programmed I/O only, never
  DMA, because the controller can be told to write anywhere in physical memory. It must
  move exactly the 512 bytes at the address a Reply names, to or from exactly the block it
  names, while the calling task's address space is live; `block_io_confined` says those
  are allowed, this code must do nothing else. A failed transfer is reported to Lean
  (`ioFailed`, a reachable transition), which gives the caller an I/O error. Tested only on
  QEMU, where the card sits on the older EMMC controller; the Pi 4's slot is on EMMC2, which
  may need more setup (clock, 1.8 V signaling) than this does.
- The kernel stack: the Lean kernel recurses once per list element, and nothing proves a
  bound. The stack is sized for the largest lists the proofs allow (2 MiB for 8192
  mappings), painted at boot, and its bottom is checked on every return to user mode, so
  an overflow stops the machine instead of corrupting kernel memory silently.
- User mode may read the processor's virtual counter (CNTKCTL_EL1.EL0VCTEN), for
  animations and timeouts. This gives no new power: a task could already time itself by
  counting loops. Timing side channels remain out of scope.

- The framebuffer: `fb_alloc` asks the firmware for 1024 x 600 x 32 through the mailbox,
  once at boot, and passes the address to Lean only if the reply matches the request.
  The mailbox is a DMA path, so it never leaves this layer. Lean checks the address is
  aligned and past the frame pool before any framebuffer page can be mapped (proved), but
  that the firmware really reserved those pages for the screen, and nothing else uses
  them, is trusted.

**`LeanOS/Arm.lean`**, the model of the MMU. It is about 90 lines, written to be checked
against the Arm Architecture Reference Manual (DDI 0487, chapter D8). Where it simplifies,
it claims more access for user mode than the hardware gives, never less, so the proved
bounds still hold on the real MMU.

**Hardware**: the MMU, GIC and timer behave as the Arm architecture says. So far that means
QEMU's model of them, because leanos has only run under QEMU.

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
- Only one scheduling property is proved (a live task is always picked). Fairness is not.
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
- Which task *runs* is proved only up to the scheduler: nothing proves that a started app
  eventually gets to run, or that the display server starts what the user clicked.
- The file server is trusted with what its clients store: it can read and change any
  file, and it sees each client's buffer while it answers that client. The proofs bound
  what it can *hold* (its own frames, a client's buffer only as that client granted it,
  and its blocks of the card), not what it does with the bytes. Writes go straight through
  to the card, data then table, but a power cut in between can lose the last change: there
  is no journal yet.
- Capability lists are bounded (64 per task) but a server that is sent grants it does not
  want must drop them; the display server and the file server do. A client that floods a
  server with grants between the server's drops is not stopped by the kernel.
- Confinement is about capabilities. A task that holds a frame can still copy its bytes
  into a message it sends, so the proofs bound what each task can *hold*, and a task on a
  grant path (the server, here) is trusted with what passes through it.
