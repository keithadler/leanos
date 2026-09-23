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
with any arguments, timer ticks, faults, and result loads. They are in
`LeanOS/Proofs.lean`.

Tasks can hand each other memory, so the central guarantee is about where memory can go.
The boot manifest (`initCaps` in `Kernel.lean`) fixes which task can send with the grant
right to which (`Edge`). Endpoint capabilities themselves never move.

| Theorem | Statement |
|---|---|
| `frame_flow` | A task holds a frame only if a chain of grant edges leads to it from the frame's owner at boot, and never with more rights than the owner had. |
| `endpoints_fixed` | Endpoint capabilities never gain rights and keep their badge, so no task can forge who it is. |
| `edge_iff` | In the demo manifest the only grant edge is alice to the server. |
| `mallory_confined`, `carol_confined`, `alice_confined` | Each of these tasks only ever holds its own 64 frames. |
| `server_frames` | The display server holds only its own frames, the framebuffer, and alice's. |
| `maps_backed` | Every page a task can see comes from one of its own capabilities, with that capability's rights. |
| `no_write_execute` | No page is ever both writable and executable. |
| `maps_in_range` | Every mapping is inside the 8192-page user window and the frame pool. |
| `derive_never_amplifies` | A derived capability covers only frames its parent covers (or names the same endpoint), keeps its badge, and allows nothing the parent does not. |
| `write_reads_only_readable` | When `write` asks the machine layer to print user memory, every byte is in a page the calling task has mapped readable. |
| `schedule_picks_ready` | If any task is ready, the scheduler picks a ready task. |

And down to the hardware, in `LeanOS/Tables.lean`. The Lean kernel computes every
translation-table word. If the machine layer stores those words (the `Installed`
hypotheses), then under the MMU model in `LeanOS/Arm.lean`:

| Theorem | Statement |
|---|---|
| `walk_eq_view` | For every virtual address, what user mode may do there is exactly what the task's mappings say, and nothing outside the 32 MiB user window. |
| `el0_only_pool_or_fb` | User mode can reach only the frame pool and, if the firmware's address for it is sane, the framebuffer: never the kernel image, heap, tables or peripherals. |
| `physOf_inj` | Different frames are different physical pages: the framebuffer never overlaps the pool. |
| `el0_no_write_execute` | No address user mode can reach is both writable and executable. |
| `el0_flow`, `el0_shared` | A physical page user mode can reach came along grant edges from its owner; two tasks share a page only if one owner reaches both. |
| `el0_mallory_isolated` | mallory's user mode never reaches a page any other task can reach. |

`make mutants` breaks the kernel in 24 specific ways (a `derive` that amplifies, forges a
badge or cuts past the end of a run, a send without the grant right, an endpoint granted like a frame, a manifest that
gives mallory one more right or the framebuffer, a framebuffer address that overlaps the
pool, a kernel page-table entry missing its execute-never bit, and so on) and checks that the proofs reject every one.

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

**`arch/boot.S` and `arch/kmain.c` (~530 lines)**
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

- The framebuffer: `fb_alloc` asks the firmware for 640 x 480 x 32 through the mailbox,
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

- The kernel maps the first GiB of RAM for itself, read-write and executable at EL1. User
  mode cannot touch it (proved), but a bug in the machine layer could.
- The kernel's own view of memory (EL1 permissions) is not yet modelled; only user
  mode's is.
- No protection against timing or cache side channels.
- Only one scheduling property is proved (a live task is always picked). Fairness is not.
- The framebuffer is the only device memory given to a user task, and it cannot start
  DMA. Devices that can (USB, SD) will need an IOMMU-free answer on the Pi, which has
  none: their drivers will have to stay trusted or be confined by other means.
- Colors: the pixel order is set so QEMU shows 0x00RRGGBB correctly. A real Pi 4 may
  swap red and blue; that needs checking on hardware.
- Endpoint capabilities are fixed by the boot manifest; tasks cannot create or pass them
  yet (stage 5). Granted frames cannot be revoked yet.
- Confinement is about capabilities. A task that holds a frame can still copy its bytes
  into a message it sends, so the proofs bound what each task can *hold*, and a task on a
  grant path (the server, here) is trusted with what passes through it.
