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

These hold for every state the kernel can reach: `init n`, then any sequence of system
calls with any arguments, timer ticks and faults. They are all in `LeanOS/Proofs.lean`.

| Theorem | Statement |
|---|---|
| `isolation` | No physical frame appears in two different tasks' address spaces. |
| `caps_isolated` | No two tasks hold capabilities to the same frame. |
| `maps_backed` | Every page a task can see comes from one of its own capabilities, with that capability's rights. |
| `no_write_execute` | No page is ever both writable and executable. |
| `maps_in_range` | Every mapping's page number is inside the 512-page user window and its frame is inside the frame pool. |
| `derive_never_amplifies` | A derived capability names its parent's frame and allows nothing the parent does not. |
| `write_reads_only_readable` | When `write` asks the machine layer to print user memory, every byte is in a page the calling task has mapped readable. |
| `schedule_picks_alive` | If any task is alive, the scheduler picks a live task. |

And down to the hardware, in `LeanOS/Tables.lean`. The Lean kernel computes every
translation-table word. If the machine layer stores those words (the `Installed`
hypotheses), then under the MMU model in `LeanOS/Arm.lean`:

| Theorem | Statement |
|---|---|
| `walk_eq_view` | For every virtual address, what user mode may do there is exactly what the task's mappings say, and nothing outside the 2 MiB user window. |
| `el0_only_frame_pool` | User mode can reach only the frame pool: never the kernel image, heap, tables or peripherals. |
| `el0_no_write_execute` | No address user mode can reach is both writable and executable. |
| `el0_isolation` | Two tasks never reach the same physical page. |

`make mutants` breaks the kernel in nine specific ways (a `derive` that amplifies, a
`write` that skips its check, a kernel entry missing its execute-never bit, and so on) and
checks that the proofs reject every one.

`make test` checks that each of these rests only on Lean's standard axioms (`propext`,
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
  word Lean computes at its index, in the three page-aligned arrays whose addresses they
  pass to Lean. This is exactly the `Installed` hypothesis. The kernel is identity-mapped,
  so those addresses are physical. TTBR0 must point at the task's level-1 table, and the
  TLB must be invalidated after every change (`tlb_flush_all`).
- MMU configuration: TCR_EL1 and SCTLR_EL1 must be set as `LeanOS/Arm.lean` assumes (4 KiB
  granule, T0SZ = 25, EPD1 = 1, WXN = 0). `mmu_init` sets each of these explicitly.
- Trap entry and exit, the saved-register copy, and the switch between address spaces
  (TTBR0, with one ASID per task).
- `do_syscall` reads the buffer for `write` while the calling task's address space is
  still active. The proof covers which pages may be read. That the read happens in the
  right address space is this code's job.
- User arguments at or above 2^62 are clamped to 2^62 before reaching Lean. Every system
  call rejects values that large, so the clamp never changes an outcome, but that is
  argued here, not proved.
- Interrupts stay masked while the kernel runs, so the Lean kernel is never re-entered.

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
- No devices are given to user tasks, so DMA isolation is not addressed yet.
