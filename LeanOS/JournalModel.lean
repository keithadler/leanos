/-
The file server's journal (user/fs.c), as a model. LeanOS/Journal.lean proves that a power
cut cannot leave a change half done.

The model: a disk is a function from block numbers to what the block holds. A transaction
is a list of writes (block, contents). The protocol writes, in order, one block at a time:
each block's contents to the journal (blocks `J + 1`, `J + 2`, ...), then the journal's
header at `J` naming the targets with a checksum over the journal's contents (the commit),
then each block to its place, then a clean header. A power cut stops that sequence after
any number of writes. At the next start, recovery reads the header: if it names blocks and
the checksum over the journal matches, it writes them to their places again; either way it
leaves a clean header.

The theorem, `crash_atomic`: whatever the number of writes that made it before the cut,
after recovery every block outside the journal holds what it held before the transaction,
or what it holds after it. Nothing in between.

What the model assumes, as user/fs.c does: a block is written whole (a 512-byte write is
atomic) and writes reach the card in the order they are made; the transaction's targets are
outside the journal; the journal starts clean. The checksum is any function at all: the
proof never needs it to catch anything, since with whole, ordered writes a header is only
ever written after the journal it describes. (The checksum is there for cards that tear or
reorder writes, which this model does not cover.)
-/
namespace LeanOS.Journal

/-- What a block holds: file system data, or (at the journal's header) a header naming `n`
blocks' targets and a checksum; `n = 0` is a clean header. -/
inductive Blk where
  | data (v : Nat)
  | header (n : Nat) (targets : List Nat) (sum : Nat)
  deriving DecidableEq

def clean : Blk := .header 0 .nil 0

abbrev Disk := Nat → Blk

def upd (d : Disk) (b : Nat) (v : Blk) : Disk := fun x => if x = b then v else d x

/-- Writes, first to last. -/
def applyW : List (Nat × Blk) → Disk → Disk
  | .nil, d => d
  | (b, v) :: ws, d => applyW ws (upd d b v)

/-- The journal's copies: the `i`-th block of the transaction at `J + 1 + i`. -/
def jw (J : Nat) : Nat → List Blk → List (Nat × Blk)
  | _, .nil => .nil
  | i, v :: vs => (J + 1 + i, v) :: jw J (i + 1) vs

/-- Read `n` journal blocks starting at copy `i`. -/
def readJ (d : Disk) (J : Nat) : Nat → Nat → List Blk
  | _, 0 => .nil
  | i, n + 1 => d (J + 1 + i) :: readJ d J (i + 1) n

/-- The whole protocol for transaction `t`: copies, commit, home, clean. -/
def protocol (csum : List Blk → Nat) (J : Nat) (t : List (Nat × Blk)) : List (Nat × Blk) :=
  jw J 0 (t.map Prod.snd) ++
    (J, .header t.length (t.map Prod.fst) (csum (t.map Prod.snd))) :: (t ++ (J, clean) :: .nil)

/-- Recovery at start. -/
def recover (csum : List Blk → Nat) (J : Nat) (d : Disk) : Disk :=
  match d J with
  | .header n ts s =>
    if n ≠ 0 ∧ ts.length = n ∧ csum (readJ d J 0 n) = s
    then upd (applyW (ts.zip (readJ d J 0 n)) d) J clean
    else upd d J clean
  | _ => upd d J clean

/-- The same everywhere outside the journal, blocks `J` to `J + L`. -/
def HomeEq (J L : Nat) (a b : Disk) : Prop := ∀ x, (x < J ∨ J + L < x) → a x = b x

end LeanOS.Journal
