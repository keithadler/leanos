#!/bin/bash
# Boots leanos in QEMU and checks the transcript: every line below must appear, in order
# within each task, and the machine must power itself off.
set -u
cd "$(dirname "$0")/.."

fail() { echo "FAIL: $*"; exit 1; }

# Axioms: only Lean's standard three, and never sorryAx.
axioms=$(lake env lean test/Axioms.lean 2>&1) || fail "axiom check did not run: $axioms"
echo "$axioms" | grep -q sorryAx && fail "a theorem depends on sorry"
echo "$axioms" | grep -v "depends on axioms: \[\(propext\|Classical.choice\|Quot.sound\)\(, \(propext\|Classical.choice\|Quot.sound\)\)*\]" \
  | grep -q . && fail "unexpected axiom: $axioms"
echo "ok: $(echo "$axioms" | wc -l | tr -d ' ') theorems rest only on Lean's standard axioms"

out=$(timeout 30 qemu-system-aarch64 -M raspi4b \
  -nographic -semihosting -kernel build/kernel8.img 2>&1 | tr -d '\r')
status=$?
echo "$out" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "QEMU did not power off cleanly (status $status)"

# Each task's lines must appear in this order; tasks may interleave with each other.
check_order() {
  local who=$1; shift
  local got
  got=$(echo "$out" | grep -E "^($who: |leanos: $who )")
  local expected
  expected=$(printf '%s\n' "$@")
  [ "$got" = "$expected" ] || { echo "expected for $who:"; echo "$expected"; echo "got:"; echo "$got"; fail "$who"; }
}

check_order alice \
  "alice: wrote secret 0x5ec12e7 to my data page" \
  "alice: still working, round 1" \
  "alice: still working, round 2" \
  "alice: still working, round 3" \
  "alice: secret intact, exiting"

check_order bob \
  "bob: I am task 1" \
  "bob: map capability 9 (not mine) at page 5 -> refused, no such capability" \
  "bob: print 16 bytes of kernel memory at 0x80000 -> refused, bad argument" \
  "bob: print from page 7, which I have not mapped -> refused, bad argument" \
  "bob: asked for rwx on my data frame, got capability 4 with rw-" \
  "bob: map my spare frame (capability 3) at page 2 -> ok" \
  "bob: wrote and read back 42 through page 2" \
  "bob: now reading page 3 directly, which is not mapped" \
  "leanos: bob stopped: data access not allowed at 0x80003000"

check_order carol \
  "carol: asked for write+execute on my data frame, got -w-" \
  "carol: jumping into the instruction I wrote in my data page" \
  "leanos: carol stopped: instruction fetch not allowed at 0x80001000"

echo "$out" | grep -q "^leanos: every task has finished" || fail "did not finish"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: boot transcript matches"
