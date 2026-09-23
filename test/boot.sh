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
  "alice: granted the server read-only capability 5 to one page of my memory -> ok" \
  "alice: sent the words 7 8 9 -> ok" \
  "alice: secret intact, exiting"

check_order mallory \
  "mallory: I am task 2" \
  "mallory: map capability 9 (not mine) at page 5 -> refused, no such capability" \
  "mallory: print 16 bytes of kernel memory at 0x80000 -> refused, not allowed" \
  "mallory: receive on the server's endpoint -> refused, not allowed" \
  "mallory: grant my data page to the server -> refused, not allowed" \
  "mallory: map the endpoint as memory -> refused, not allowed" \
  "mallory: asked for every right on the endpoint, got send" \
  "mallory: send 666 to the server -> ok" \
  "mallory: reading page 64 directly, which nobody mapped for me" \
  "leanos: mallory stopped: data access not allowed at 0x80040000"

check_order carol \
  "carol: asked for write+execute on my data frame, got -w-" \
  "carol: jumping into the instruction I wrote in my data page" \
  "leanos: carol stopped: instruction fetch not allowed at 0x80010000"

# The server's three messages may arrive in any order; each must arrive exactly once.
server=$(echo "$out" | grep -E "^server: ")
[ "$(echo "$server" | head -1)" = "server: waiting for messages" ] || fail "server did not start"
[ "$(echo "$server" | tail -1)" = "server: done" ] || fail "server did not finish"
for line in \
  "server: from badge 1: 44 0 0, with a capability to 1 page (r--); mapped at page 100, it says: a page alice drew into and shared, read-only" \
  "server: from badge 2: 666 0 0" \
  "server: from badge 1: 7 8 9"; do
  [ "$(echo "$server" | grep -cxF "$line")" = 1 ] || fail "server line missing or repeated: $line"
done
[ "$(echo "$server" | wc -l | tr -d ' ')" = 5 ] || fail "server printed unexpected lines"

echo "$out" | grep -q "^leanos: every task has finished" || fail "did not finish"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: boot transcript matches"
