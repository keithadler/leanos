#!/bin/bash
# The fuzzer on the card (user/progs/fuzz.c): 20,000 system calls with made-up arguments
# from an open slot, every answer checked against the proofs. Afterwards the rest of the
# system must still work: the display server takes a new window, the file server a file.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
# fuzz from the Apps window's grid: the eighth program on the card, second row, third column
steps = [*click(*DOCK["Apps"]), wait_for("apps: opened"), *click(376, 426), wait_for("fuzz: opened"),
         wait_for("fuzz: 20000 calls", 1),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("write after.txt still here\r"), wait_for("terminal: write"),
         *click(*DOCK["Settings"]), wait_for("settings: opened")]
sys.exit(boot(240, steps=steps, until="settings: opened", settle=1))
PY
)
status=$?
echo "$out" | grep -E "^(fuzz|apps: fuzz|terminal: (run|write)|settings: opened|display: a program from the SD card (sent|keeps|may not))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "^fuzz: 20000 calls, 20000 answered as promised, 0 not$" || fail "the fuzzer found a broken promise"
echo "$out" | grep -qE "^terminal: write after.txt -> ok" || fail "the file server stopped answering"
echo "$out" | grep -qx "display: a program from the SD card keeps sending requests it cannot make; ignoring them quietly" || fail "the display did not quiet the flood"
[ "$(echo "$out" | grep -c "^display: a program from the SD card \(sent\|keeps\|may not\)")" -le 6 ] || fail "the flood reached the log"
echo "ok: 20,000 made-up system calls, every answer as the proofs promise, and the system still works"
