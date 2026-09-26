#!/bin/bash
# Stopping a program: Terminal runs clock from the card, then `kill 10` stops it (the kernel's
# stop, through Terminal's launch capability for slot 10), whether it answers or not; the
# display server takes its window back. Killing it again finds nothing, and Terminal cannot
# stop anything but the open slots.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run clock\r"), wait_for("clock: opened"), *wclick("Terminal", 230, 150),
         *keys("kill 10\r"), wait_for("terminal: kill"), *keys("kill 10\r"), wait_for("terminal: kill", 2),
         *keys("kill 3\r"), wait_for("terminal: kill", 3), *keys("ps\r"), wait_for("terminal: ps")]
sys.exit(boot(90, steps=steps, until="terminal: ps", settle=0.5))
PY
)
status=$?
echo "$out" | grep -E "^(terminal: (run|kill|ps)|clock: opened|display: .*gone)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "terminal: kill 10 -> stopped" || fail "kill did not stop clock"
echo "$out" | grep -qx "display: a program from the SD card stopped; its window is gone" || fail "the window stayed"
echo "$out" | grep -qx "terminal: kill 10 -> nothing running" || fail "a stopped slot was stopped again"
echo "$out" | grep -qx "terminal: kill 3 -> not an open slot" || fail "kill reached past the open slots"
echo "$out" | grep -qx "terminal: ps -> 5 running" || fail "ps still counts the stopped program"
echo "ok: kill stops a program from the card, and its window goes with it"
