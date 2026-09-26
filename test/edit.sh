#!/bin/bash
# The editor from the card, given one file: Terminal writes memo.txt, runs `edit memo.txt`
# (which gives edit that file and its own folder, nothing else), types into it, and the
# change is saved by itself; Terminal reads it back. Then edit, given nothing, opens a new
# file in its own folder, apps/edit.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
term = wclick("Terminal", 230, 150)     # in Terminal's window, where edit's does not cover it
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("write memo.txt hello\r"), wait_for("terminal: write"),
         *keys("run edit memo.txt\r"), wait_for("edit: opened a window"),
         *keys("Say "), wait_for("edit: saved"),
         *term, *keys("cat memo.txt\r"), wait_for("terminal: cat"),
         *keys("ls apps\r"), wait_for("terminal: ls")]
sys.exit(boot(90, steps=steps, until="terminal: ls apps", settle=0.5))
PY
)
status=$?
echo "$out" | grep -E "^(edit|terminal: (write|run|gave|cat|ls)|fs: refused)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "terminal: gave edit memo.txt -> ok" || fail "Terminal did not give edit the file"
echo "$out" | grep -qx "edit: opened memo.txt (5 bytes)" || fail "edit did not open the file it was given"
echo "$out" | grep -qx "edit: saved memo.txt (9 bytes)" || fail "edit did not save"
echo "$out" | grep -qx "terminal: cat memo.txt -> 9 bytes" || fail "the saved file did not read back"
echo "$out" | grep -qx "terminal: ls apps -> 1 file" || fail "edit's own folder was not made"
echo "ok: edit opens only the file it was given, saves it by itself, and has a folder of its own"
