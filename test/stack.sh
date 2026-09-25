#!/bin/bash
# The kernel stack at its worst: deep (user/progs/deep.c), on a card of its own, maps all
# 8192 pages of its window and makes the kernel walk every one of those mappings with
# nothing to take out (a map, an unmap, a drop); then hello starts in another slot, and
# taking back that slot's frames walks them again. The Lean kernel's walks are loops
# (the `@[csimp]` theorems in LeanOS/Kernel.lean), so the stack must stay far below its
# size however long the lists get. The peak is what the kernel reports when it switches off.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/deep.elf build/progs/hello.elf || fail "deep did not build"
card=build/sd-deep.img
python3 tools/mksd.py $card deep=build/progs/deep.elf hello=build/progs/hello.elf || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run deep\r"), wait_for("deep: "),
         *keys("run hello\r"), wait_for("hello: opened"),
         *click(40, 15), *click(60, 80), wait_for("leanos: switched off")]
sys.exit(boot(240, steps=steps, sd=card))
PY
)
status=$?
echo "$out" | grep -E "^(deep|hello|terminal: run|leanos: (idle|switched off))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "deep: all 8192 pages mapped, 0 calls refused" || fail "deep did not map its whole window"
echo "$out" | grep -q "^hello: opened a window" || fail "hello did not start after deep"
peak=$(echo "$out" | sed -n 's/^leanos: switched off (.* stack \([0-9]*\) bytes peak.*/\1/p')
[ -n "$peak" ] || fail "no stack peak reported"
# The stack is 64 KiB (arch/kmain.c, STACK_SIZE); the walks must leave most of it unused.
[ "$peak" -le 32768 ] || fail "the kernel stack reached $peak bytes with 8192 mappings"
echo "ok: 8192 mappings walked end to end, kernel stack peak $peak bytes"
