#!/bin/bash
# A program larger than one file-server request: big (user/progs/big.c) carries a 40 KiB
# table, on a card of its own. Terminal loads it piece by piece and it must sum its table
# to the value it was built with; a file of 250 KiB is written, moved into a folder, read
# back whole, and survives a restart.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/big.elf || fail "big did not build"
card=build/sd-big.img
python3 tools/mksd.py $card big=build/progs/big.elf || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run big\r"), wait_for("big: "),
         *keys("mkdir keep\r"), wait_for("terminal: mkdir"),
         *keys("fill keep/huge 250 q\r"), wait_for("terminal: fill"),
         *keys("verify keep/huge\r"), wait_for("terminal: verify")]
boot(90, steps=steps, until="terminal: verify", sd=card)
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("cd keep\r"), wait_for("terminal: cd"),
         *keys("verify huge\r"), wait_for("terminal: verify")]
boot(90, steps=steps, until="terminal: verify", sd=card)
PY
)
echo "$out" | grep -E "^(big|terminal: (run|fill|verify|cd|mkdir)|fs: (ready|checked|repaired))" | sed 's/^/  | /'
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "big: 40960 bytes of table, sum 5228827, as built" || fail "big did not load whole"
[ "$(echo "$out" | grep -cx "terminal: verify keep/huge -> 256000 bytes of 'q'\|terminal: verify huge -> 256000 bytes of 'q'")" = 2 ] \
  || fail "the 250 KiB file did not read back whole, before and after a restart"
echo "$out" | grep -q "fs: repaired" && fail "the card needed repairs"
echo "ok: a 41 KiB program loads piece by piece, and a 250 KiB file in a folder reads back whole after a restart"
