#!/bin/bash
# A program may not take another's name. The display server names a window after the file
# its program was run from, and `run`, Apps and the dock's pinned programs look for that
# name: a window named clock is brought forward instead of starting Clock. The name comes
# from four pages of the program's code run, which the loader wrote and nothing can write
# (user/display.c, on_icon; user/elf.h, image_marked).
#
#   1. spoof (user/progs/spoof.c), from Terminal, opens two windows and lends the display a
#      forged icon named clock from every run it can write: its spare pages (read-only,
#      read-write, and asking for the execute right), its data pages and its stack; then its
#      code run without the execute right, and with it from pages the loader did not write.
#      Every claim must be refused, and nothing named clock. Then the pages the loader wrote,
#      as app_open lends them: its own name, which the display must take.
#   2. forge (user/progs/forge.c), whose code run carries a forged icon named clock at the
#      start of a page: Terminal must refuse to run it.
#   3. Clock in the dock must start the real Clock (through Apps), and `run clock` must then
#      find it by its name (the real one has it); after `kill`, `run clock` starts it again.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/spoof.elf build/progs/forge.elf build/progs/clock.elf build/icons/clock.icon \
  || fail "the programs did not build"
card=$T/sd-spoof.img
python3 tools/mksd.py "$card" spoof=build/progs/spoof.elf forge=build/progs/forge.elf \
  clock=build/progs/clock.elf clock.icon=build/icons/clock.icon >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
from collections import Counter
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
front = click(*DOCK["Terminal"])        # a program's new window takes focus: give it back to Terminal
seen = Counter()
def cmd(line, done):
    seen[done] += 1                     # the same command again waits for its next line
    return [*front, (line + "\r").encode(), wait_for(done, seen[done])]
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *cmd("run spoof", "spoof: done"),
         *cmd("run forge", "terminal: run forge"),
         *click(*DOCK["Clock"]), wait_for("clock: opened"),
         *cmd("run clock", "terminal: run clock"),
         *cmd("kill 11", "terminal: kill 11"),
         *cmd("run clock", "terminal: run clock"), wait_for("clock: opened", 2),
         *cmd("ps", "terminal: ps")]
sys.exit(boot(90, steps=steps, until="terminal: ps", sd=sys.argv[1], settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(spoof|forge|clock: opened|apps: clock|terminal: (run|kill)|display: (open clock|clock is))" | sed 's/^/  | /'
# every check, so a failing run says all that went wrong
failed=0
fail() { echo "FAIL: $*"; failed=1; }
has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }

# 1. every forged claim refused, each with the rights its capability really has
took=$(echo "$out" | grep "^spoof: .*: taken$" | grep -v "^spoof: its own name from its code run, read and execute (r-x): taken$" | head -1)
[ -z "$took" ] || fail "a program took a name that is not its own: $took"
has "spoof: opened 2 windows"
has "spoof: clock from its spare pages, read-only (r--): refused"
has "spoof: clock from its spare pages, read-write (rw-): refused"
has "spoof: clock from its spare pages, asking for execute (r--): refused"
has "spoof: clock from its data pages (r--): refused"
has "spoof: clock from its stack (r--): refused"
has "spoof: its own name from its code run, read-only (r--): refused"
has "spoof: its code run from page 0, no marker (r-x): refused"
has "spoof: claims refused: 7 of 7; no window named clock"
# the pages the loader wrote, lent as app_open lends them, still name its window
has "spoof: its own name from its code run, read and execute (r-x): taken"
has "spoof: done: its own name taken, and found by name"
# 2. a code run with a marker of its own is not run
echo "$out" | grep -q "^forge: ran" && fail "a program with a forged icon in its code run was run: $(echo "$out" | grep "^forge: ran")"
has "terminal: run forge -> has an icon marker of its own (only the loader writes one)"
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
# 3. the dock's Clock starts the real one, which then has the name
echo "$out" | grep -qx "display: open clock from the dock" \
  || fail "clicking Clock in the dock did not start Clock (another window named clock came forward?)"
has "apps: clock started in slot 11"
has "terminal: run clock -> already open"
echo "$out" | sed -n '/^apps: clock started/,$p' | grep -qx "display: clock is already open; brought it to the front" \
  || fail "run clock did not find the real Clock by its name"
has "terminal: kill 11 -> stopped"
[ "$(echo "$out" | grep -c "^terminal: run clock -> slot 11")" = 1 ] || fail "run clock did not start Clock again after kill"
[ "$(echo "$out" | grep -cx "clock: opened a window -> ok")" = 2 ] || fail "the real Clock did not open twice"
[ $failed = 0 ] || exit 1
echo "ok: 7 forged claims to the name clock refused (spare, data and stack pages, the code run without execute or without the loader's marker), a forged code run not run; the dock's Clock and run clock start and find the real Clock"
