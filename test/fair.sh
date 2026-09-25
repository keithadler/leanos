#!/bin/bash
# Receiving is fair (LeanOS/Fair.lean): a server takes waiting messages in turn, round robin
# from the task it served last, so programs in low slots that keep it busy cannot starve one
# in a higher slot. Before, a receive took the lowest-numbered sender waiting, and this test
# found no progress at all for the program in the higher slot.
#
#   1. The file server: chaos (user/progs/chaos.c) runs as `files`, file rounds back to
#      back, in slots 10 and 11, so the file server always has a request waiting. Then a
#      third starts in slot 12: it must finish 4 rounds while slot 10 finishes at most 16
#      (in turn it gets a third of the file server; before, it got none).
#   2. The display: the three are stopped, and chaos runs as `busy` (calls and grants to the
#      display, every round) in slots 10 to 14. Then a sixth starts in slot 15: it must
#      finish 16 rounds while slot 10 finishes at most 64.
# Both bounds are counted in the other programs' rounds, not in seconds, so a slow or busy
# host does not change the verdict; the times are printed for the record.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/chaos.elf || fail "chaos did not build"
card=$T/sd-fair.img
python3 tools/mksd.py "$card" files=build/progs/chaos.elf busy=build/progs/chaos.elf >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys, time
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [s.encode()]           # a whole command at once: QEMU holds what the UART cannot take yet
front = click(*DOCK["Terminal"])       # a new window takes the keys: give them back to Terminal
t0 = time.monotonic()
def line(l):
    print(f"{time.monotonic() - t0:8.2f} {l}", flush=True)
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened")]
# 1. the file server, two programs keeping it busy, then a third
steps += [*keys("run files\r"), wait_for("chaos: files in slot 10: 4 rounds"),
          *keys("run files\r"), wait_for("chaos: files in slot 11: 4 rounds"),
          *keys("run files\r"), wait_for("chaos: files in slot 12: 4 rounds")]
steps += [*keys("kill 10\r"), wait_for("terminal: kill", 1), *keys("kill 11\r"), wait_for("terminal: kill", 2),
          *keys("kill 12\r"), wait_for("terminal: kill", 3)]
# 2. the display, five busy programs, then a sixth
for k in range(10, 15):
    steps += [*keys("run busy\r"), wait_for(f"chaos: busy in slot {k}: 16 rounds"), *front]
steps += [*keys("run busy\r"), wait_for("chaos: busy in slot 15: 16 rounds"), *front,
          *keys("ps\r"), wait_for("terminal: ps")]
sys.exit(boot(120, steps=steps, sd=card, on_line=line, until="terminal: ps"))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^ *[0-9.]+ (chaos: (files|busy) in slot 1[25]|terminal: (run|kill|ps)|leanos: PANIC)" | sed 's/^/  | /'
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -q "SURPRISED" && fail "a program saw a file come back wrong, or a derive refused"

# How far a program had got by a line: its last report before it (or by the end, if the
# line never came).
rounds_by() {   # slot, name, the line
  echo "$out" | sed -n "1,/$3/p" | sed -n "s/^ *[0-9.]* chaos: $2 in slot $1: \([0-9]*\) rounds.*/\1/p" | tail -1
}
at() { echo "$out" | sed -n "s/^ *\([0-9.]*\) $1.*/\1/p" | head -1; }
# The program in `slot` must report `rounds` rounds while slot 10 does at most `limit`.
served() {   # what, name, slot, rounds, limit
  local began="terminal: run $2 -> slot $3" done="chaos: $2 in slot $3: $4 rounds"
  echo "$out" | grep -q "$began" || fail "$2 did not start in slot $3"
  local start=$(rounds_by 10 "$2" "$began")
  if ! echo "$out" | grep -q "$done"; then
    local last=$(rounds_by 10 "$2" "no such line") got=$(rounds_by $3 "$2" "no such line")
    fail "$1: slot $3 did not finish $4 rounds (it did ${got:-none}) while slot 10 did $((${last:-0} - ${start:-0})), in $(echo "$(echo "$out" | tail -1 | awk '{print $1}') - $(at "$began")" | bc) s"
  fi
  local d=$(($(rounds_by 10 "$2" "$done") - ${start:-0}))
  echo "$1: slot $3 did its first $4 rounds while slot 10 did $d ($(echo "$(at "$done") - $(at "$began")" | bc) s)"
  [ $d -le $5 ] || fail "$1: slot $3 waited while slot 10 did $d rounds (at most $5 allowed)"
}
served "file server" files 12 4 16
served "display" busy 15 16 64
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "ok: a program in a higher slot is served in turn: 4 file rounds beside two busy file programs, 16 busy rounds beside five"
