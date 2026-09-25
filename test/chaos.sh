#!/bin/bash
# The trusted base at its limits: chaos (user/progs/chaos.c), on a card of its own under the
# names hog, hogx, hogf, busy, wins, nap and pest, run from Terminal into the open slots, again
# and again. The proofs cover the Lean kernel's decisions; this is about the unproved C under
# and around them (the runtime's allocator and freeing, the machine layer's tables, loading
# and kernel lock, the servers) with every list the kernel keeps as long as it may get.
#
#   1. Baseline: nap in all six open slots, the kernel heap after the sixth start.
#   2. Every limit at once: hog in all six slots. Each derives capabilities until the kernel
#      says full (64), maps all 8192 pages of its window, writes and reads back a 16 KiB file,
#      grants the display its spare run 100 times, and waits on its window: with Notes and
#      Terminal the display holds all 8 of its reply slots. The system must still work
#      (Terminal writes and reads a file); then each is killed with its call outstanding.
#   3. Thirty restarts of slot 10, while slots 11 to 15 keep five stopped hogs' 8192
#      mappings (every start rebuilds all 18 tasks' tables and walks those lists): hog killed
#      waiting on the display, busy killed mid-round, hogf stopped by its own fault, nap
#      killed asleep, hogx exiting. The heap after each start must be the same number.
#   4. Windows until the display refuses one (Notes and Terminal have two of its twelve).
#   5. Four cores busy: busy in four slots at once (capabilities and mappings made and
#      dropped, each map a new level-3 table; display calls with grants; files), and Terminal
#      writing a file beside them. (Not six: a server answers the lowest slot waiting first,
#      so the fifth and sixth would wait long for the display.)
#   6. nap in all six slots again: the heap must be back at the baseline.
#   7. pest sends the file server and the display 100 grants each by plain send, which
#      wants no answer. Then the file server must still take requests (every one carries a
#      grant): before it let go of such grants, 58 filled its capabilities and no file could
#      be read or written again. Then the display takes a window (hello), the file server a
#      file, and the machine switches off, with its last report.
# Nothing may panic, no server may stop, every check the programs make must hold.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/chaos.elf build/progs/hello.elf || fail "chaos did not build"
card=$T/sd-chaos.img
python3 tools/mksd.py "$card" hog=build/progs/chaos.elf hogx=build/progs/chaos.elf hogf=build/progs/chaos.elf \
  busy=build/progs/chaos.elf wins=build/progs/chaos.elf nap=build/progs/chaos.elf pest=build/progs/chaos.elf \
  hello=build/progs/hello.elf >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
from collections import Counter
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [s.encode()]           # a whole command at once: QEMU holds what the UART cannot take yet
front = click(*DOCK["Terminal"])       # a new window takes the keys: give them back to Terminal
seen = Counter()
def wait(prefix):
    seen[prefix] += 1
    return wait_for(prefix, seen[prefix])
def run(name, ready):
    return [*keys(f"run {name}\r"), wait(ready), *front]
def kill(slot):
    return [*keys(f"kill {slot}\r"), wait("terminal: kill")]
SLOTS = range(10, 16)

steps = [*click(*DOCK["Terminal"]), wait("terminal: opened")]
# 1. the baseline
for k in SLOTS: steps += run("nap", f"chaos: nap in slot {k}: asleep")
for k in SLOTS: steps += kill(k)
# 2. every limit at once, then killed with their calls outstanding
for k in SLOTS: steps += run("hog", f"chaos: hog in slot {k}:")
steps += [*keys("write limits.txt every limit at once\r"), wait("terminal: write limits.txt"),
          *keys("cat limits.txt\r"), wait("terminal: cat limits.txt")]
for k in SLOTS: steps += kill(k)
# 3. thirty restarts of slot 10
for cycle in range(6):
    steps += run("hog", "chaos: hog in slot 10:") + kill(10)
    steps += run("busy", "chaos: busy in slot 10: 16 rounds") + kill(10)
    steps += run("hogf", "leanos: slot 10 stopped: data access not allowed at 0x80000000") + kill(10)
    steps += run("nap", "chaos: nap in slot 10: asleep") + kill(10)
    steps += run("hogx", "chaos: hogx in slot 10:") + kill(10)
# 4. windows until the display refuses one
steps += run("wins", "chaos: wins in slot 10:") + kill(10)
# 5. four cores busy
for k in range(10, 14): steps += run("busy", f"chaos: busy in slot {k}: 16 rounds")
steps += [*keys("write busy.txt four at once\r"), wait("terminal: write busy.txt"),
          *keys("cat busy.txt\r"), wait("terminal: cat busy.txt"), wait("chaos: busy in slot 13: 32 rounds")]
for k in range(10, 14): steps += kill(k)
# 6. the baseline again
for k in SLOTS: steps += run("nap", f"chaos: nap in slot {k}: asleep")
# 7. grants nobody asked for, then the rest of the system still works
steps += kill(10) + run("pest", "chaos: pest in slot 10:") + kill(11)
steps += [*keys("run hello\r"), wait("terminal: run hello"), pause(0.5), *front]
steps += [*keys("write after.txt still here\r"), wait("terminal: write after.txt"),
          *keys("cat after.txt\r"), wait("terminal: cat after.txt"),
          *click(40, 15), *click(60, 80), wait("leanos: switched off")]
sys.exit(boot(300, steps=steps, sd=card))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^(chaos: (hog|hogx|hogf|wins|pest) |chaos: busy in slot 1.: 16 rounds|terminal: (run|kill|write|cat)|hello: opened|leanos: (slot 1. stopped|kernel heap .* slot 1[05]$|switched off|PANIC))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: [a-z]+ stopped" | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or app stopped: $bad"
echo "$out" | grep -q "^chaos: .*run under a name it does not know" && fail "chaos did not find its name"

# Every limit, reached every time, and every check the programs make held.
hogs=$(echo "$out" | grep -E "^chaos: hog[xf]? in slot")
[ "$(echo "$hogs" | wc -l | tr -d ' ')" = 24 ] || fail "not every hog finished (expected 24)"
[ -z "$(echo "$hogs" | grep -v ": 64 capabilities, 8192 pages mapped, a window, 100 grants to the display, 0 surprises$")" ] \
  || fail "a hog missed a limit: $(echo "$hogs" | grep -v ', 0 surprises$' | head -1)"
echo "$out" | grep -q "^chaos: busy .*SURPRISED" && fail "busy saw a file come back wrong, or a derive refused"
echo "$out" | grep -q "^chaos: pest in slot 10: 100 grants sent to the file server, 100 taken; 100 to the display, 100 taken; its file still reads back$" \
  || fail "a server kept grants sent to it by plain send: $(echo "$out" | grep "^chaos: pest")"
echo "$out" | grep -q "^chaos: wins in slot 10: 10 windows, then the display refused one$" \
  || fail "the display did not take exactly its 10 free windows"
[ "$(echo "$out" | grep -c "^leanos: slot 10 stopped: data access not allowed at 0x80000000$")" = 6 ] \
  || fail "hogf was not stopped by its fault six times"
[ "$(echo "$out" | grep -c "^terminal: kill 1[0-5] -> stopped$")" -ge 37 ] || fail "a program was not killed"

# The system still works: under every limit at once, beside four busy programs, and at the end.
for f in limits busy after; do
  echo "$out" | grep -q "^terminal: write $f.txt -> ok" || fail "the file server did not take $f.txt"
done
echo "$out" | grep -q "^hello: opened a window -> ok" || fail "the display did not take a window at the end"

# The kernel heap: the same after every restart of slot 10, and back at the baseline.
heap() { echo "$out" | sed -n "s/^leanos: kernel heap \([0-9]*\) bytes live, [0-9]* peak, after starting slot $1$/\1/p"; }
h15=$(heap 15)
base=$(echo "$h15" | head -1)
hogs5=$(echo "$h15" | sed -n 2p)
end=$(echo "$h15" | tail -1)
cycles=$(heap 10 | sed -n '3,32p')         # slot 10's 30 restarts (after a nap and a hog)
[ "$(echo "$cycles" | wc -l | tr -d ' ')" = 30 ] || fail "expected 30 restarts of slot 10"
lo=$(echo "$cycles" | sort -n | head -1)
hi=$(echo "$cycles" | sort -n | tail -1)
echo "kernel heap after starting slot 15: $base bytes with five naps, $hogs5 with five hogs holding 8192 mappings each, $end with five naps again"
echo "kernel heap after each of slot 10's 30 restarts: $(echo $cycles | tr ' ' ',')"
# A leak grows with every cycle. The one change allowed: the display's list of reply slots
# grows once, to its bound of 8, when phase 2 fills it (48 bytes a slot; 192 here).
[ $((hi - lo)) -le 1024 ] || fail "the heap after a restart of slot 10 ranged from $lo to $hi bytes"
d=$((end - base)); [ ${d#-} -le 384 ] || fail "the heap did not come back: $base bytes before, $end after"
peak=$(echo "$out" | sed -n 's/^leanos: switched off (.*kernel heap [0-9]* bytes live, \([0-9]*\) peak, stack \([0-9]*\) bytes peak.*/\1 \2/p')
[ -n "$peak" ] || fail "no report at switch-off"
set -- $peak
[ "$2" -le 32768 ] || fail "the kernel stack reached $2 bytes"
echo "ok: 24 programs at every limit, 30 restarts of one slot, four busy at once, 200 grants nobody asked for; heap back to $end bytes (peak $1), stack peak $2 bytes"
