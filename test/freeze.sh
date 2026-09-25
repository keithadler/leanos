#!/bin/bash
# More windows waiting than the display has reply slots. The kernel gives a task 8 reply
# slots (maxCallers); the display shows up to 12 windows and holds each waiting window's call
# (OP_WAIT) until it has an event. It used to hold every one: with 8 windows waiting, the
# next call to it (Notes asking for a window) made each of its receives fail as full, it
# retried for ever, and no key or click reached anyone again. Now it holds at most 7 and
# answers the one waiting longest with no event; that app asks again a moment later.
#
#   1. The freeze as it was found: Notes closed, Terminal and Files open, hog (user/progs/
#      chaos.c) in all six open slots, each waiting on its window: 8 windows wait. Notes,
#      started from the dock, must get its window; keys typed into it must reach it (it
#      saves them: Terminal's cat finds 2 bytes); a click in Files must reach Files.
#   2. The most windows the display shows: one hog stopped, then Security, Settings, Apps
#      and wins, which opens windows until the display refuses one: 12 windows, 11 waiting.
#      Keys still reach Notes and Terminal, a click still reaches Files.
#   3. No spinning: the host CPU QEMU uses while 11 windows wait with nothing to do stays
#      near what it uses while 2 wait, and the whole run makes a bounded number of system
#      calls. A parked app asks again every WAIT_AGAIN_MS (app.h), and while the slots are
#      taken the display answers it at once, without letting another go; an app that asked
#      again at once would keep a core busy.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/chaos.elf || fail "chaos did not build"
card=$T/sd-freeze.img
python3 tools/mksd.py "$card" hog=build/progs/chaos.elf wins=build/progs/chaos.elf >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import os, subprocess, sys, time
from collections import Counter
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [s.encode()]
front = click(*DOCK["Terminal"])       # a new window takes the keys: give them back to Terminal
FILES = (580, 200)                     # in Files' window (the second to open, at 136,112), clear of the rest
seen = Counter({"files: showing": 1})   # Files shows its first file as it opens
def wait(prefix):
    seen[prefix] += 1
    return wait_for(prefix, seen[prefix])
def run(name, ready):
    return [*keys(f"run {name}\r"), wait(ready), *front]

def qemu_cpu():
    """Host CPU seconds QEMU (this script's child) has used so far."""
    total = 0.0
    kids = subprocess.run(["pgrep", "-P", str(os.getpid())], capture_output=True, text=True).stdout.split()
    for pid in kids:
        t = subprocess.run(["ps", "-o", "time=", "-p", pid], capture_output=True, text=True).stdout.strip()
        if not t:
            continue
        days, _, t = t.rpartition("-")
        secs = sum(float(p) * 60 ** i for i, p in enumerate(reversed(t.split(":"))))
        total += secs + 86400 * int(days or 0)
    return total

samples = []
def on_line(line):
    print(line, flush=True)
    if line.startswith("terminal: ps"):
        samples.append((time.monotonic(), qemu_cpu()))
        if len(samples) % 2 == 0:
            (t0, c0), (t1, c1) = samples[-2:]
            print(f"freeze: QEMU used {100 * (c1 - c0) / (t1 - t0):.0f}% of a host core for {t1 - t0:.1f} s", flush=True)

IDLE = [*keys("ps\r"), wait("terminal: ps"), pause(6), *keys("ps\r"), wait("terminal: ps")]
steps = [*click(114, 91), wait("alice: window closed"),
         *click(*DOCK["Terminal"]), wait("terminal: opened"),
         *click(*DOCK["Files"]), wait("files: opened"), *front, *IDLE]
# 1. eight windows wait, then Notes asks for one
for k in range(10, 16): steps += run("hog", f"chaos: hog in slot {k}:")
steps += [*click(*DOCK["Notes"]), wait("alice: opened"), *keys("Hi"), wait("display: key 'i' to alice"),
          *front, *keys("cat notes.txt\r"), wait("terminal: cat notes.txt"),
          *click(*FILES), wait("files: showing"), *front]
# 2. twelve windows, eleven waiting
steps += [*keys("kill 15\r"), wait("terminal: kill 15"),
          *click(*DOCK["Security"]), wait("security: opened"),
          *click(*DOCK["Settings"]), wait("settings: opened"),
          *click(*DOCK["Apps"]), wait("apps: opened"), *front,
          *run("wins", "chaos: wins in slot 15:"),
          *click(*DOCK["Notes"]), *keys("!"), wait("display: key '!' to alice"), pause(0.5),
          *front, *keys("cat notes.txt\r"), wait("terminal: cat notes.txt"),
          *click(*DOCK["Files"]), *click(*FILES), wait("files: showing"), *front, pause(1)]
# 3. idle with eleven waiting, then switch off
steps += [*IDLE, *click(40, 15), *click(60, 80), wait("leanos: switched off")]
sys.exit(boot(90, steps=steps, sd=card, on_line=on_line))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^(chaos: (hog|wins) |alice: opened|display: more windows|terminal: (cat|ps|kill)|files: showing|freeze: |leanos: (switched off|PANIC))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status): the display froze?"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: [a-z]+ stopped" | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or app stopped: $bad"

[ "$(echo "$out" | grep -c "^chaos: hog in slot 1[0-5]: 64 capabilities, 8192 pages mapped, a window, 100 grants to the display, 0 surprises$")" = 6 ] \
  || fail "not all six hogs reached their limits and waited on a window"
echo "$out" | grep -q "^display: more windows wait than the 7 calls it holds: " \
  || fail "the display never had more windows waiting than it holds"
[ "$(echo "$out" | grep -c "^alice: opened a 300x200 window, read-only, 59 pages -> ok$")" = 2 ] \
  || fail "Notes did not get its window with 8 windows waiting"
cats=$(echo "$out" | grep "^terminal: cat notes.txt")
[ "$(echo "$cats" | sed -n 1p)" = "terminal: cat notes.txt -> 2 bytes" ] || fail "keys typed into Notes did not reach it: $cats"
[ "$(echo "$cats" | sed -n 2p)" = "terminal: cat notes.txt -> 3 bytes" ] || fail "with 12 windows, a key typed into Notes did not reach it: $cats"
[ "$(echo "$out" | grep -c "^files: showing")" -ge 3 ] || fail "a click in Files did not reach it"
echo "$out" | grep -q "^chaos: wins in slot 15: 1 windows, then the display refused one$" \
  || fail "the display did not show exactly 12 windows: $(echo "$out" | grep "^chaos: wins")"
echo "$out" | grep -q "^leanos: switched off" || fail "the machine did not switch off"

# No spinning: 11 windows waiting cost about what 2 do.
cpu=$(echo "$out" | sed -n 's/^freeze: QEMU used \([0-9]*\)% .*/\1/p')
[ "$(echo "$cpu" | wc -l | tr -d ' ')" = 2 ] || fail "no CPU measurement"
two=$(echo "$cpu" | sed -n 1p)
eleven=$(echo "$cpu" | sed -n 2p)
[ "$eleven" -le $((two + 40)) ] || fail "with 11 windows waiting QEMU used $eleven% of a host core, with 2 $two%: something spins"
calls=$(echo "$out" | sed -n 's/^leanos: switched off (\([0-9]*\) system calls.*/\1/p')
[ -n "$calls" ] && [ "$calls" -le 100000 ] || fail "$calls system calls in the run: something spins (about 23,000 without)"
echo "ok: Notes opened with 8 windows waiting, 12 windows with 11 waiting, keys and clicks still reach apps; idle QEMU at $two% of a core with 2 windows waiting, $eleven% with 11; $calls system calls"
