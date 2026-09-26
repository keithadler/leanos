#!/bin/bash
# Starting an open slot again while the display still knows its last run. The kernel's start
# frees every reply slot held for the last run (the next caller takes the first free one)
# and takes back the pixels it lent the display. If the display kept its records of that run,
# it would answer the new caller with another window's event, or wait on a dead window and
# never deliver the new one's, or draw pixels it no longer has.
#
# restart (user/progs/restart.c), on a card of its own under several names: alpha, beta and
# gamma each open a window, wait on it and print every event they get, with their name.
#
#   1. alpha waits on its window (the display holds its call); `kill 10` stops it, `run beta`
#      starts beta in the same slot. Keys and a click go to beta, and to nobody else.
#   2. blip opens a window in slot 11, then exits by itself while Terminal is loading gamma:
#      after Terminal has asked the display whether gamma is open, before it starts it, with
#      no message to the display in between (blip watches the file server get slow). gamma
#      starts in slot 11. The old display kept blip's window until its next message and
#      then drew it from pixels the start had taken back: it stopped (a data abort). Where
#      that window was hidden, gamma's wait was held on it instead, and the key typed into
#      gamma's window never reached gamma. Now a launcher calls the display just before it
#      starts a slot, and the display forgets stopped programs' windows before it answers
#      any call.
#   3. Keys and clicks to gamma, beta and Terminal reach each, and only it; gamma's close
#      button closes gamma; the display lives on to switch the machine off.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/restart.elf || fail "restart did not build"
card=$T/sd-restart.img
p=build/progs/restart.elf
python3 tools/mksd.py "$card" alpha=$p beta=$p blip=$p gamma=$p >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wmouse, wclick, CLOSE, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [s.encode()]
TERM = wclick("Terminal", 164, 174)     # in Terminal's window, once it is moved to the right
BETA = wclick("beta", 14, 48)           # in slot 10's window: (14, 18) in its pixels
GAMMA = wclick("gamma", 74, 77)         # in slot 11's window: (74, 47) in its pixels
GAMMA_CLOSE = wclick("gamma", *CLOSE)   # that window's close button
steps = [*wclick("alice", *CLOSE), wait_for("alice: window closed"),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         wmouse("d", "Terminal", 164, 12), wmouse("v", "Terminal", 164 + 220, 12),
         wmouse("v", "Terminal", 164 + 440, 12), wmouse("u", "Terminal", 164 + 440, 12),
         wait_for("display: moved Terminal's window"),
         # 1. kill + run into the slot of a program the display holds a call for
         *keys("run alpha\r"), wait_for("restart: alpha in slot 10: opened"), *TERM,
         *keys("kill 10\r"), wait_for("terminal: kill 10"),
         *keys("run beta\r"), wait_for("restart: beta in slot 10: opened"),
         *keys("b"), wait_for("restart: beta in slot 10: event 1 "),
         *BETA, wait_for("restart: beta in slot 10: event 2 "),
         # 2. a program that stops by itself between Terminal's question and its start
         *TERM, *keys("run blip\r"), wait_for("restart: blip in slot 11: ready"), *TERM,
         *keys("run gamma\r"), wait_for("terminal: run gamma"), wait_for("restart: gamma in slot 11: opened"),
         # 3. every app gets its own events, and only those
         *keys("g"), wait_for("restart: gamma in slot 11: event 1 "),
         *BETA, wait_for("restart: beta in slot 10: event 2 ", 2),
         *GAMMA, wait_for("restart: gamma in slot 11: event 2 "),
         *TERM, *keys("ps\r"), wait_for("terminal: ps"),
         *GAMMA_CLOSE, wait_for("restart: gamma in slot 11: event 5 "),
         *TERM, *keys("ps\r"), wait_for("terminal: ps", 2),
         *click(40, 15), *click(60, 80), wait_for("leanos: switched off")]
sys.exit(boot(120, steps=steps, sd=card))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^(restart: |terminal: (run|kill|ps)|display: (a program from the SD card stopped|.*unseen|the kernel dropped)|leanos: (switched off|PANIC)|leanos: .* stopped:)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status): an event went astray, or the display stopped?"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: [a-z ]+ stopped: " | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or app stopped: $bad"

events() { echo "$out" | grep "^restart: $1 in slot" | grep -v ": opened\|: ready\|: the file server"; }
[ -z "$(events alpha)" ] || fail "alpha, stopped while it waited, got events: $(events alpha)"
[ "$(events beta)" = "restart: beta in slot 10: event 1 b 0
restart: beta in slot 10: event 2 14 18
restart: beta in slot 10: event 2 14 18" ] || fail "beta did not get exactly its key and its two clicks: $(events beta)"
[ "$(events gamma)" = "restart: gamma in slot 11: event 1 g 0
restart: gamma in slot 11: event 2 74 47
restart: gamma in slot 11: event 5 0 0" ] || fail "gamma did not get exactly its key, its click and its close: $(events gamma)"
[ -z "$(events blip)" ] || fail "blip got events: $(events blip)"
echo "$out" | grep -q "^restart: blip in slot 11: the file server was busy" || fail "blip did not stop by itself"
echo "$out" | grep -qx "terminal: run gamma -> slot 11" || fail "gamma did not start in blip's slot"
[ "$(echo "$out" | grep -c "^display: a program from the SD card stopped; its window is gone")" = 2 ] \
  || fail "the display did not let go of alpha's and blip's windows before their slots started again"
echo "$out" | grep -qE "^display: (.*unseen|the kernel dropped)" && fail "a start got past the display unseen: $(echo "$out" | grep -E "^display: (.*unseen|the kernel dropped)")"
[ "$(echo "$out" | grep -c "^terminal: ps -> ")" = 2 ] || fail "Terminal did not get its keys"
echo "$out" | grep -q "^leanos: switched off" || fail "the machine did not switch off"
# Whether blip stopped inside Terminal's load (the race this test is for) or a little early,
# which only a slow host makes happen: say which.
when=$(echo "$out" | grep -nE "^(restart: blip in slot 11: the file server|display: key return to Terminal)" | tail -2 | head -1)
case "$when" in
  *"key return"*) how="while Terminal loaded gamma" ;;
  *) how="before Terminal was asked to run gamma (a slow host)" ;;
esac
echo "ok: slot 10 killed while waiting and slot 11 stopped by itself, both started again; blip stopped $how; each program got only its own events"
