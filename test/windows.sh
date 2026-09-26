#!/bin/bash
# A program with several windows. WAIT and POLL name no window: a program hears the events
# of all its windows in one wait, each event with its window's number (0 for its first, then
# the lowest it is not using), and the display holds one call per program. CLOSE closes one
# of the caller's own windows at once; a window whose close button was clicked is gone from
# the table when its program hears EV_CLOSE. (Before, a program heard only its first
# window's events: a second window's clicks, keys and close button went nowhere, and a
# closed second window stayed in the table until the program stopped.)
#
# mwin (user/progs/mwin.c), run from Terminal, opens three windows, red, green and blue
# (numbers 0, 1, 2, at (136, 112), (176, 148) and (216, 184), each 200 x 120: Notes is
# closed first, so Terminal has the table's first place and they the next three), and says
# every event with its window's number.
#
#   1. A click and a key in each window, at a point only that window covers.
#   2. Ctrl+C with the blue window in front (mwin answers "from window 2"), Ctrl+V into the red.
#   3. Terminal over all three, then `run mwin`: the display brings every window of mwin
#      forward, the one in front last (red) in front; a key goes to it.
#   4. The green window's close button: mwin hears EV_CLOSE for window 1; closing it again
#      is refused (it left the table), a new window gets number 1 again, mwin closes it
#      itself (CLOSE), and a second CLOSE is refused. The screen shows red and blue, no green.
#   5. A click and a key still reach the blue window. The red window's close button: mwin
#      closes the blue one itself, then WAIT and POLL (no window left) answer at once with
#      no event, and it stops. The screen shows none of its colors.
#
# The dock shows one icon for mwin, not one per window, all along.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/mwin.elf || fail "mwin did not build"
card=$T/sd-windows.img
python3 tools/mksd.py "$card" mwin=build/progs/mwin.elf >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
from collections import Counter
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, snap, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
RED, GREEN, BLUE = (150, 200), (190, 280), (300, 320)   # points only that window covers
GREEN_CLOSE, RED_CLOSE = (194, 163), (154, 127)
seen = Counter()
def after(prefix):
    seen[prefix] += 1                     # the same line again waits for its next one
    return wait_for(prefix, seen[prefix])
EV = "mwin: window "
steps = [*click(114, 91), wait_for("alice: window closed"),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         b"run mwin\r", wait_for("mwin: opened windows"),
         # 1. a click and a key in each
         *click(*RED), after(EV), b"a", after(EV),
         *click(*GREEN), after(EV), b"b", after(EV),
         *click(*BLUE), after(EV), b"c", after(EV), pause(0.3), snap("three"),
         # 2. copy from the blue window, paste into the red
         b"\x03", wait_for("display: copied"), *click(*RED), after(EV), b"\x16", after(EV),
         # 3. Terminal over them, then run mwin: all of mwin's windows come forward
         *click(*DOCK["Terminal"]), pause(0.5), snap("covered"),
         b"run mwin\r", wait_for("terminal: run mwin", 2), pause(0.5), snap("raised"), b"r", after(EV),
         # 4. the green window's close button
         *click(*GREEN), after(EV), *click(*GREEN_CLOSE), wait_for("mwin: ready"), pause(0.5), snap("two"),
         # 5. the blue window still hears; then the red window's close button
         *click(*BLUE), after(EV), b"z", after(EV),
         *click(*RED_CLOSE), wait_for("mwin: no window left")]
sys.exit(boot(90, steps=steps, until="mwin: no window left", sd=card, settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(mwin: |terminal: run|display: (a program from the SD card (opened|closed)|closed|copied|paste|mwin is))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: ([a-z]+|slot 1[0-5]) stopped" | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or program stopped: $bad"
echo "$out" | grep -E "^mwin: " | grep -qE "WRONG|TAKEN|REFUSED|NOT " && fail "$(echo "$out" | grep -E "^mwin: .*(WRONG|TAKEN|REFUSED|NOT )" | head -1)"

failed=0
has() { echo "$out" | grep -qxF "$1" || { echo "FAIL: missing: $1"; failed=1; }; }
S="a program from the SD card"
has "mwin: opened windows 0, 1, 2"
has "display: $S opened a 200x120 window from a read-only capability to 24 pages, its window 1"
has "display: $S opened a 200x120 window from a read-only capability to 24 pages, its window 2"
# 1. each window's click (in its own coordinates) and key, with its number
has "mwin: window 0: click at (14, 58)"
has "mwin: window 0: key 'a'"
has "mwin: window 1: click at (14, 102)"
has "mwin: window 1: key 'b'"
has "mwin: window 2: click at (84, 106)"
has "mwin: window 2: key 'c'"
# 2. copy asked of the window in front, pasted into the one in front then
has "mwin: copy asked of window 2"
has "display: copied 13 bytes from $S"
has "mwin: window 0: paste 'from window 2'"
# 3. RAISE brings the program's windows forward, the one in front last in front
has "display: mwin is already open; brought it to the front"
has "mwin: window 0: key 'r'"
# 4. the close button, then CLOSE
has "display: closed $S's window"
has "mwin: window 1: closed by its button"
has "mwin: closing window 1 again: refused"
has "mwin: opened another window: 1, the closed one's number"
has "display: $S closed its window 1; windows in the table: 3"
has "mwin: closed window 1 itself"
has "mwin: closing window 1 twice: refused"
# 5. the rest still hear; the last closed; no window left
has "mwin: window 2: click at (84, 106)"
has "mwin: window 2: key 'z'"
has "mwin: window 0: closed by its button"
has "mwin: closed window 2 itself"
has "display: $S closed its window 2; windows in the table: 1"
has "mwin: no window left: WAIT and POLL answer at once, with no event"
# every event mwin heard, in order: nothing for a window it did not click or type into
evs=$(echo "$out" | grep "^mwin: window " | sed 's/^mwin: window \([0-9]\): \([a-z]*\).*/\1 \2/' | tr '\n' ',')
want="0 click,0 key,1 click,1 key,2 click,2 key,0 click,0 paste,0 key,1 click,1 closed,2 click,2 key,0 closed,"
[ "$evs" = "$want" ] || { echo "FAIL: mwin's events, in order: $evs (expected $want)"; failed=1; }
[ $failed -eq 0 ] || exit 1

# The screen: each window's color where only it can be seen, and nowhere once it is closed.
# The dock: one icon for mwin (a card program's icon, drawn in the dock's extras when it has
# no picture of its own: a blue square), not one per window.
python3 - "$T" <<'PYS' || fail "the screen does not show the windows as they are"
import os, sys
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return w, h, px
COLORS = {"red": (0xd0, 0x40, 0x40), "green": (0x40, 0xb0, 0x40), "blue": (0x40, 0x60, 0xd0), "yellow": (0xd0, 0xc0, 0x40)}
# where only that window can be seen, beside where the test clicked (the pointer is there)
POINTS = {"red": (146, 196), "green": (186, 276), "blue": (296, 316)}
MINI = (58, 110, 230)          # the dock's square for a program with no icon
def near(p, c):
    return all(abs(p[i] - c[i]) <= 2 for i in range(3))
def count(name, c, x0=0, y0=0, x1=None, y1=None):
    w, h, px = load(name)
    x1, y1 = x1 or w, y1 or h
    return sum(1 for y in range(y0, y1) for x in range(x0, x1) if near(px[(y * w + x) * 3:(y * w + x) * 3 + 3], c))
def at(name, x, y):
    w, h, px = load(name)
    return tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
out = []
for shot, shown in (("three", "red green blue"), ("raised", "red green blue")):
    for c in shown.split():
        assert near(at(shot, *POINTS[c]), COLORS[c]), (shot, c, "not shown where only it can be", at(shot, *POINTS[c]))
for c in POINTS:
    assert not near(at("covered", *POINTS[c]), COLORS[c]), ("covered", c, "shows through Terminal")
two = {c: count("two", COLORS[c]) for c in COLORS}
assert two["red"] > 2000 and two["blue"] > 2000, ("two", "red and blue must be shown", two)
assert two["green"] < 50 and two["yellow"] < 50, ("two", "the closed windows are still drawn", two)
end = {c: count("screen", COLORS[c]) for c in COLORS}
assert max(end.values()) < 50, ("the end", "a closed window is still drawn", end)
# the dock's extras start at x 849, one 40 px square each, 48 apart
first = count("three", MINI, 849, 520, 889, 590)
more = count("three", MINI, 893, 520, 1024, 590)
assert first > 500 and more < 20, ("the dock shows one icon for mwin", first, more)
print(f"ok: the screen: each window's color where only it can be seen, with three up and after Terminal covered them "
      f"and run raised them; after the green one closed, red {two['red']} and blue {two['blue']} pixels, no green, no yellow; "
      f"none at the end; one dock icon for mwin ({first} pixels, {more} beside it)")
PYS
echo "ok: one program, three windows: each window's clicks, keys, copy and paste reach it with its number; RAISE brings all three forward; a window's close button and CLOSE each take it out of the table at once, a second CLOSE is refused, its number is given again; with none left, WAIT and POLL answer at once"
