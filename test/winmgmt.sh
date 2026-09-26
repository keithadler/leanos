#!/bin/bash
# Window management: the yellow button minimizes a window, the green one zooms it, Ctrl+O
# (byte 15) brings the next window to the front, and the Window menu does all three. All of
# it is the display server's: no program changes, and a program can tell only by what it no
# longer hears.
#
# On a card with mwin (three windows, test/windows.sh) and clock (a pinned program):
#
#   1. Notes, Terminal and Files open, Files in front. Ctrl+O three times: the focus goes to
#      Terminal, Notes, Files (a key typed after each reaches that one), back where it began.
#   2. Terminal, in front, minimized with its yellow button: it is gone from the screen, the
#      next window in front (Notes) has the keys, and Terminal's dock icon has an amber dot.
#      Its dock icon brings it back, where it was, in front, with the keys; the dot is white.
#   3. Files zoomed with its green button: in the middle of the room between the menu bar and
#      the dock, in front; the green button again puts it back where it was.
#   4. The Window menu: Next window, Minimize, Zoom and Zoom again, each on the window in
#      front (the menu found on the screen, after the window's name and Edit).
#   5. `run mwin`: three windows. Window 1 minimized: windows 0 and 2 stay, and 2 still hears
#      keys; mwin's dock icon has the amber dot. `run mwin` (RAISE) brings window 1 back.
#   6. Clock, pinned in the dock: minimized, it keeps ticking and asking to be drawn, and its
#      pixels are never drawn; its dock icon brings it back.
#   7. mwin's window minimized, then mwin killed and run again in its slot: the display forgot
#      the old run's windows, the minimized one too, and the new run's three are all shown.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/mwin.elf || fail "mwin did not build"
card=$T/sd-winmgmt.img
python3 tools/mksd.py "$card" mwin=build/progs/mwin.elf clock=build/progs/clock.elf \
  clock.icon=build/icons/clock.icon >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
from collections import Counter
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, snap, wclick, screen_click, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
YELLOW, GREEN = (38, 15), (58, 15)          # the title bar's minimize and zoom buttons
seen = Counter()
def after(prefix):
    seen[prefix] += 1                        # the same line again waits for its next one
    return wait_for(prefix, seen[prefix])
def key_to(name):
    return [b"q", after(f"display: key 'q' to {name}")] + ([b"\x7f"] if name == "Terminal" else [])
NEXT = b"\x0f"

def window_menu(item):
    """Open the Window menu and choose an item (0 Minimize, 1 Zoom, 2 Next window): its name
    is the third word in the menu bar from x 104 (the window's name, Edit, Window), and the
    menu opens under it, 28 px an item from y 40."""
    def label(ppm):
        data = open(ppm, "rb").read()
        _, dims, _, px = data.split(b"\n", 3)
        w = int(dims.split()[0])
        ink = [any(min(px[(y * w + x) * 3:(y * w + x) * 3 + 3]) > 170 for y in range(8, 23)) for x in range(w)]
        words, x = [], 104
        while x < 600 and len(words) < 3:
            if ink[x]:
                words.append(x)
                while x < 600 and any(ink[x:x + 12]):
                    x += 1
            x += 1
        return words[2] if len(words) == 3 else None
    def at_label(ppm):
        x = label(ppm)
        return (x + 20, 15) if x else None
    def at_item(ppm):
        x = label(ppm)
        return (x + 20, 54 + 28 * item) if x else None
    return [screen_click(at_label), after("display: the Window menu, for "), screen_click(at_item)]

steps = [wait_for("alice: opened"),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *click(*DOCK["Files"]), wait_for("files: opened"), pause(0.5), snap("three"),
         # 1. Ctrl+O through the three
         NEXT, after("display: focus to Terminal"), *key_to("Terminal"),
         NEXT, after("display: focus to alice"), *key_to("alice"),
         NEXT, after("display: focus to Files"), *key_to("Files"),
         # 2. Terminal in front, minimized; keys to the next; the dock brings it back
         NEXT, after("display: focus to Terminal"),
         *wclick("Terminal", *YELLOW), after("display: Terminal minimized"), after("display: focus to alice"),
         *key_to("alice"), pause(0.5), snap("minimized"),
         *click(*DOCK["Terminal"]), after("display: Terminal restored"), *key_to("Terminal"),
         pause(0.5), snap("restored"),
         # 3. Files zoomed, and back
         *click(*DOCK["Files"]), *wclick("Files", *GREEN), after("display: Files zoomed"),
         after("display: moved Files's window"), *key_to("Files"), pause(0.5), snap("zoomed"),
         *wclick("Files", *GREEN), after("display: Files zoomed back"), after("display: moved Files's window"),
         # 4. the Window menu: Files in front, then Terminal (Next window), minimized; Notes zoomed and back
         *window_menu(2), after("display: focus to Terminal"),
         *window_menu(0), after("display: Terminal minimized"), after("display: focus to alice"),
         *window_menu(1), after("display: alice zoomed"), after("display: moved alice's window"),
         pause(0.3), snap("menuzoom"),
         *window_menu(1), after("display: alice zoomed back"), after("display: moved alice's window"),
         # 5. mwin: one of three windows minimized, then brought back by run
         *click(*DOCK["Terminal"]), after("display: Terminal restored"),
         b"run mwin\r", after("mwin: opened windows"), pause(0.5), snap("mwin3"),
         *wclick("mwin", *YELLOW, 1), after("display: mwin minimized, its window 1"),
         b"k", after("mwin: window 2: key 'k'"), pause(0.5), snap("mwin2"),
         *click(*DOCK["Terminal"]), b"run mwin\r", after("display: mwin restored, its window 1"),
         b"j", after("mwin: window 1: key 'j'"), pause(0.5), snap("mwinback"),
         # 6. the pinned clock
         *click(*DOCK["Clock"]), after("clock: ticked"), pause(0.5), snap("clock"),
         *wclick("clock", *YELLOW), after("display: clock minimized"), pause(0.5), snap("clockmin"),
         pause(1.5), snap("clockmin2"),
         *click(*DOCK["Clock"]), after("display: clock restored"), pause(0.5), snap("clockback"),
         # 7. mwin minimized, killed, run again
         *wclick("mwin", *YELLOW, 0), wait_for("display: mwin minimized", 2),
         *click(*DOCK["Terminal"]), b"kill 10\r", after("terminal: kill 10"),
         b"run mwin\r", after("mwin: opened windows"), pause(0.5), b"z"]
sys.exit(boot(120, steps=steps, until="mwin: window 2: key 'z'", sd=card, settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(mwin: |terminal: (run|kill)|display: (.* (minimized|restored|zoomed|zoomed back|opened .*)(, its window [0-9]+)?$|focus to|moved|the Window menu|key 'q'|a program from the SD card stopped))" \
  | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: ([a-z]+|slot 1[0-5]) stopped" | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or program stopped: $bad"
echo "$out" | grep -E "^mwin: " | grep -qE "WRONG|TAKEN|REFUSED|NOT " && fail "$(echo "$out" | grep -E "^mwin: .*(WRONG|TAKEN|REFUSED|NOT )" | head -1)"

failed=0
has() { echo "$out" | grep -qxF "$1" || { echo "FAIL: missing: $1"; failed=1; }; }
# In order: what the display did, and who got each key typed to see where the focus was.
# Files is 460 x 340 (460 x 370 with its title bar), zoomed to x (1024 - 460) / 2 and, in the
# room from the menu bar (31 px) to the dock (y 514), y 31 + (483 - 370) / 2; Notes is 300 x
# 230, zoomed to ((1024 - 300) / 2, 31 + (483 - 230) / 2).
got=$(echo "$out" | grep -E "^display: (.* (minimized|restored|zoomed|zoomed back)(, its window [0-9]+)?$|focus to |key 'q' to |moved Files|moved alice|the Window menu)")
want="display: focus to Terminal
display: key 'q' to Terminal
display: focus to alice
display: key 'q' to alice
display: focus to Files
display: key 'q' to Files
display: focus to Terminal
display: Terminal minimized
display: focus to alice
display: key 'q' to alice
display: Terminal restored
display: key 'q' to Terminal
display: Files zoomed
display: moved Files's window to (282, 87)
display: key 'q' to Files
display: Files zoomed back
display: moved Files's window to (88, 136)
display: the Window menu, for Files
display: focus to Terminal
display: the Window menu, for Terminal
display: Terminal minimized
display: focus to alice
display: the Window menu, for alice
display: alice zoomed
display: moved alice's window to (362, 157)
display: the Window menu, for alice
display: alice zoomed back
display: moved alice's window to (8, 38)
display: Terminal restored
display: mwin minimized, its window 1
display: mwin restored, its window 1
display: clock minimized
display: focus to mwin, its window 1
display: clock restored
display: mwin minimized"
[ "$got" = "$want" ] || { echo "FAIL: what the display did, in order:"; echo "$got" | sed 's/^/  got  | /'; failed=1; }
has "display: Files opened a 460x340 window at 88,136 from a read-only capability to 153 pages"
has "display: alice opened a 300x200 window at 8,38 from a read-only capability to 59 pages"
# mwin's other windows heard their keys while window 1 was minimized; 1 its own once back
has "mwin: window 2: key 'k'"
has "mwin: window 1: key 'j'"
has "display: mwin is already open; brought it to the front"
# killed with a window minimized: all three of the old run's windows forgotten, and the new
# run's three shown, a key reaching the one in front
[ "$(echo "$out" | grep -c "^display: a program from the SD card stopped; its window is gone$")" = 3 ] \
  || { echo "FAIL: the killed mwin's three windows were not all forgotten"; failed=1; }
[ "$(echo "$out" | grep -c "^mwin: opened windows 0, 1, 2$")" = 2 ] || { echo "FAIL: mwin did not open its windows again"; failed=1; }
has "mwin: window 2: key 'z'"
[ $failed -eq 0 ] || exit 1

# The screen.
python3 - "$T" <<'PYS' || fail "the screen does not show the windows as they are"
import os, sys
sys.path.insert(0, "test")
from run import window_pos
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
def count(name, pred, x0, y0, x1, y1):
    at = load(name)
    return sum(1 for y in range(y0, y1) for x in range(x0, x1) if pred(at(x, y)))
def near(c):
    return lambda p: all(abs(p[i] - c[i]) <= 2 for i in range(3))
# The dock's dot under a program's icon (at the icon's center x): white, or amber (the yellow
# button's color) while a window of it is minimized. Terminal's and Clock's icons, and mwin's
# (the first after the built-in and pinned ones).
WHITE, AMBER = (230, 232, 240), (254, 188, 46)
TERMINAL, CLOCK, EXTRA = 347, 611, 869
def dot(name, x):
    return load(name)(x - 1, 584)
for icon, shots in ((TERMINAL, ("three", "minimized", "restored")), (EXTRA, ("mwin3", "mwin2", "mwinback")),
                    (CLOCK, ("clock", "clockmin", "clockback"))):
    for shot, want in zip(shots, (WHITE, AMBER, WHITE)):
        assert dot(shot, icon) == want, (shot, "the dock's dot at", icon, dot(shot, icon))
# Terminal (556, 38; its dark content from y 68, 460 x 272): drawn, gone, back
dark = lambda p: max(p) < 40
term = {s: count(s, dark, 556, 68, 1016, 340) for s in ("three", "minimized", "restored")}
assert term["three"] > 100000 and term["restored"] > 100000 and term["minimized"] < 100, ("Terminal's pixels", term)
# Files zoomed to (282, 87): its window where it went (light), none where it was
z, t = load("zoomed"), load("three")
assert min(z(700, 440)) > 200 and max(t(700, 440)) < 160, ("Files at its zoomed place", z(700, 440), t(700, 440))
assert max(z(400, 485)) < 160 and min(t(400, 485)) > 200, ("Files gone from where it was", z(400, 485), t(400, 485))
# Notes zoomed from the Window menu to (362, 157): light where it went
m = load("menuzoom")
assert min(m(620, 300)) > 200 and max(t(620, 300)) < 160, ("Notes at its zoomed place", m(620, 300), t(620, 300))
# mwin: red, green, blue; green (window 1) gone while minimized, the others shown; green back
RED, GREEN, BLUE = (0xd0, 0x40, 0x40), (0x40, 0xb0, 0x40), (0x40, 0x60, 0xd0)
cols = {s: {n: count(s, near(c), 0, 31, 1024, 514) for n, c in (("red", RED), ("green", GREEN), ("blue", BLUE))}
        for s in ("mwin3", "mwin2", "mwinback")}
for s in ("mwin3", "mwinback"):
    assert min(cols[s].values()) > 15000, (s, "mwin's three windows", cols[s])
assert cols["mwin2"]["green"] < 50 and cols["mwin2"]["red"] > 15000 and cols["mwin2"]["blue"] > 15000, \
    ("mwin2", "window 1 minimized, 0 and 2 shown", cols["mwin2"])
# the clock (300 x 180 with its title bar): minimized, nothing of it drawn as it ticks, and
# its seconds changed by the time it is back
log = open(os.path.join(sys.argv[1], "serial.txt")).read()
cx, cy = window_pos(log.split("display: clock minimized")[0], "clock")
box = [(x, y) for y in range(cy, cy + 180) for x in range(cx, cx + 300)]
a, b, c, d = load("clock"), load("clockmin"), load("clockmin2"), load("clockback")
still = sum(1 for p in box if b(*p) != c(*p))
gone = sum(1 for p in box if a(*p) != b(*p))
ticked = sum(1 for p in box if a(*p) != d(*p))
assert still == 0 and gone > 20000 and ticked > 50, ("the clock minimized", still, gone, ticked)
print(f"ok: the screen: Terminal's dark pixels {term['three']}, minimized {term['minimized']}, back {term['restored']}; "
      f"Files and Notes zoomed to the middle; mwin minimized one window {cols['mwin2']}; the clock not drawn while "
      f"minimized and ticking ({still} pixels changed in 1.5 s, {ticked} changed by the time it was back); "
      f"the dock's dots amber while minimized")
PYS
echo "ok: the yellow button minimizes (keys go to the next window; the dock and run bring it back; a killed program's minimized window is forgotten), the green button zooms and back, Ctrl+O and the Window menu go through the windows"
