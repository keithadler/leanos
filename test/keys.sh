#!/bin/bash
# The keys a real keyboard has, as a program hears them. restart (user/progs/restart.c), run
# as `keys` on a card of its own, opens a window and prints every event it gets, so the test
# sees each key's code (user/app.h):
#
#   1. From the serial line, each way a terminal sends them: the function keys (ESC O P..S,
#      ESC [ 11 ~ to ESC [ 24 ~), the arrows, Home, End, Page Up and Page Down with Shift
#      (ESC [ 1 ; 2 A and the like, ESC [ 5 ; 2 ~), Shift with a key that has no Shift code
#      (Shift+F1 is F1, Shift+Delete is Delete), and Control with an arrow (ESC [ 1 ; 5 C:
#      dropped, as leanos has no such key). The plain keys are what they were.
#   2. From the USB keyboard: F1, F2, F5, F12, Shift with each of the eight keys that have a
#      Shift code, Shift+Delete, Shift+F3, and Ctrl+Right (dropped).
#   3. F11, from either, never reaches the program: the display zooms its window, and back.
#   4. Ctrl+X and Ctrl+C reach it only as the display's EV_COPY (7), with a = 1 for the cut:
#      a program that does not look at a sees a copy, and restart answers neither.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/restart.elf || fail "restart did not build"
card=$T/sd-keys.img
python3 tools/mksd.py "$card" keys=build/progs/restart.elf >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, usb_key, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
E = lambda s: ("\x1b" + s).encode()          # one escape sequence, sent at once
serial = [E("OP"), E("OQ"), E("OR"), E("OS"), E("[11~"), E("[12~"), E("[13~"), E("[14~"), E("[15~"),
          E("[17~"), E("[18~"), E("[19~"), E("[20~"), E("[21~"), E("[24~"),
          E("[1;2A"), E("[1;2B"), E("[1;2C"), E("[1;2D"), E("[1;2H"), E("[1;2F"), E("[5;2~"), E("[6;2~"),
          E("[1;2P"), E("[3;2~"), E("[1;5C"), E("[A"), E("[1~"), b"s"]
usb = [*usb_key("f1"), *usb_key("f2"), *usb_key("f5"), *usb_key("f12"),
       *[x for k in ("up", "down", "right", "left", "home", "end", "pgup", "pgdn") for x in usb_key(k, shift=True)],
       *usb_key("delete", shift=True), *usb_key("f3", shift=True), *usb_key("right", ctrl=True), *usb_key("u")]
steps = [wait_for("usb: ready"), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         b"run keys\r", wait_for("restart: keys in slot 10: opened"),
         *serial, wait_for("restart: keys in slot 10: event 1 s"), pause(0.3),
         *usb, wait_for("restart: keys in slot 10: event 1 u"), pause(0.3),
         E("[23~"), wait_for("display: keys zoomed"), pause(0.3),
         *usb_key("f11"), wait_for("display: keys zoomed back"), pause(0.3),
         b"\x18", wait_for("restart: keys in slot 10: event 7 1"), pause(2.3),
         b"\x03", wait_for("restart: keys in slot 10: event 7 0"), b"e"]
sys.exit(boot(90, usb=True, steps=steps, until="restart: keys in slot 10: event 1 e", sd=sys.argv[1], settle=0.3))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(restart: keys|display: (keys zoomed|cut|copy))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"

got=$(echo "$out" | grep "^restart: keys in slot 10: event " | sed 's/^restart: keys in slot 10: event //')
want="1 145 0
1 146 0
1 147 0
1 148 0
1 145 0
1 146 0
1 147 0
1 148 0
1 149 0
1 150 0
1 151 0
1 152 0
1 153 0
1 154 0
1 156 0
1 137 0
1 138 0
1 139 0
1 140 0
1 141 0
1 142 0
1 143 0
1 144 0
1 145 0
1 134 0
1 128 0
1 132 0
1 s 0
1 145 0
1 146 0
1 149 0
1 156 0
1 137 0
1 138 0
1 139 0
1 140 0
1 141 0
1 142 0
1 143 0
1 144 0
1 134 0
1 147 0
1 u 0
7 1 0
7 0 0
1 e 0"
[ "$got" = "$want" ] || fail "the program did not hear exactly these keys: $(diff <(echo "$want") <(echo "$got"))"
has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
has "display: keys zoomed"
has "display: keys zoomed back"
has "display: cut: asked a program from the SD card for its text"
has "display: copy: asked a program from the SD card for its text"
echo "$out" | grep -q "^display: copied" && fail "the display took a copy nobody sent"
echo "ok: the function keys and Shift with the arrows, Home, End and the page keys reach a program as their codes, from the serial line and the USB keyboard; F11 zooms; Ctrl+X asks for a cut"
