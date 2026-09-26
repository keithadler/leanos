#!/bin/bash
# Copy and paste, and the rule behind it: text moves between programs only by the user's
# hand. At boot mallory asks the display for the clipboard (there is no such request) and
# puts text on it unasked (refused), so a paste into Notes finds nothing. Then text typed in
# Notes is copied (Ctrl+C on the serial line) and pasted into Terminal (Ctrl+V on the USB
# keyboard), which must receive exactly that text; Terminal's output goes back into Notes,
# and into `edit` through the Edit menu. The tour's clipboard page asks for what was copied
# and copies unasked, once with no copy asked of it and once 2.5 s after Ctrl+C in its
# window (too late): both refused, and the next paste is still what the user copied.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

rm -f "$T"/paste-*.png "$T"/edit-menu.png "$T"/tour-clipboard.png "$T/screen.png"
out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, snap, usb_key, wclick, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
TERM = wclick("Terminal", 364, 100)     # in Terminal's window, where no other window covers it
keys = lambda s: [c.encode() for c in s]
COPY, PASTE, LEFT, RIGHT = b"\x03", b"\x16", b"\x1b[D", b"\x1b[C"
steps = [wait_for("usb: ready"),
         PASTE, wait_for("display: paste: nothing"),                      # Notes is in front
         *keys("echo copied by hand"), COPY, wait_for("display: copied"),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *usb_key("v", ctrl=True), wait_for("terminal: pasted"), pause(0.5), snap("paste-terminal"),
         b"\r", pause(0.3), *usb_key("c", ctrl=True), wait_for("display: copied", 2),   # what echo printed
         *wclick("alice", 14, 124), b"\r", PASTE, wait_for("alice: pasted"), pause(0.5), snap("paste-notes"),
         wait_for("alice: saved note 1 (34"),
         *TERM, *keys("run edit\r"), wait_for("edit: opened a window"),
         *click(165, 15), wait_for("display: the Edit menu"), pause(0.3), snap("edit-menu"),
         *click(180, 80), wait_for("edit: pasted"), wait_for("edit: saved"), pause(0.3), snap("paste-edit"),
         *TERM, *keys("tour\r"), wait_for("tour: opened"),
         *[b"\r"] * 5, wait_for("tour: What you copy"), pause(0.3), snap("tour-clipboard"),
         COPY, wait_for("display: copy: asked a program"), pause(2.5),
         LEFT, RIGHT, wait_for("tour: What you copy", 2),
         *TERM, *keys("cat notes/1.txt\r"), wait_for("terminal: cat notes/1.txt"),
         PASTE, wait_for("terminal: pasted", 2), COPY]
sys.exit(boot(120, usb=True, steps=steps, until="terminal: copied the command line", settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"            # where each window opened, for the pixel checks
echo "$out" | grep -E "^(mallory: (ask|put)|alice: (copied|pasted|saved)|terminal: (copied|pasted|cat|run)|edit: (copied|pasted|saved)|tour: What|display: (copy|copied|paste|the Edit|.*(copy|request)))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"

has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }

# Nothing reads the clipboard by asking, and nobody puts text on it unasked.
has "mallory: ask the display for what was copied -> refused, it has no such request"
has "mallory: put text on the clipboard without being asked -> refused"
has "display: mallory sent a copy nobody asked for; refused"
has "display: paste: nothing has been copied"

# Notes to Terminal: exactly what was typed.
has "display: copy: asked alice for its text"
has "alice: copied 19 bytes -> ok"
has "display: copied 19 bytes from alice"
has "display: paste: 19 bytes to Terminal"
has "terminal: pasted 19 bytes: echo copied by hand"

# Terminal (what echo printed) to Notes, and to edit through the Edit menu.
has "terminal: copied the last command's output, 14 bytes -> ok"
has "display: copied 14 bytes from Terminal"
has "display: paste: 14 bytes to alice"
has "alice: pasted 14 bytes"
has "alice: saved note 1 (34 bytes)"
has "terminal: cat notes/1.txt -> 34 bytes"
has "display: the Edit menu, for a program from the SD card"
has "display: paste: 14 bytes to a program from the SD card"
has "edit: pasted 14 bytes"
has "edit: saved apps/edit/untitled.txt (14 bytes)"

# The tour: no request reads the clipboard, a copy nobody asked for is refused, and so is
# one that comes after the 2 seconds a copy is open for. The clipboard is still Terminal's.
count 2 "tour: What you copy: Read the clipboard, and write it unasked -> refused, no such request; not asked"
has "display: a program from the SD card sent a copy nobody asked for; refused"
has "display: copy: asked a program from the SD card for its text"
has "display: a program from the SD card answered a copy too late; refused"
has "display: paste: 14 bytes to Terminal"
has "terminal: pasted 14 bytes: copied by hand"
has "terminal: copied the command line, 14 bytes -> ok"
count 2 "display: copied 14 bytes from Terminal"
[ "$(echo "$out" | grep -c "^display: copied ")" = 3 ] || fail "the clipboard changed more often than the user copied"

# Ctrl+C and Ctrl+V never reach an app as keys, from the serial line or the USB keyboard:
# the only keys the display logs as '?' (not printable) are the tour's two arrows.
[ "$(echo "$out" | grep -c "^display: key '?' to")" = 2 ] || fail "a control key reached an app"

python3 - "$T" <<'PYS' || fail "the screens are not what copy and paste drew"
import os, sys
sys.path.insert(0, "test")
from run import window_pos
log = open(os.path.join(sys.argv[1], "serial.txt")).read()
tx, ty = window_pos(log, "Terminal")
ex, ey = window_pos(log, "edit")
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
# Terminal's prompt line holds the pasted command: light text on its dark window, after "$ "
at = load("paste-terminal")
assert sum(1 for y in range(ty + 58, ty + 78) for x in range(tx + 24, tx + 194) if min(at(x, y)) > 150) > 150, \
    "the pasted command"
# the Edit menu is open under its name: a light panel below the menu bar; edit's page is
# still empty behind it
at = load("edit-menu")
assert all(min(at(x, 40)) > 220 for x in range(160, 310)), ("the Edit menu", at(200, 40))
edit_text = lambda at: sum(1 for y in range(ey + 38, ey + 58) for x in range(ex + 12, ex + 144) if max(at(x, y)) < 110)
assert edit_text(at) < 5, ("edit's page before the paste", edit_text(at))
# then edit shows the pasted text on its first line: dark text on its light page
assert edit_text(load("paste-edit")) > 100, "edit's pasted line"
print("ok: the pasted command on Terminal's prompt, the Edit menu and edit's pasted line are on screen")
PYS
echo "ok: text moves between Notes, Terminal and edit only when the user copies and pastes; nothing else reads or writes the clipboard"
