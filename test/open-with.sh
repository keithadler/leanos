#!/bin/bash
# Opening a file from Files in the program for it, on a card of its own (tools/mksd.py) with
# edit, view, hello and spoof, a picture pics/red.bmp (60 x 40, one color) and odd.xyz. Files
# cannot start programs: it asks the display (OP_OPEN_WITH, user/app.h), which takes the
# request only from Files, right after the user's key or click in Files' window, and passes
# it to Apps, which starts the program in a free open slot and hands it the file, read-write,
# as Terminal's `run PROG FILE` does.
#
#   1. Terminal writes note.txt. In Files, a click on it and Return: edit opens with it (Apps
#      was not running: the display starts it with the name pending) and shows its text; a
#      key typed in edit is saved to note.txt, which Terminal's cat then shows.
#   2. A double-click on pics (the folder opens), then on red.bmp in it: view shows it, red in
#      the middle of its window (Apps was not running again: it leaves after each start).
#   3. hello, a program's own file, by Return: Apps starts hello.
#   4. odd.xyz by Return: refused, "No program opens that kind of file." in red in the
#      status line, and nothing asked of the display.
#   5. welcome.txt by a double-click, with edit open: a second edit, in another slot, with
#      welcome.txt.
#   6. spoof, from Terminal, sends the display a well-formed request to open welcome.txt in
#      edit, as Files would: refused, only Files may ask, and logged.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/edit.elf build/progs/view.elf build/progs/hello.elf build/progs/spoof.elf \
  build/icons/edit.icon build/icons/view.icon build/icons/hello.icon || fail "the programs did not build"
files=$T/open-with-files
rm -rf "$files" && mkdir -p "$files"
python3 - "$files" <<'PY' || fail "could not make the picture"
import os, sys
sys.path.insert(0, "tools")
from mksamples import bmp
open(os.path.join(sys.argv[1], "red.bmp"), "wb").write(bmp(60, 40, lambda x, y: (220, 40, 40)))
PY
printf 'not a kind of file anything opens\n' > "$files/odd.xyz"
card=$T/sd-open-with.img
python3 tools/mksd.py "$card" edit=build/progs/edit.elf edit.icon=build/icons/edit.icon \
  view=build/progs/view.elf view.icon=build/icons/view.icon hello=build/progs/hello.elf \
  hello.icon=build/icons/hello.icon spoof=build/progs/spoof.elf odd.xyz="$files/odd.xyz" \
  pics/red.bmp="$files/red.bmp" >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, snap, pause, DOCK, TITLE_H
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
LEFT = b"\x1b[D"
def row(r):
    """A press on row r of Files' list (user/files.c: rows of 22 from 40 down). In the top
    folder: welcome.txt, edit, view, hello, spoof, odd.xyz, pics, then note.txt."""
    return wclick("Files", 60, TITLE_H + 40 + 22 * r + 10)
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         b"write note.txt hello from files\r", wait_for("terminal: write note.txt"),
         # 1. note.txt, by Return
         *click(*DOCK["Files"]), wait_for("files: opened a window"),
         *row(7), wait_for("files: showing note.txt"), b"\r", wait_for("edit: opened a window"), pause(0.5),
         snap("open-with-edit"), b"X", wait_for("edit: saved note.txt"),
         # 2. red.bmp in pics, by a double-click
         *click(*DOCK["Files"]), pause(0.5), *row(6), *row(6), wait_for("files: opened pics"), pause(0.5),
         *row(0), *row(0), wait_for("view: drew red.bmp"), pause(0.5), snap("open-with-view"),
         # 3. hello, by Return
         *click(*DOCK["Files"]), pause(0.5), LEFT, pause(0.5), *row(3),
         wait_for("files: showing hello"), pause(0.5), snap("open-with-hints"), b"\r", wait_for("hello: opened a window"),
         # 4. odd.xyz, refused
         *click(*DOCK["Files"]), pause(0.5), *row(5), wait_for("files: showing odd.xyz"), b"\r",
         wait_for("files: open odd.xyz"), pause(0.5), snap("open-with-refused"),
         # 5. welcome.txt, by a double-click, with edit open
         *row(0), *row(0), wait_for("edit: opened welcome.txt"),
         # 6. a forged request, and what Terminal sees of note.txt
         *click(*DOCK["Terminal"]), pause(0.5), b"run spoof\r", wait_for("spoof: done"),
         *click(*DOCK["Terminal"]), pause(0.5), b"cat note.txt\r", wait_for("terminal: cat note.txt")]
sys.exit(boot(150, steps=steps, until="terminal: cat note.txt", sd=card, settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(files: (asked|open)|display: (Files|a program).* asked to open|display: start Apps|apps: |edit: opened|view: (opened|drew)|hello: opened|spoof: open|terminal: cat)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -E "^leanos: .* stopped: " | grep -qvE "^leanos: (carol|mallory) stopped: " && fail "a program stopped on a fault"
failed=0
fail() { echo "FAIL: $*"; failed=1; }
has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }

# 1. note.txt in edit: Files asks, the display passes it on, Apps (started for it) hands it over
has "files: asked to open note.txt in edit -> ok"
has "display: Files asked to open note.txt in edit; passed to Apps"
has "apps: gave edit note.txt -> ok"
has "apps: edit started in slot 10 with note.txt"
has "edit: opened note.txt (16 bytes)"
has "edit: saved note.txt (17 bytes)"
has "terminal: cat note.txt -> 17 bytes"
# 2. the double-click on red.bmp, in a folder
has "files: opened pics"
has "files: asked to open pics/red.bmp in view -> ok"
has "display: Files asked to open pics/red.bmp in view; passed to Apps"
has "apps: gave view pics/red.bmp -> ok"
has "apps: view started in slot 11 with pics/red.bmp"
has "view: opened pics/red.bmp: 60x40, BMP 24-bit"
# 3. a program's own file: the program
has "files: asked to open hello -> ok"
has "display: Files asked to open hello; passed to Apps"
has "apps: hello started in slot 12"
has "hello: opened a window -> ok"
# 4. no program for .xyz: nothing asked of the display
has "files: open odd.xyz -> no program opens that kind of file"
echo "$out" | grep -q "asked to open odd.xyz" && fail "odd.xyz was asked for"
# 5. a second edit, with welcome.txt
has "files: asked to open welcome.txt in edit -> ok"
has "apps: edit started in slot 13 with welcome.txt"
has "edit: opened welcome.txt (169 bytes)"
# Apps was started for each (no window of its own), five times: at boot and for each open
count 5 "display: start Apps -> ok"
# 6. the forged request, refused: the badge is not Files'
has "spoof: open welcome.txt in edit, as Files asks: refused"
has "display: a program from the SD card asked to open a file; refused: only Files may ask"
[ "$(echo "$out" | grep -c "^display: Files asked to open .*; passed to Apps$")" = 4 ] || fail "Files did not ask 4 times"
[ "$(echo "$out" | grep -c "asked to open.*refused")" = 1 ] || fail "a request was refused that should not be, or more than one"

python3 - "$T" <<'PY' || fail "the screen is not what the programs drew"
import os, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
T = sys.argv[1]
log = open(os.path.join(T, "serial.txt")).read()
def load(name, win, before=None):
    """The snapshot, as a window's pixels: where the log put the window (before the line
    `before`, for the first of two windows of one name)."""
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    wx, wy = window_pos(log.split("\n" + before)[0] if before else log, win)
    def at(x, y):
        i = ((wy + TITLE_H + y) * w + wx + x) * 3
        return tuple(px[i:i + 3])
    return at
# edit shows note.txt's text on its first line (dark on light), and nothing on its third
at = load("open-with-edit", "edit", "files: opened pics")
dark = lambda c: max(c) < 120
first = sum(dark(at(x, y)) for x in range(12, 300) for y in range(12, 30))
third = sum(dark(at(x, y)) for x in range(12, 300) for y in range(48, 66))
assert first > 60 and third == 0, ("edit's text", first, third)
# view shows the red picture in the middle of its window (500 x 292 for the picture)
at = load("open-with-view", "view")
assert at(250, 146) == (220, 40, 40) and at(250 - 29, 146) == (220, 40, 40), ("view's middle", at(250, 146))
assert at(250 - 40, 146) != (220, 40, 40), ("the picture is larger than it is", at(250 - 40, 146))
# Files says in red, in its status line, that nothing opens odd.xyz
at = load("open-with-refused", "Files")
red = sum(1 for x in range(8, 300) for y in range(340 - 24, 340 - 2) if at(x, y)[0] > 150 and at(x, y)[1] < 110)
assert red > 40, ("no red message in Files' status line", red)
print(f"ok: edit shows note.txt ({first} dark pixels on its first line), view shows red.bmp, Files' refusal in red ({red} pixels)")
PY
[ $failed = 0 ] || exit 1
echo "ok: Return and a double-click in Files open note.txt in edit, pics/red.bmp in view and hello itself, through the display and Apps; odd.xyz is refused; a second edit opens welcome.txt; a forged request from another program is refused"
