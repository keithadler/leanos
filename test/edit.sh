#!/bin/bash
# The editor from the card, given one file: Terminal writes memo.txt, runs `edit memo.txt`
# (which gives edit that file and its own folder, nothing else), types into it, and the
# change is saved by itself; Terminal reads it back. Then the keys above the arrows, from
# the serial line (each way a terminal sends them) and from the USB keyboard: End and a
# second line; Home and End around it; Up, Home and Delete (four letters go), End and a
# letter, Delete at the line's end (the second line joins the first); twenty short lines,
# Page Up 14 lines up (a mark), Page Down back (a mark), Page Up twice to the first line
# (a mark at the same column). The file, saved again, holds each change where it was
# made. Then edit, given nothing, opens a new file in its own folder, apps/edit.
#
# Then, on a card of its own, sel.txt ("alpha beta gamma"), by the mouse and the keys:
#   - a click before "beta" puts the cursor there (line 1, column 7), and "big " goes in;
#   - a drag over "beta" selects it (drawn highlighted, checked on screen), and "BETA" is
#     typed over it; Ctrl+Z takes that back (beta again, selected), Ctrl+Y does it again,
#     Ctrl+Z takes it back again;
#   - Ctrl+C copies the selection ("beta", 4 bytes), End, a space and Ctrl+V paste it;
#   - Ctrl+A selects all, Ctrl+C copies it, and it is pasted as a second line;
#   - Ctrl+F finds "gamma" as it is typed (first "g" in "big", then "gamma" on line 1),
#     Return the next (line 2), "x" finds nothing, Backspace finds it again, Escape (the USB
#     keyboard's: the serial line cannot send one alone) closes the field, and "GAMMA" is
#     typed over the match;
#   - Ctrl+G 1 goes to line 1; a double-click selects the word "big", and "small" replaces
#     it; Home, Ctrl+B (the mark) and Right six times select "#alpha", Backspace deletes it;
#   - a Tab, and a click at column 5 lands after it (a tab shows as 4 columns);
#   - closing the window saves: the file, read off the card image, is exactly what was
#     typed.
# And on a third card, big.txt (59,800 bytes, 2,300 lines, more than one 16 KiB request) and
# huge.txt (70,000 bytes, more than the 64 KiB edit holds): big.txt opens whole; Ctrl+G
# 1500, a word; Ctrl+G 1, a word; Ctrl+S; Ctrl+G past the end, a word; closing saves it.
# huge.txt is not opened, and typing into it and Ctrl+S never save over it. Off the card
# image: big.txt is the original with the three words where they were typed, huge.txt is as
# it was, and no apps/edit/save.part~ is left behind.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, pause, usb_key, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
term = wclick("Terminal", 230, 60)      # in Terminal's window, where edit's does not cover it
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("write memo.txt hello\r"), wait_for("terminal: write"),
         *keys("run edit memo.txt\r"), wait_for("edit: opened a window"),
         *keys("Say "), wait_for("edit: saved"),
         # (a moment between the serial line and the USB keyboard: they reach the display apart)
         b"\x1b[F", *keys("\rtwo"), pause(0.3), *usb_key("home"), pause(0.3), *keys("["), pause(0.3),
         *usb_key("end"), pause(0.3), *keys("]"),
         b"\x1b[A", b"\x1bOH", b"\x1b[3~", b"\x1b[3~", b"\x1b[3~", pause(0.3), *usb_key("delete"), pause(0.3),
         b"\x1b[4~", *keys("!"), b"\x1b[3~", b"\x1b[8~", *keys("".join(f"\rL{i}" for i in range(1, 21))),
         b"\x1b[5~", *keys("^"), pause(0.3), *usb_key("pgdn"), pause(0.3), *keys("~"),
         b"\x1b[5~", b"\x1b[5~", *keys("_"), wait_for("edit: saved memo.txt (85"),
         *term, *keys("cat memo.txt\r"), wait_for("terminal: cat"),
         *keys("grep hel_lo![two] memo.txt\r"), wait_for("terminal: grep hel_lo"),
         *keys("grep L6^ memo.txt\r"), wait_for("terminal: grep L6^"),
         *keys("grep L20~ memo.txt\r"), wait_for("terminal: grep L20~"),
         *keys("wc memo.txt\r"), wait_for("terminal: wc"),
         *keys("ls apps\r"), wait_for("terminal: ls")]
sys.exit(boot(120, usb=True, steps=[wait_for("usb: ready")] + steps, until="terminal: ls apps", settle=0.5))
PY
)
status=$?
echo "$out" | grep -E "^(edit|terminal: (write|run|gave|cat|ls|grep|wc)|fs: refused)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "terminal: gave edit memo.txt -> ok" || fail "Terminal did not give edit the file"
echo "$out" | grep -qx "edit: opened memo.txt (5 bytes)" || fail "edit did not open the file it was given"
echo "$out" | grep -qx "edit: saved memo.txt (9 bytes)" || fail "edit did not save"
echo "$out" | grep -qx "edit: saved memo.txt (85 bytes)" || fail "edit did not save the keys' changes"
echo "$out" | grep -qx "terminal: cat memo.txt -> 85 bytes" || fail "the saved file did not read back"
for w in "hel_lo![two]" "L6^" "L20~"; do
  echo "$out" | grep -qxF "terminal: grep $w -> 1 line" || fail "Home, End, Delete or the page keys: no $w in the file"
done
echo "$out" | grep -qx "terminal: wc memo.txt -> 20 lines, 21 words, 85 bytes" || fail "the file does not have its 21 lines"
echo "$out" | grep -qx "terminal: ls apps -> 1 file" || fail "edit's own folder was not made"
echo "ok: edit opens only the file it was given, saves it by itself, and has a folder of its own"

# ---- the mouse, selections, copy and paste, undo, find ----
card=$T/sd-edit-sel.img
cp build/sd-template.img "$card" || fail "no card"
rm -f "$T"/edit-selected.* "$T"/edit-find.*
out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wmouse, wait_for, pause, snap, usb_key, wclick, DOCK, TITLE_H, CLOSE
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
CW, PAD, LINE_H = 9, 12, 18              # the monospaced font's width, and edit's layout (edit.c)
X = lambda col: PAD + CW * col + 1       # just right of the boundary before column `col` (from 0)
Y = lambda row: TITLE_H + PAD + LINE_H * row + LINE_H // 2
at = lambda kind, col, row=0: wmouse(kind, "edit", X(col), Y(row))
CTRL = lambda c: bytes([ord(c) - 96])
END, HOME, RIGHT = b"\x1b[F", b"\x1b[H", b"\x1b[C"
steps = [wait_for("usb: ready"), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("write sel.txt alpha beta gamma\r"), wait_for("terminal: write"),
         *keys("run edit sel.txt\r"), wait_for("edit: opened a window"),
         at("d", 6), at("u", 6), wait_for("edit: cursor at"), *keys("big "),
         at("d", 10), at("v", 12), at("v", 14), at("u", 14), wait_for("edit: selected"),
         pause(0.3), snap("edit-selected"), *keys("BETA"),
         CTRL("z"), wait_for("edit: undid"), CTRL("y"), wait_for("edit: redid"), CTRL("z"), wait_for("edit: undid", 2),
         CTRL("c"), wait_for("display: copied"), END, b" ", CTRL("v"), wait_for("edit: pasted"),
         CTRL("a"), wait_for("edit: selected", 2), CTRL("c"), wait_for("display: copied", 2),
         END, b"\r", CTRL("v"), wait_for("edit: pasted", 2),
         CTRL("f"), *keys("gamma"), wait_for('edit: find "gamma"'), b"\r", wait_for('edit: find "gamma"', 2), pause(0.3), snap("edit-find"),
         b"x", wait_for('edit: find "gammax"'), b"\x7f", wait_for('edit: find "gamma"', 3),
         pause(0.3), *usb_key("esc"), pause(0.3), *keys("GAMMA"),
         CTRL("g"), *keys("1\r"), wait_for("edit: went to line"), b"#",
         at("d", 8), at("u", 8), at("d", 8), at("u", 8), wait_for("edit: selected", 3), *keys("small"),
         HOME, CTRL("b"), *[RIGHT] * 6, b"\x7f", b"\t", at("d", 4), at("u", 4), wait_for("edit: cursor at", 2), b"T",
         *wclick("edit", *CLOSE), wait_for("edit: window closed")]
sys.exit(boot(120, usb=True, steps=steps, until="edit: window closed", sd=sys.argv[1], settle=0.3))
PY
)
status=$?
echo "$out" > "$T/edit-sel.txt"
echo "$out" | grep -E "^(edit|display: (copied|paste))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }
has "edit: opened sel.txt (16 bytes)"
has "edit: cursor at line 1, column 7"
has "edit: selected 4 bytes at line 1, column 11: beta"
has "edit: undid typing; 1 step to undo, 1 to redo"
has "edit: redid typing; 2 steps to undo, 0 to redo"
count 2 "edit: undid typing; 1 step to undo, 1 to redo"
has "edit: copied 4 bytes -> ok"
has "edit: pasted 4 bytes"
has "edit: selected 25 bytes at line 1, column 1: alpha big beta gamma beta"
has "edit: copied 25 bytes -> ok"
has "edit: pasted 25 bytes"
has 'edit: find "g": at line 1, column 9'
has 'edit: find "gamma": at line 1, column 16'
count 2 'edit: find "gamma": at line 2, column 16'
has 'edit: find "gammax": not found'
has "edit: went to line 1"
has "edit: selected 3 bytes at line 1, column 8: big"
has "edit: mark set at line 1, column 1"
has "edit: cursor at line 1, column 5"
has "edit: saved sel.txt (50 bytes)"

# ---- a file larger than one request, and one larger than edit holds ----
big=$T/edit-big.txt
huge=$T/edit-huge.txt
card2=$T/sd-edit-big.img
python3 - "$big" "$huge" <<'PY' || fail "could not make big.txt"
import sys
open(sys.argv[1], "w").write("".join(f"line {i:04d} of the big file\n" for i in range(1, 2301)))
open(sys.argv[2], "w").write("".join(f"{i:05d}huge\n" for i in range(7000)))
PY
[ "$(wc -c < "$big" | tr -d ' ')" = 59800 ] || fail "big.txt is not 59800 bytes"
[ "$(wc -c < "$huge" | tr -d ' ')" = 70000 ] || fail "huge.txt is not 70000 bytes"
python3 tools/mksd.py "$card2" edit=build/progs/edit.elf edit.icon=build/icons/edit.icon big.txt="$big" \
  huge.txt="$huge" >/dev/null || fail "no card for big.txt"
out=$(python3 - "$card2" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, wclick, DOCK, CLOSE
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
GOTO, SAVE = b"\x07", b"\x13"
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run edit big.txt\r"), wait_for("edit: opened a window"),
         GOTO, *keys("1500\r"), wait_for("edit: went to line 1500"), *keys("MARK "),
         GOTO, *keys("1\r"), wait_for("edit: went to line 1", 2), *keys("TOP "), SAVE,
         wait_for("edit: saved big.txt (59809 bytes)"),
         GOTO, *keys("99999\r"), wait_for("edit: went to line 2301"), *keys("END"),
         *wclick("edit", *CLOSE), wait_for("edit: window closed"),
         *keys("run edit huge.txt\r"), wait_for("edit: opened a window", 2), *keys("x"), SAVE, pause(1.5),
         *wclick("edit", *CLOSE), wait_for("edit: window closed", 2), *keys("ls apps/edit\r")]
sys.exit(boot(120, steps=steps, until="terminal: ls apps/edit", sd=sys.argv[1], settle=0.3))
PY
)
status=$?
echo "$out" | grep -E "^(edit|terminal: (gave|ls)|fs: refused)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run with big.txt did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
has "edit: opened big.txt (59800 bytes)"
has "edit: went to line 1500"
has "edit: saved big.txt (59812 bytes)"
has "edit: opened huge.txt (70000 bytes, more than 65536: not opened, never saved over)"
echo "$out" | grep -q "^edit: saved huge.txt" && fail "huge.txt was saved over"
has "terminal: ls apps/edit -> 0 files"

# The files, off the card: the file system of user/fs.c (as test/paint.sh reads it).
python3 - "$card2" "$big" "$huge" "$card" <<'PY' || fail "the files on the card are not what was typed"
import struct, sys

def files(path):
    img = open(path, "rb").read()
    start = next(struct.unpack_from("<I", img, 446 + 16 * i + 8)[0] for i in range(4) if img[446 + 16 * i + 4] == 0xDA)
    part = img[start * 512:]
    (magic, version, total, jstart, jblocks, bstart, bblocks, istart, icount, dstart,
     clusters) = struct.unpack_from("<8s10I", part, 0)
    assert magic == b"LEANOSF2", magic
    cl = lambda c: part[(dstart + c * 8) * 512:(dstart + c * 8) * 512 + 4096]
    def read(ino):
        kind, _, size, *rest = struct.unpack_from("<HHI12III", part, istart * 512 + 64 * ino)
        direct, ind = rest[:12], rest[12]
        ptrs = list(direct) + (list(struct.unpack("<1024I", cl(ind))) if ind else [])
        return b"".join(cl(c) for c in ptrs[:(size + 4095) // 4096])[:size]
    def walk(ino, prefix):
        data = read(ino)
        for at in range(0, len(data), 64):
            e, kind = struct.unpack_from("<II", data, at)
            name = data[at + 8:at + 64].split(b"\0")[0].decode()
            if not e:
                continue
            yield prefix + name, e, kind
            if kind == 2:
                yield from walk(e, prefix + name + "/")
    return {name: (read(e) if kind == 1 else None) for name, e, kind in walk(1, "")}

f = files(sys.argv[1])
orig = open(sys.argv[2], "rb").read()
at = 1499 * 26                           # line 1500's start: every line is 26 bytes
want = b"TOP " + orig[:at] + b"MARK " + orig[at:] + b"END"
got = f["big.txt"]
assert got == want, ("big.txt", len(got), len(want), next((i for i in range(min(len(got), len(want))) if got[i] != want[i]), None))
assert f["huge.txt"] == open(sys.argv[3], "rb").read(), "huge.txt changed"
assert not [n for n in f if n.endswith(".part~")], [n for n in f if n.endswith(".part~")]
sel = files(sys.argv[4])["sel.txt"]
assert sel == b"\tT small beta gamma beta\nalpha big beta GAMMA beta", sel
print("ok: big.txt holds the three words where they were typed, huge.txt is as it was, sel.txt is what was typed")
PY

# The drag's selection, on screen: edit's light blue behind "beta" (and the word on it).
python3 - "$T" <<'PY' || fail "the selection is not drawn highlighted"
import os, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
T = sys.argv[1]
ex, ey = window_pos(open(os.path.join(T, "edit-sel.txt")).read(), "edit")
data = open(os.path.join(T, "edit-selected.ppm"), "rb").read()
_, dims, _, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
at = lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
row = range(ey + TITLE_H + 12, ey + TITLE_H + 30)
lit = lambda x0, x1: sum(1 for y in row for x in range(ex + x0, ex + x1) if at(x, y) == (191, 213, 250))
inside, outside = lit(12 + 9 * 10 + 1, 12 + 9 * 14 - 1), lit(12, 12 + 9 * 10 - 1)
assert inside > 200 and outside == 0, (inside, outside)
print("ok: the selection is drawn highlighted")
PY
echo "ok: a click places the cursor, a drag and a double-click select, typing replaces a selection, select all and a mark, copy of a selection, undo and redo, find, go to a line, tabs, and a file of 59,800 bytes saved in pieces and read back off the card"
