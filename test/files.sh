#!/bin/bash
# Files as a file manager, on a card of its own (tools/mksd.py) holding welcome.txt, a.txt,
# b.txt and c.txt, with a USB keyboard for Escape (the serial line has no Escape key alone).
# Everything is done with Files' keys and clicks, and checked in its log and through Terminal:
#
#   N makes "untitled folder", named at once: box. N again, left as it is, then the + Folder
#   button makes "untitled folder 2", named sub. R on box refuses a/b, an empty name, a.txt
#   (taken) and a name of 56 characters, each with a message in red; Escape cancels it, and so
#   does a click elsewhere. C on a folder is refused. C marks a.txt, V in box puts a copy there,
#   and V again "a copy.txt", which R renames to pear.txt (typing replaces the name without its
#   extension); R and Escape leave it so. X marks b.txt, V in box moves it; X marks box, V in
#   sub moves the folder with all in it; X marks sub, V inside sub is refused (a folder cannot
#   go inside itself). Delete removes the empty "untitled folder"; Terminal's find, ls, cat and
#   df see all of it. Delete on sub asks first; another key keeps it; Delete twice removes it
#   and the 4 things in it. Then text copied in Terminal is pasted (Ctrl+V) into a name.
#   Last, a copy is made in NAME.part~, as Terminal's cp makes one: in a folder t that holds
#   the user's file c.txt.tmp, a folder kiwi.txt.tmp, a file c.txt.part~ (what a power cut
#   leaves) and a folder welcome.txt.part~, V copies c.txt and kiwi.txt there and leaves the
#   .tmp ones alone and no .part~ file behind, and refuses welcome.txt, whose folder stays.
#
# Then the pixels: the name field while box is typed (white, a blue edge, a text cursor, not
# the selected row's blue), the red refusal and the Move mark in the status line.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

files=$T/files-mgr-files
rm -rf "$files" && mkdir -p "$files"
printf 'apple\n' > "$files/a.txt"
printf 'banana split\n' > "$files/b.txt"
printf 'cherry\n' > "$files/c.txt"
card=$T/sd-files.img
python3 tools/mksd.py "$card" a.txt="$files/a.txt" b.txt="$files/b.txt" c.txt="$files/c.txt" >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, usb_key, snap, pause, DOCK, TITLE_H
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
COPY, PASTE = b"\x03", b"\x16"
LEFT, DEL, ESC = b"\x1b[D", b"\x7f", usb_key("esc")
seen = {}
def after(prefix):
    """Wait for the next line starting with prefix (counting those before)."""
    seen[prefix] = seen.get(prefix, 0) + 1
    return wait_for(prefix, seen[prefix])
def row(r):
    """A click on row r of Files' list (user/files.c: rows of 22 from 40 down). Keys and clicks
    on the serial line reach Files in order, so nothing waits for it; the USB keyboard's
    Escape comes another way, and waits for what came before it."""
    return wclick("Files", 60, TITLE_H + 40 + 22 * r + 10)
def cmd(line, done=None):
    return [(line + "\r").encode(), after(done or "terminal: " + line.split()[0] + " ")]
def shown():
    """What the last command printed, copied, and pasted onto the command line after echo."""
    return [COPY, after("terminal: copied the last command's output"), b"echo ", PASTE, after("terminal: pasted"), b"\r"]
steps = [wait_for("usb: ready"), *click(*DOCK["Files"]), wait_for("files: opened a window"),
         # a new folder, named box as it is made: the field drawn with its name selected, and
         # while box is typed
         b"n", after("files: renaming "), pause(0.5), snap("files-new"), b"box", after("display: key 'x' to Files"), pause(0.5), snap("files-field"),
         b"\r", after("files: renamed "),
         # N again, kept as it is; then the + Folder button: untitled folder 2, named sub
         b"N", after("files: renaming "), b"\r", after("files: kept the name "),
         *wclick("Files", 140, TITLE_H + 21), after("files: renaming "), b"sub\r", after("files: renamed "),
         # names refused, then Escape; then a click elsewhere cancels
         *row(4), b"r", after("files: renaming "), b"a/b\r", after("files: renamed "), pause(0.5), snap("files-refused"),
         DEL * 3, b"\r", after("files: renamed "), b"a.txt\r", after("files: renamed "),
         b"x" * 51 + b"\r", after("files: renamed "), *ESC, after("files: rename of "),
         b"r", after("files: renaming "), b"zzz", *wclick("Files", 300, TITLE_H + 150), after("files: rename of "),
         b"c", after("files: copy "),
         # copy a.txt into box, twice
         *row(1), b"c", after("files: marked "), *row(4), b"\r", after("files: opened box"),
         b"v", after("files: copied "), b"v", after("files: copied "),
         # rename the second copy, then a rename cancelled with Escape
         b"r", after("files: renaming "), b"pear\r", after("files: renamed "),
         b"R", after("files: renaming "), b"zzz", pause(0.5), *ESC, after("files: rename of "),
         # move b.txt into box
         LEFT, *row(2), b"x", after("files: marked "), pause(0.5), snap("files-marked"),
         *row(4), b"\r", after("files: opened box"), b"v", after("files: moved "),
         # move box into sub; sub into itself is refused
         LEFT, *row(3), b"X", after("files: marked "), *row(5), b"\r", after("files: opened sub"),
         b"v", after("files: moved "), LEFT,
         *row(4), b"x", after("files: marked "), b"\r", after("files: opened sub"), b"v", after("files: moved "),
         *ESC, after("files: forgot "), LEFT,
         # the empty untitled folder goes at once, by the USB keyboard's Delete (forward
         # delete) key, as Backspace does
         *row(3), *usb_key("delete"), after("files: deleted "),
         # what Terminal sees
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *cmd("find"), *shown(), *cmd("ls"), *cmd("cat sub/box/pear.txt"), *shown(), *cmd("cat sub/box/b.txt"), *shown(),
         *cmd("df"),
         # sub, with all in it: Delete asks; q keeps it; Delete twice deletes it
         *click(*DOCK["Files"]), pause(0.5), *row(2), *row(3), DEL, after("files: sub is not empty"), pause(0.5), snap("files-confirm"),
         b"q", DEL, after("files: sub is not empty"), DEL, after("files: deleted "),
         *click(*DOCK["Terminal"]), pause(0.5), *cmd("find"), *shown(), *cmd("df"),
         # a name pasted from Terminal's command line
         b"kiwi", COPY, after("terminal: copied the command line"),
         *click(*DOCK["Files"]), pause(0.5), *row(1), b"r", after("files: renaming "), PASTE,
         after("files: pasted into the name"), b"\r", after("files: renamed "),
         # a copy is made in NAME.part~, as Terminal's cp makes one: in t, a file c.txt.tmp of
         # the user's and a folder kiwi.txt.tmp are left alone, a file c.txt.part~ (what a
         # power cut leaves) is written over, and a folder welcome.txt.part~ refuses the copy
         *click(*DOCK["Terminal"]), pause(0.5), DEL * 4,
         *cmd("mkdir t"), *cmd("write t/c.txt.tmp mine"), *cmd("write t/c.txt.part~ left by a power cut"),
         *cmd("mkdir t/kiwi.txt.tmp"), *cmd("mkdir t/welcome.txt.part~"),
         *click(*DOCK["Files"]), pause(0.5),
         *row(3), b"c", after("files: marked "), *row(2), b"\r", after("files: opened t"), b"v", after("files: copied "),
         LEFT, *row(1), b"c", after("files: marked "), *row(2), b"\r", after("files: opened t"), b"v", after("files: copied "),
         LEFT, *row(0), b"c", after("files: marked "), *row(2), b"\r", after("files: opened t"), b"v", after("files: copied "),
         *click(*DOCK["Terminal"]), pause(0.5),
         *cmd("find t"), *shown(), *cmd("cat t/c.txt.tmp"), *shown(), *cmd("cat t/c.txt"), *shown(),
         *cmd("cat t/kiwi.txt")]
sys.exit(boot(200, steps=steps, until="terminal: cat t/kiwi.txt ", sd=card, usb=True, settle=1))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(files: |terminal: )" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"

has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }
pasted() { local n; n=$(printf '%s' "$1" | wc -c | tr -d ' '); has "terminal: pasted $n bytes: $1"; }

# new folders, named as they are made; the second is "untitled folder 2", from the button
count 2 "files: made folder untitled folder -> ok"
has "files: renamed untitled folder to box -> ok"
has "files: kept the name untitled folder"
has "files: made folder untitled folder 2 -> ok"
has "files: renamed untitled folder 2 to sub -> ok"
# names refused, and renames cancelled: by Escape, by a click elsewhere
has "files: renamed box to a/b -> refused, a name cannot hold /"
has "files: renamed box to  -> refused, a name is needed"
has "files: renamed box to a.txt -> refused, that name is taken here"
has "files: renamed box to a.txt$(printf 'x%.0s' $(seq 1 51)) -> refused, a name has 55 characters at most"
count 2 "files: rename of box cancelled"
has "files: rename of box/pear.txt cancelled"
# copies: a file, twice into one folder; not a folder
has "files: copy box -> refused, copies files, not folders"
has "files: marked a.txt to copy"
has "files: copied a.txt to box/a.txt -> ok, 6 bytes"
has "files: copied a.txt to box/a copy.txt -> ok, 6 bytes"
has "files: renamed box/a copy.txt to box/pear.txt -> ok"
# moves: a file, a folder with what is in it, and not a folder into itself
has "files: marked b.txt to move"
has "files: moved b.txt to box/b.txt -> ok"
has "files: moved box to sub/box -> ok"
has "files: moved sub to sub/sub -> refused, a folder cannot go inside itself"
has "files: forgot sub"
# deletes: an empty folder at once; one with things in it after asking (q keeps it)
has "files: deleted untitled folder -> ok"
count 2 "files: sub is not empty (1 in it): asked before deleting it"
has "files: deleted sub and the 4 things in it -> ok"
# a name pasted from Terminal (kiwi, over a.txt's name without its extension)
has "terminal: copied the command line, 4 bytes -> ok"
has "files: pasted into the name: kiwi.txt"
has "files: renamed a.txt to kiwi.txt -> ok"

# what Terminal saw: the tree after the moves, the copies' contents, and the tree after the delete
has "terminal: find -> 8 found"
pasted "welcome.txt a.txt c.txt sub/ sub/box/ sub/box/a.txt sub/box/pear.txt sub/box/b.txt"
has "terminal: ls -> 4 files"
has "terminal: cat sub/box/pear.txt -> 6 bytes"
pasted "apple"
has "terminal: cat sub/box/b.txt -> 13 bytes"
pasted "banana split"
has "terminal: find -> 3 found"
pasted "welcome.txt a.txt c.txt"
# the free space Files logs is the file server's, as df tells it
dfs=$(echo "$out" | sed -n 's/^terminal: df -> \([0-9]*\) KiB free of .*/\1/p')
frees=$(echo "$out" | sed -n '/^terminal: mkdir t /q;p' | sed -n 's/^files: \([0-9]*\) KiB free$/\1/p')
[ "$(echo "$dfs" | wc -l | tr -d ' ')" = 2 ] || fail "df did not answer twice"
before=$(echo "$out" | sed -n '/^terminal: df /q;p' | sed -n 's/^files: \([0-9]*\) KiB free$/\1/p' | tail -1)
[ "$before" = "$(echo "$dfs" | sed -n 1p)" ] || fail "Files said $before KiB free, df $(echo "$dfs" | sed -n 1p)"
[ "$(echo "$frees" | tail -1)" = "$(echo "$dfs" | sed -n 2p)" ] || fail "after the delete, Files said $(echo "$frees" | tail -1) KiB free, df $(echo "$dfs" | sed -n 2p)"
[ "$(echo "$frees" | head -1)" -lt "$(echo "$frees" | tail -1)" ] || fail "b.txt gone, no more is free"
# a copy is made in NAME.part~, as Terminal's cp makes one: the user's c.txt.tmp (a file) and
# kiwi.txt.tmp (a folder) stay as they were; the file c.txt.part~ a power cut left is written
# over and gone once the copy is in place; a folder welcome.txt.part~ refuses the copy, and stays
has "files: copied c.txt to t/c.txt -> ok, 7 bytes"
has "files: copied kiwi.txt to t/kiwi.txt -> ok, 6 bytes"
has "files: copied welcome.txt to t/welcome.txt -> refused, NAME.part~ is a folder: rename it first"
has "terminal: find t -> 5 found"
pasted "t/c.txt.tmp t/c.txt t/kiwi.txt.tmp/ t/welcome.txt.part~/ t/kiwi.txt"
has "terminal: cat t/c.txt.tmp -> 4 bytes"
pasted "mine"
has "terminal: cat t/c.txt -> 7 bytes"
pasted "cherry"
has "terminal: cat t/kiwi.txt -> 6 bytes"

python3 - "$T" <<'PY' || fail "the screen is not what Files drew"
import os, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
log = open(os.path.join(sys.argv[1], "serial.txt")).read()
wx, wy = window_pos(log, "Files")
top = wy + TITLE_H
row4 = top + 40 + 22 * 4                     # box's row: the field, 20 high, from x 8 to 176
dark = lambda p: max(p) < 90
blue = lambda p: p[2] > 200 and p[0] < 90    # the selection's blue, and the field's edge
red = lambda p: p[0] > 170 and p[1] < 110 and p[2] < 110
def area(at, x0, y0, x1, y1, pred):
    return sum(1 for y in range(y0, y1) for x in range(x0, x1) if pred(at(x, y)))

# the name field while box is typed: white inside, not the selected row's blue; a blue edge;
# the letters; and right of them the text cursor, one column dark from top to bottom
f = load("files-field")
assert f(wx + 120, row4 + 10) == (255, 255, 255), ("the field is white", f(wx + 120, row4 + 10))
assert blue(f(wx + 9, row4 + 10)) and blue(f(wx + 120, row4)), "the field's blue edge"
assert area(f, wx + 13, row4 + 3, wx + 60, row4 + 17, dark) > 25, "box, in the field"
cols = [x for x in range(wx + 13, wx + 120) if area(f, x, row4 + 3, x + 1, row4 + 17, dark)]
cursor = max(cols)
assert area(f, cursor, row4 + 4, cursor + 1, row4 + 16, dark) == 12, ("the cursor", cursor - wx)
assert area(f, cursor + 1, row4 + 3, wx + 170, row4 + 17, dark) == 0, "nothing right of the cursor"
# a new folder's field: its whole name selected (light blue behind the letters), no cursor
n = load("files-new")
sel = lambda p: abs(p[0] - 179) < 12 and abs(p[1] - 206) < 12 and p[2] > 240
width = [x for x in range(wx + 10, wx + 176) if sel(n(x, row4 + 3))]
assert len(width) > 60 and min(width) <= wx + 15, ("untitled folder, selected", len(width))
# the status line: a refusal in red; the Move mark (a blue pill, left); the question before a delete
status = top + 340 - 26
for name in ("files-refused", "files-confirm"):
    s = load(name)
    assert area(s, wx + 10, status + 4, wx + 200, status + 24, red) > 60, (name, "red news")
m = load("files-marked")
assert area(m, wx + 12, status + 5, wx + 50, status + 22, blue) > 250, "the Move mark"
assert area(m, wx + 10, status + 4, wx + 440, status + 24, red) == 0, "no red while all is well"
# b.txt, marked, in its row (selected): "move" where its size was, in white on the blue
assert area(m, wx + 130, top + 40 + 44 + 3, wx + 176, top + 40 + 44 + 17, lambda p: min(p) > 230) > 20, "move, in b.txt's row"
print("ok: the name field with its cursor and its selection, red refusals and the Move mark are on screen")
PY
echo "ok: Files makes, renames, copies, moves and deletes, refuses what it should, and Terminal sees each change"
