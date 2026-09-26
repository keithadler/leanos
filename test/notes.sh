#!/bin/bash
# Notes (user/alice.c): several notes, each a file in her folder, and an editor with a cursor.
#
#   1. Notes closed; Terminal writes notes.txt, the one note of a card from before, and, in
#      notes/, a file of the user's named 2.txt.tmp. Notes, started from the dock, moves
#      notes.txt to notes/1.txt and shows it; a line typed at its end is saved.
#   2. Ctrl+N makes note 2: two lines, then the arrows move the cursor (Left into the first
#      line, Down to the end of the second, Up twice to the very start, Down twice to the
#      very end) and each key goes in where it is. Note 2 is saved through notes/2.txt.tmp2:
#      the user's notes/2.txt.tmp is left alone.
#   3. edit copies the first 4 KiB of guide.txt; a new note 3 gets it pasted (scrolled to
#      keep the cursor at its end); Up 40 times and Down 6 put the cursor mid-note, halfway
#      down the window, and four more pastes go in there: 20 KiB, saved in two pieces and
#      one rename.
#   4. Note 4: Ctrl+D asks, a key keeps it, Ctrl+D twice deletes it. A new empty note is
#      dropped when Tab and Up go back through the list, to note 3, the long one. Return goes
#      back into it, at its start, and the keys above the arrows move and edit it, from the
#      serial line and from the USB keyboard: Page Down to its very end (ENDMARK typed
#      there), 30 short lines, Page Up a window of lines (14) and again (a mark on each line
#      it lands on, after Home), Page Down back, Home and Delete (the mark goes), End and a
#      letter, Delete at the line's end (the next line joins it); then a long line that
#      wraps, Home to the start of its last line as shown (not of the line), Up, End to the
#      end of that shown line and Delete (the space between them goes); Page Up to the very
#      start (TOPMARK). Tab and Up go on to note 2, and a key typed there lands at its end.
#      A click in the list chooses note 1.
#   5. Terminal fills notes/9.txt with 40 KiB, more than a note holds. Notes closed and
#      started again from the dock: the three notes are back, as saved, and note 9 is shown
#      (its first 32 KiB) but read-only: keys typed there change nothing. Terminal's cat,
#      grep, wc and ls read the files; then the machine starts again with the card, and they
#      are still there. Notes' secret is written and checked each time.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/two-notes.* "$T"/long-note.* "$T"/notes-back.*

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, fresh_card, mouse, wait_for, pause, snap, wclick, usb_key, CLOSE, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
line = lambda s: [s.encode() + b"\r"]              # a whole Terminal command at once
UP, DOWN, RIGHT, LEFT = b"\x1b[A", b"\x1b[B", b"\x1b[C", b"\x1b[D"
HOME, END, DELETE, PGUP, PGDN = b"\x1b[H", b"\x1b[F", b"\x1b[3~", b"\x1b[5~", b"\x1b[6~"
# many keys, a moment between each 20, so a busy Notes never falls a whole queue behind
many = lambda k, n: [x for i in range(n) for x in ([k] + ([pause(0.5)] if i % 20 == 19 else []))]
CTRL_N, CTRL_D, CTRL_C, CTRL_V, TAB = b"\x0e", b"\x04", b"\x03", b"\x16", b"\t"
row = lambda i: wclick("alice", 60, 30 + 48 + 28 * i + 14)     # a note in the list
TERM, NOTES = click(*DOCK["Terminal"]), click(*DOCK["Notes"])  # to the front
card = fresh_card()
steps = [wait_for("alice: opened"),
         # 1. the note of a card from before, and a file of the user's in notes/
         *wclick("alice", *CLOSE), wait_for("alice: window closed"),
         *TERM, wait_for("terminal: opened"),
         *line("write notes.txt legacy note"), wait_for("terminal: write notes.txt"),
         *line("mkdir notes"), wait_for("terminal: mkdir notes"),
         *line("write notes/2.txt.tmp keep me"), wait_for("terminal: write notes/2.txt.tmp"),
         *NOTES, wait_for("alice: opened", 2),
         *keys("\rline two"), wait_for("alice: saved note 1"),
         # 2. note 2, and the cursor
         CTRL_N, wait_for("alice: new note 2"), *keys("abcdef\rxyz"),
         *[LEFT] * 7, *keys("MID"), DOWN, *keys("+"), UP, UP, *keys("S"), DOWN, DOWN, *keys("E"),
         wait_for("alice: saved note 2"), pause(0.3), snap("two-notes"),
         # 3. a long note: 4 KiB from edit, then 16 KiB more in the middle of it
         *TERM, *line("run edit guide.txt"), wait_for("edit: opened a window"),
         CTRL_C, wait_for("edit: copied"), *wclick("edit", *CLOSE), wait_for("edit: window closed"),
         *NOTES, CTRL_N, wait_for("alice: new note 3"), CTRL_V, wait_for("alice: pasted"),
         wait_for("alice: saved note 3"), *[UP] * 40, *[DOWN] * 6, pause(0.5), snap("long-note"),
         *[x for k in range(2, 6) for x in (CTRL_V, wait_for("alice: pasted", k))],
         wait_for("alice: saved note 3 (20480"),
         # 4. deleting, asked first; an empty note dropped; the list by keys and by a click
         CTRL_N, wait_for("alice: new note 4"), *keys("delete me"), wait_for("alice: saved note 4"),
         CTRL_D, wait_for("alice: asked before deleting note 4"), *keys("x"), wait_for("alice: kept note 4"),
         CTRL_D, wait_for("alice: asked before deleting note 4", 2), CTRL_D, wait_for("alice: deleted note 4"),
         CTRL_N, wait_for("alice: new note 4", 2), TAB, UP, wait_for("alice: showing note 3"),
         # the keys above the arrows, in note 3 (the cursor at its start)
         b"\r", *many(PGDN, 80), pause(0.5), *keys("ENDMARK\r"),
         *[x for i in range(1, 31) for x in keys(f"Pq{i:02d}\r")], pause(0.5),
         # (a moment between the serial line and the USB keyboard: they reach the display apart)
         PGUP, *keys("@"), pause(0.3), *usb_key("pgup"), *usb_key("home"), pause(0.3), *keys("="), pause(0.3),
         *usb_key("pgdn"), pause(0.3), b"\x1b[1~", DELETE, pause(0.3), *usb_key("end"), pause(0.3), *keys("!"),
         pause(0.3), *usb_key("delete"), pause(0.3),
         *many(PGDN, 3), *keys(" ".join(f"wq{i:02d}" for i in range(1, 41))), pause(0.5),
         b"\x1b[7~", *keys("#"), UP, b"\x1b[8~", DELETE, *many(PGUP, 80), pause(0.5), *keys("TOPMARK"),
         wait_for("alice: saved note 3 (20845"),
         TAB, UP, wait_for("alice: showing note 2"), b"\r", *keys("!"), wait_for("alice: saved note 2 (17"),
         *row(0), wait_for("alice: showing note 1"),
         # 5. a note too long; Notes again: what came back, and the files
         *TERM, *line("fill notes/9.txt 40 y"), wait_for("terminal: fill notes/9.txt"),
         *NOTES, *wclick("alice", *CLOSE), wait_for("alice: window closed", 2),
         *NOTES, wait_for("alice: opened", 3), *row(3), wait_for("alice: showing note 9"), *keys("abc"),
         pause(1), *row(1), wait_for("alice: showing note 2", 2), pause(0.3), snap("notes-back"),
         *TERM, *line("cat notes/1.txt"), wait_for("terminal: cat notes/1.txt"),
         *line("cat notes/2.txt"), wait_for("terminal: cat notes/2.txt"),
         *line("cat notes/3.txt"), wait_for("terminal: cat notes/3.txt"),
         *line("cat notes/9.txt"), wait_for("terminal: cat notes/9.txt"),
         *line("cat notes/2.txt.tmp"), wait_for("terminal: cat notes/2.txt.tmp"),
         *line("cat notes.txt"), wait_for("terminal: cat notes.txt"),
         *line("grep SabcMIDdef notes/2.txt"), wait_for("terminal: grep SabcMIDdef"),
         *line("grep xyz+E! notes/2.txt"), wait_for("terminal: grep xyz+E!"),
         *line("grep legacy notes/1.txt"), wait_for("terminal: grep legacy"),
         *line("head -n 1 notes/3.txt | grep TOPMARK"), wait_for("terminal: grep TOPMARK"),
         *line("tail -n 31 notes/3.txt | grep ENDMARK"), wait_for("terminal: grep ENDMARK"),
         *line("tail -n 30 notes/3.txt | grep ENDMARK"), wait_for("terminal: grep ENDMARK", 2),
         *line("grep =Pq03 notes/3.txt"), wait_for("terminal: grep =Pq03"),
         *line("grep @Pq notes/3.txt"), wait_for("terminal: grep @Pq"),
         *line("grep Pq17!Pq18 notes/3.txt"), wait_for("terminal: grep Pq17!Pq18"),
         *line("grep Pq notes/3.txt"), wait_for("terminal: grep Pq "),
         *line("grep #wq01 notes/3.txt"), wait_for("terminal: grep #wq01"),
         *line("grep #wq notes/3.txt | wc"), wait_for("terminal: wc"),
         *line("wc notes/2.txt"), wait_for("terminal: wc notes/2.txt"),
         *line("ls notes"), wait_for("terminal: ls notes")]
first = boot(210, steps=steps, until="terminal: ls notes", sd=card, settle=0.3, usb=True)
print("---- boot 2", flush=True)
sys.exit(first or boot(40, sd=card))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(alice|edit: copied|terminal: (write|mkdir|fill|cat|grep|wc|ls|head|tail)|---- boot)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -q "^leanos: alice stopped" && fail "Notes stopped"

has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }

# Her secret, written each time she starts (at boot, twice from the dock, at the second
# boot), and never changed.
count 4 "alice: wrote secret 0x5ec12e7 to my data page"
count 4 "alice: opened a 480x320 window, read-only, 150 pages -> ok"
echo "$out" | grep -q "SECRET CHANGED" && fail "alice's secret changed"

# Everything she said, in order (the file-server lines are hers too).
got=$(echo "$out" | sed '/^---- boot 2/q' | grep -E "^alice: " | grep -vE "^alice: (wrote secret|opened a)")
want="alice: no saved note yet
alice: window closed, exiting
alice: moved notes.txt to notes/1.txt
alice: 1 note; loaded notes/1.txt, 11 bytes
alice: saved note 1 (20 bytes)
alice: new note 2
alice: notes/2.txt.tmp is there already: left alone
alice: saved note 2 (16 bytes)
alice: new note 3
alice: pasted 4096 bytes
alice: saved note 3 (4096 bytes)
alice: pasted 4096 bytes
alice: pasted 4096 bytes
alice: pasted 4096 bytes
alice: pasted 4096 bytes
alice: saved note 3 (20480 bytes)
alice: new note 4
alice: saved note 4 (9 bytes)
alice: asked before deleting note 4
alice: kept note 4
alice: asked before deleting note 4
alice: deleted note 4
alice: new note 4
alice: removed note 4, which was empty
alice: showing note 3 (20480 bytes)
alice: saved note 3 (20845 bytes)
alice: showing note 2 (16 bytes)
alice: notes/2.txt.tmp is there already: left alone
alice: saved note 2 (17 bytes)
alice: showing note 1 (20 bytes)
alice: window closed, exiting
alice: 4 notes; loaded notes/1.txt, 20 bytes
alice: showing note 9 (32768 bytes, read-only)
alice: showing note 2 (17 bytes)"
# A save comes a moment after the typing stops: on a slow host it may come more than once
# while keys are still arriving. Those extra saves (of sizes not wanted here), and the line
# before each about the user's .tmp, are left out; the ones wanted must all be there.
got=$(echo "$got" | python3 -c '
import re, sys
want, got = sys.argv[1].splitlines(), sys.stdin.read().splitlines()
keep = []
for line in got:
    if re.fullmatch(r"alice: saved note \d+ \(\d+ bytes\)", line) and line not in want:
        if keep and re.fullmatch(r"alice: notes/\d+\.txt\.tmp is there already: left alone", keep[-1]):
            keep.pop()
        continue
    keep.append(line)
print("\n".join(keep))' "$want")
[ "$got" = "$want" ] || { echo "got:"; echo "$got" | sed 's/^/  | /'; fail "Notes did not do what was asked, in order"; }

# The files, as Terminal reads them.
has "edit: copied 4096 bytes -> ok"
has "terminal: cat notes/1.txt -> 20 bytes"
has "terminal: cat notes/2.txt -> 17 bytes"
has "terminal: cat notes/3.txt -> 20845 bytes"
has "terminal: cat notes/9.txt -> 40960 bytes"
has "terminal: cat notes/2.txt.tmp -> 7 bytes"
has "terminal: cat notes.txt -> no such file"
has "terminal: grep SabcMIDdef -> 1 line"
has "terminal: grep xyz+E! -> 1 line"
has "terminal: grep legacy -> 1 line"
has "terminal: ls notes -> 5 files"
has "terminal: wc notes/2.txt -> 1 line, 2 words, 17 bytes"

# The keys above the arrows, in note 3: Page Down reached its very end (ENDMARK is on the
# line before the 31 after it: 30 short ones, two of them joined, and the long one); Page
# Up went 14 lines up (from the empty line after Pq30 to Pq17, and on to Pq03), and Page
# Down 14 back; Home and Delete took the @ away again; End and Delete joined Pq17! and
# Pq18; Home in the long line went to its last line as shown, not its start, and End on the
# line shown before it went to just before the space that Delete took (39 words left of
# 40); Page Up reached the very start (TOPMARK on the first line).
has "terminal: head notes/3.txt -> 1 line"
has "terminal: grep TOPMARK -> 1 line"
has "terminal: grep ENDMARK -> 1 line"
has "terminal: grep ENDMARK -> 0 lines"
echo "$out" | grep -qE "^terminal: tail notes/3.txt -> 31 lines of [0-9]+$" || fail "tail did not show 31 lines of note 3"
has "terminal: grep =Pq03 -> 1 line"
has "terminal: grep @Pq -> 0 lines"
has "terminal: grep Pq17!Pq18 -> 1 line"
has "terminal: grep Pq -> 29 lines"
has "terminal: grep #wq01 -> 0 lines"
has "terminal: grep #wq -> 1 line"
echo "$out" | grep -qE "^terminal: wc -> [01] lines?, 39 words, " || fail "End and Delete in the long line: not 39 words"

# The second boot: the notes are there.
boot2=$(echo "$out" | sed -n '/^---- boot 2/,$p')
echo "$boot2" | grep -qx "alice: 4 notes; loaded notes/1.txt, 20 bytes" || fail "the notes did not survive a restart"
echo "ok: notes made, edited at the cursor, pasted into, scrolled, deleted when asked twice, one too long left as it was, and back after Notes and the machine start again"

# The screens: two notes in the list; a long note scrolled with the cursor in its middle.
python3 - "$T" <<'PYS' || fail "the screens are not what Notes drew"
import os, sys
sys.path.insert(0, "test")
from run import window_pos
log = open(os.path.join(sys.argv[1], "serial.txt")).read()
runs = log.split("---- boot 2")[0].split("alice: window closed")
nx, ny = window_pos(runs[1], "alice")           # where Notes' second run opened
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
TOP = ny + 30                                   # the window's content, below its title bar
dark = lambda p: max(p) < 100
blue = lambda p: p[2] > 200 and p[0] < 90       # the cursor
thumb = lambda p: abs(p[0] - 196) <= 3 and abs(p[2] - 206) <= 3
def count(at, pred, x0, y0, x1, y1):
    return sum(1 for y in range(y0, y1) for x in range(x0, x1) if pred(at(x, y)))
# two notes in the list, each a row of dark text, the second chosen (a light blue row); its
# two lines in the note, the cursor at its end
at = load("two-notes")
rows = [count(at, dark, nx + 14, TOP + 48 + 28 * i, nx + 140, TOP + 76 + 28 * i) for i in range(3)]
assert rows[0] > 40 and rows[1] > 40 and rows[2] == 0, ("the list", rows)
assert at(nx + 10, TOP + 48 + 28 + 14) == (221, 228, 246), ("the chosen row", at(nx + 10, TOP + 48 + 28 + 14))
lines = [count(at, dark, nx + 160, TOP + 10 + 20 * i, nx + 460, TOP + 30 + 20 * i) for i in range(3)]
assert lines[0] > 40 and lines[1] > 20 and lines[2] == 0, ("note 2's lines", lines)
assert count(at, blue, nx + 160, TOP + 30, nx + 460, TOP + 50) > 20, "the cursor at the end of the second line"
# the long note: text on every row, the cursor mid-window, and the scroll bar's thumb well
# away from both ends of its track (rows 10 to 290)
at = load("long-note")
full = [count(at, dark, nx + 160, TOP + 10 + 20 * i, nx + 460, TOP + 30 + 20 * i) for i in range(14)]
assert sum(1 for f in full if f > 30) >= 10, ("the long note's rows", full)
ys = [y for y in range(TOP, TOP + 294) if blue(at(nx + 164 + 1, y)) or any(blue(at(x, y)) for x in range(nx + 160, nx + 460, 1))]
assert ys and TOP + 20 < min(ys) and max(ys) < TOP + 280, ("the cursor", ys[:1], ys[-1:])
ts = [y for y in range(TOP, TOP + 294) if thumb(at(nx + 473, y))]
assert ts and min(ts) > TOP + 40 and max(ts) < TOP + 260, ("the scroll bar", ts[:1], ts[-1:])
# Notes started again: four notes in the list, the second chosen
nx, ny = window_pos(runs[2], "alice")           # its third run
TOP = ny + 30
at = load("notes-back")
rows = [count(at, dark, nx + 14, TOP + 48 + 28 * i, nx + 140, TOP + 76 + 28 * i) for i in range(5)]
assert all(r > 40 for r in rows[:4]) and rows[4] == 0, ("the list after a restart", rows)
assert at(nx + 10, TOP + 48 + 28 + 14) == (221, 228, 246), ("the chosen row", at(nx + 10, TOP + 48 + 28 + 14))
print("ok: the list of two notes, the long note scrolled with its cursor in the middle, and the four notes back on screen")
PYS
