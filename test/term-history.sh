#!/bin/bash
# Terminal's command line: history, Tab completion, and a cursor that moves. Commands typed
# are recalled with Up and Down (ESC [ A and B on the serial line, as the browser console
# sends them, and the USB keyboard's arrows): an empty line and a command repeated at once
# are not kept, the line being typed comes back after Down, and a recalled line runs and
# can be edited where the cursor is (Left, Right, Backspace). Home and End go to the line's
# start and end and Delete deletes the letter under the cursor (nothing at the end), as the
# serial line sends them (each way a terminal does) and from the USB keyboard; a sequence
# no key has (Insert, Ctrl+Right) types nothing. Tab completes a command's
# name and a file or folder name (a folder with a '/', in the current folder or one the
# word names), completes what several names share, lists them on a second Tab, and does
# nothing when no name matches.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

rm -f "$T"/term-*.png "$T/screen.png"
out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, snap, usb_key, DOCK
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
UP, DOWN, RIGHT, LEFT = b"\x1b[A", b"\x1b[B", b"\x1b[C", b"\x1b[D"
HOME, END, DELETE = b"\x1b[H", b"\x1b[F", b"\x1b[3~"
steps = [wait_for("usb: ready"),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         b"write a.txt one\r", wait_for("terminal: write a.txt"),
         b"cat welcome.txt\r", wait_for("terminal: cat welcome.txt"),
         b"ls\r", wait_for("terminal: ls"), b"ls\r", wait_for("terminal: ls", 2), b"   \r",
         # Up twice: past the repeated ls and the empty line (neither kept), to cat welcome.txt
         UP, UP, pause(0.5), snap("term-recalled"), b"\r", wait_for("terminal: cat welcome.txt", 2),
         # the line being typed is kept while Up and Down show others; Down past it does nothing
         b"write b.txt kept", pause(0.3), *usb_key("up"), pause(0.3), UP, DOWN, pause(0.3),
         *usb_key("down"), pause(0.3), DOWN, b"\r", wait_for("terminal: write b.txt"),
         # a recalled line edited where the cursor is: a letter in the middle, then two out
         UP, *[LEFT] * 7, RIGHT, pause(0.3), *usb_key("right"), pause(0.5), snap("term-cursor"), b"2\r",
         wait_for("terminal: write b.txt2"),
         UP, *[LEFT] * 5, b"\x7f\x7f\r", wait_for("terminal: write b.tx "),
         # Home, End and Delete (a moment between the serial line and the USB keyboard)
         b"rite c.txt ab", HOME, b"w", END, b"c", DELETE, b"\r", wait_for("terminal: write c.txt"),
         b"xwrite d.txt 12", pause(0.3), *usb_key("home"), *usb_key("delete"), *usb_key("end"), pause(0.3),
         b"3", *[LEFT] * 3, DELETE, b"\r", wait_for("terminal: write d.txt"),
         b"ite e.txt q", b"\x1bOH", b"wr", b"\x1b[2~\x1b[1;5C", b"\x1b[8~", b"!\r", wait_for("terminal: write e.txt"),
         b"ite f.txt z", b"\x1b[1~", b"r", b"\x1b[7~", b"w", b"\x1b[4~", b"yx", pause(0.3), *usb_key("left"),
         *usb_key("delete"), pause(0.3), b"\r", wait_for("terminal: write f.txt"),
         b"grep abc c.txt\r", wait_for("terminal: grep abc"), b"cat d.txt\r", wait_for("terminal: cat d.txt"),
         b"grep 23 d.txt\r", wait_for("terminal: grep 23"), b"cat e.txt\r", wait_for("terminal: cat e.txt"),
         b"grep q! e.txt\r", wait_for("terminal: grep q!"), b"cat f.txt\r", wait_for("terminal: cat f.txt"),
         b"grep zy f.txt\r", wait_for("terminal: grep zy"),
         # Tab: two commands start with ca, listed on the second Tab (from the USB keyboard)
         b"ca\t", pause(0.3), *usb_key("tab"), wait_for("terminal: completions for ca"),
         b"t\t", wait_for("terminal: completed cat"),
         b"we\t\t", wait_for("terminal: completions for we"),
         b"lc\t", wait_for("terminal: completed welc"), pause(0.5), snap("term-completed"),
         b"\r", wait_for("terminal: cat welcome.txt", 3),
         # a folder: completed with its '/', then a name inside one
         b"mkd\tdocs\r", wait_for("terminal: mkdir docs"),
         b"cd do\t\r", wait_for("terminal: cd docs"),
         b"write in.txt x\r", wait_for("terminal: write in.txt"),
         b"cd ..\r", wait_for("terminal: cd .."),
         b"cat docs/i\t\r", wait_for("terminal: cat docs/in.txt"),
         b"cat zz\t\r", wait_for("terminal: cat zz"),
         b"ve\ta.\t\r"]
sys.exit(boot(120, usb=True, steps=steps, until="terminal: verify", settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"            # where Terminal opened, for the pixel checks
echo "$out" | grep -E "^terminal: " | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"

has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }

# History: Up Up reached cat welcome.txt, which ran again and printed the same; the line
# being typed came back; a recalled line was edited in the middle.
cat1=$(echo "$out" | grep -m1 "^terminal: cat welcome.txt -> ") || fail "cat welcome.txt did not run"
count 3 "$cat1"
count 2 "terminal: ls -> $(echo "$out" | grep -m1 '^terminal: ls -> ' | sed 's/^terminal: ls -> //')"
count 1 "terminal: write a.txt -> ok"
has "terminal: write b.txt -> ok"
has "terminal: write b.txt2 -> ok"
has "terminal: write b.tx -> ok"
[ "$(echo "$out" | grep -c '^terminal: write ')" = 9 ] || fail "a command ran that was not asked for"

# Home, End and Delete: write c.txt abc (Delete at the end did nothing), write d.txt 23 (the
# x before it and the 1 after the cursor deleted), write e.txt q! (the unknown sequences
# typed nothing), write f.txt zy (the x under the cursor deleted)
for f in "c.txt" "d.txt" "e.txt" "f.txt"; do has "terminal: write $f -> ok"; done
has "terminal: grep abc -> 1 line"
has "terminal: cat d.txt -> 2 bytes"
has "terminal: grep 23 -> 1 line"
has "terminal: cat e.txt -> 2 bytes"
has "terminal: grep q! -> 1 line"
has "terminal: cat f.txt -> 2 bytes"
has "terminal: grep zy -> 1 line"

# Tab completion
has "terminal: completions for ca -> 2: caps cat"
has "terminal: completed cat -> cat"
we=$(echo "$out" | grep "^terminal: completions for we -> 3: ") || fail "missing: the names that start with we"
for n in web web.icon welcome.txt; do echo "$we" | grep -qw -- "$n" || fail "not listed: $n"; done
has "terminal: completed welc -> welcome.txt"
has "terminal: completed mkd -> mkdir"
has "terminal: mkdir docs -> ok"
has "terminal: completed do -> docs/"
has "terminal: cd docs/ -> ok"
has "terminal: write in.txt -> ok"
has "terminal: cd .. -> ok"
has "terminal: completed i -> in.txt"
has "terminal: cat docs/in.txt -> 1 bytes"
has "terminal: completed zz -> no match"
has "terminal: cat zz -> no such file"
has "terminal: completed ve -> verify"
has "terminal: completed a. -> a.txt"
has "terminal: verify a.txt -> 3 bytes, mixed"

python3 - "$T" <<'PYS' || fail "the screens are not what Terminal should draw"
import os, sys
sys.path.insert(0, "test")
from run import window_pos
tx, ty = window_pos(open(os.path.join(sys.argv[1], "serial.txt")).read(), "Terminal")
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
# the prompt line, at the bottom of Terminal's window: where its green cursor block is, and
# where light text is (the cursor's own letter is drawn dark on the block)
def prompt(name):
    at = load(name)
    xs, ys = range(tx + 34, tx + 454), range(ty + 266, ty + 286)
    green = [x for x in xs if sum(1 for y in ys if at(x, y) == (0x7f, 0xd1, 0xa0)) > 12]
    text = [x for x in xs if any(min(at(x, y)) > 150 for y in ys)]
    assert green and text, (name, "no prompt line", green[:3], text[:3])
    return green, text
green, text = prompt("term-recalled")         # cat welcome.txt, the cursor after it
assert min(green) > max(text), ("the cursor is not at the end of the recalled line", green[:3], text[-3:])
green, text = prompt("term-completed")        # cat welcome.txt and a space, the cursor after it
assert min(green) > max(text) + 6, ("the cursor is not after the completed name and its space", green[:3], text[-3:])
green, text = prompt("term-cursor")           # write b.txt| kept: text after the cursor
assert max(green) - min(green) < 10 and max(text) > max(green) + 20, ("the cursor is not inside the line", green, text[-3:])
print("ok: the recalled line, the completed line, and a cursor inside a line are on screen")
PYS
echo "ok: Up and Down recall commands, Left and Right edit them, Tab completes and lists names"
