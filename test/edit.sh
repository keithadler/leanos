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
set -u
cd "$(dirname "$0")/.."
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
