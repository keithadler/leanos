#!/bin/bash
# A USB keyboard and mouse on the DWC2, behind QEMU's hub. The USB driver finds them, the
# kernel refuses the requests that could aim the controller's DMA anywhere but the driver's
# own memory (tried for real at start), typing on the keyboard lands in Notes, and the
# mouse moves the pointer and clicks Terminal open in the dock. Then, in mines (a window
# that hears the right button), a right click flags a cell and another takes the flag back,
# and a left click still opens one.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, wait_for, usb_key, usb_mouse, usb_wmove, DOCK, TITLE_H
x, y = DOCK["Terminal"]
# mines' Beginner board: 28-pixel cells from (123, 42) in its window (test/mines.sh)
cell = lambda cx, cy: usb_wmove("mines", 123 + 28 * cx + 14, TITLE_H + 42 + 28 * cy + 14)
right = [usb_mouse(button=True, which="right"), usb_mouse(button=False, which="right")]
steps = [wait_for("usb: ready"), *usb_key("h", shift=True), *usb_key("i"), *usb_key("1", shift=True),
         wait_for("display: key '!'"),
         usb_mouse(x - 512, 0), usb_mouse(0, y - 300), wait_for("usb: ready"),
         usb_mouse(button=True), usb_mouse(button=False), wait_for("terminal: opened"),
         b"run mines\r", wait_for("mines: opened a window"),
         cell(0, 0), *right, wait_for("mines: flagged 0,0"), *right, wait_for("mines: unflagged 0,0"),
         cell(8, 8), usb_mouse(button=True), usb_mouse(button=False), wait_for("mines: opened", 2),
         *usb_key("3")]         # Expert: a line to wait for that nothing before could print
sys.exit(boot(120, usb=True, steps=steps, until="mines: new game, expert", settle=1))
PY
)
status=$?
echo "$out" | grep -E "^(usb|display: (key|start Terminal)|terminal: opened|mines|run.py)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "usb: refused, as proved: DMA into the display's memory, descriptor DMA, device mode" \
  || fail "a dangerous USB request was not refused"
echo "$out" | grep -qx "usb: device 1: hub, 8 ports" || fail "the hub was not found"
echo "$out" | grep -qx "usb: ready, 1 keyboard, 1 mouse" || fail "the keyboard and mouse were not found"
for k in H i '!'; do
  echo "$out" | grep -qxF "display: key '$k' to alice" || fail "the USB keyboard's $k did not reach Notes"
done
echo "$out" | grep -qx "display: start Terminal -> ok" || fail "the USB mouse did not click Terminal in the dock"
echo "$out" | grep -qx "mines: flagged 0,0 (9 left)" || fail "a right click with the USB mouse did not flag a cell in mines"
echo "$out" | grep -qx "mines: unflagged 0,0 (10 left)" || fail "a second right click did not take the flag back"
echo "$out" | grep -qx "mines: opened [0-9]* cells at 8,8" || fail "a left click in mines did not open a cell"
[ "$(echo "$out" | grep -c "^mines: \(flagged\|unflagged\)")" = 2 ] || fail "the left click flagged, or a right click did twice"
echo "ok: a USB keyboard and mouse work through a hub, the right button reaches a window that hears it, and the controller's DMA stays in the driver's memory"
