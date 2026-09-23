#!/bin/bash
# A USB keyboard and mouse on the DWC2, behind QEMU's hub. The USB driver finds them, the
# kernel refuses the requests that could aim the controller's DMA anywhere but the driver's
# own memory (tried for real at start), typing on the keyboard lands in Notes, and the
# mouse moves the pointer and clicks Terminal open in the dock.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, wait_for, usb_key, usb_mouse, DOCK
x, y = DOCK["Terminal"]
steps = [wait_for("usb: ready"), *usb_key("h", shift=True), *usb_key("i"), *usb_key("1", shift=True),
         wait_for("display: key '!'"),
         usb_mouse(x - 512, 0), usb_mouse(0, y - 300), wait_for("usb: ready"),
         usb_mouse(button=True), usb_mouse(button=False), wait_for("terminal: opened")]
sys.exit(boot(90, usb=True, steps=steps, until="terminal: opened", settle=1))
PY
)
status=$?
echo "$out" | grep -E "^(usb|display: (key|start Terminal)|terminal: opened|run.py)" | sed 's/^/  | /'
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
echo "ok: a USB keyboard and mouse work through a hub, and the controller's DMA stays in the driver's memory"
