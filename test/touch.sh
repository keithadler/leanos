#!/bin/bash
# A touchscreen: an absolute pointer on USB (QEMU's tablet stands in for one). The USB
# driver reads its report descriptor, finds where X, Y and the touch are in its reports,
# and a tap on Terminal in the dock opens it.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, wait_for, usb_touch, DOCK
x, y = DOCK["Terminal"]
steps = [wait_for("usb: ready"), usb_touch(x, y), usb_touch(x, y, True), usb_touch(x, y, False),
         wait_for("terminal: opened")]
sys.exit(boot(90, touch=True, steps=steps, until="terminal: opened", settle=1))
PY
)
status=$?
echo "$out" | grep -E "^(usb|display: start Terminal|terminal: opened|run.py)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -q "^usb: device [0-9]*: touchscreen or tablet$" || fail "the tablet was not found"
echo "$out" | grep -qx "display: start Terminal -> ok" || fail "a tap on Terminal in the dock did not open it"
echo "ok: a USB touchscreen (an absolute pointer) taps Terminal open in the dock"
