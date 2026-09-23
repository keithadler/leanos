#!/bin/bash
# Restart and switch off from the leanos menu: the display server asks the kernel (it alone
# holds the power capability), the machine resets through the watchdog and boots again from
# the same card, and then switches itself off.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
steps = [*click(40, 15), *click(60, 52), wait_for("leanos: idle", 2),
         *click(40, 15), *click(60, 80), wait_for("leanos: switching off")]
sys.exit(boot(90, steps=steps))
PY
)
status=$?
echo "$out" | grep -E "^(leanos © |leanos: (restarting|switching)|display: (restarting|switching))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the machine did not switch itself off cleanly (status $status)"
[ "$(echo "$out" | grep -c "^leanos © 2026 Keith Adler")" = 2 ] || fail "the machine did not boot twice"
echo "$out" | grep -qx "display: restarting, as the user asked" || fail "the menu did not ask to restart"
echo "$out" | grep -qx "leanos: restarting, as the display server asked" || fail "the kernel did not restart"
echo "$out" | grep -qx "leanos: switching off, as the display server asked" || fail "the kernel did not switch off"
[ "$(echo "$out" | grep -c "^fs: ready, 9 files on the SD card")" = 2 ] || fail "the second boot did not find the card"
echo "ok: the leanos menu restarts the machine and switches it off"
