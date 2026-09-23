#!/bin/bash
# The programs on the card, used the way a person would: from Terminal, one after another,
# each in its own open slot. The tour must see every attack refused.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

out=$(python3 - <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
UP, DOWN, RIGHT, LEFT = b"\x1b[A", b"\x1b[B", b"\x1b[C", b"\x1b[D"
term = click(150, 400)                  # Terminal's window, where no program window covers it
steps = [*click(478, 548), wait_for("terminal: opened"),
         *keys("tour\r"), wait_for("tour: opened"),
         *[b"\r" for _ in range(10)], wait_for("tour: The difference"),
         *term, *keys("run calc\r"), wait_for("calc: opened"),
         *keys("2+3*4\r"), *keys("(7-2)*3\r"), *keys("1/0\r"), wait_for("calc: 1/0"),
         *term, *keys("run snake\r"), wait_for("snake: opened"), UP, wait_for("snake: game over"),
         *term, *keys("run life\r"), wait_for("life: 30 generations"),
         *term, *keys("run tiles\r"), wait_for("tiles: opened"),
         *[LEFT, UP, RIGHT, DOWN] * 3, wait_for("tiles: 3 moves"),
         *click(682, 548), wait_for("apps: opened"), *click(528, 370), wait_for("apps: clock"),
         wait_for("clock: opened"),
         *term, *keys("run calc\r"), wait_for("terminal: run calc"),
         *term, *keys("ps\r"), wait_for("terminal: ps")]
sys.exit(boot(150, steps=steps, until="terminal: ps", settle=2))
PY
)
status=$?
echo "$out" | grep -E "^(tour|calc|snake|life|tiles|apps|clock|terminal: (run|ps|tour)|display: .* already open)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
for page in "Your files" "Other programs' memory" "The disk" "Your keystrokes" "No all-powerful account"; do
  echo "$out" | grep -E "^tour: $page: " | grep -q " -> refused" || fail "the tour's attack was not refused: $page"
done
echo "$out" | grep -qx "tour: Writing, then running code: Ask for memory both writable and executable -> refused, got rw-: never both" || fail "write+execute"
echo "$out" | grep -qE "^tour: Tampered programs: Check every program the manifest names -> [0-9]+ match, 0 refused$" || fail "tamper check"
[ "$(echo "$out" | grep -c "^tour: ")" -ge 11 ] || fail "the tour did not show every page"
for line in "calc: 2+3*4 = 14" "calc: (7-2)*3 = 15" "calc: 1/0 cannot divide by 0"; do
  echo "$out" | grep -qxF "$line" || fail "missing: $line"
done
echo "$out" | grep -qE "^snake: game over, score [0-9]+$" || fail "snake did not end at the wall"
echo "$out" | grep -qx "life: 30 generations" || fail "life did not run"
echo "$out" | grep -qE "^tiles: 3 moves, score [0-9]+$" || fail "tiles did not move"
echo "$out" | grep -qx "apps: clock started in slot 15" || fail "Apps did not start clock"
echo "$out" | grep -qx "terminal: run calc -> already open" || fail "a second run of calc started another copy"
echo "$out" | grep -qx "display: calc is already open; brought it to the front" || fail "the display did not bring calc forward"
echo "$out" | grep -qx "terminal: ps -> 12 running" || fail "ps did not count the running programs"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "ok: the tour sees every attack refused; calc, snake, life and tiles run from Terminal, clock from Apps, six at once, one copy of each"
