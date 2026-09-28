#!/bin/bash
# Force Quit: Apps' Running view (user/launcher.c) lists what runs in the open slots and
# stops what the user picks, after asking.
#
# The card holds hello, clock, and spin (user/progs/chaos.c run as `spin`: a loop that never
# makes a system call, and has no window, the kind of program that needs force quitting).
#
#   1. Terminal runs hello (slot 10) and clock (slot 11). Apps, from the dock, starts spin by
#      typing its name (slot 12). Ctrl+Q shows the Running view: three rows, hello and clock
#      named by the display from their windows and marked "started elsewhere" (Terminal
#      started them), spin with no window, started here. How long each has run grows.
#   2. A click on hello's row, Backspace: the view asks "Quit Hello? Return to confirm, or
#      click Quit again". Return: hello stops (the kernel's stop, as Terminal's `kill`), the
#      display takes its window back, and the list has two rows.
#   3. Down twice selects spin. Quit, then a stray key: nothing is stopped. Quit, and Quit
#      again: spin stops, whoever else hogs a core.
#   4. Ctrl+Q, from the USB keyboard, goes back to the grid. Terminal's `run hello` starts
#      hello in slot 10 again (the slot hello was quit in is free), and `ps` counts clock
#      running still. Then the pixels: the rows, their icons, the question in red, hello's
#      window gone, and clock's still ticking.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/fq-*.ppm "$T"/fq-*.png
make -s build/progs/hello.elf build/progs/clock.elf build/progs/chaos.elf build/icons/hello.icon build/icons/clock.icon \
  || fail "the programs did not build"
card=$T/sd-force-quit.img
python3 tools/mksd.py "$card" hello=build/progs/hello.elf clock=build/progs/clock.elf spin=build/progs/chaos.elf \
  hello.icon=build/icons/hello.icon clock.icon=build/icons/clock.icon >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, pause, snap, usb_key, DOCK, TITLE_H
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
# in Apps' window (user/launcher.c): the rows start at ROWS_Y, ROW_H apart; the Quit button
ROW = lambda i: (120, TITLE_H + 58 + 34 * i + 16)
QUIT = (480 - 20 - 42, TITLE_H + 276 + 13)
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run hello\r"), wait_for("hello: opened"), *wclick("Terminal", 230, 150),
         *keys("run clock\r"), wait_for("clock: opened"),
         *click(*DOCK["Apps"]), wait_for("apps: opened"),
         *keys("spin"), wait_for('apps: find "spin"'), b"\r", wait_for("apps: spin started"),
         b"\x11", wait_for("apps: showing what runs"), wait_for("apps: slot 12"), pause(2.5), snap("fq-list"),
         *wclick("Apps", *ROW(0)), wait_for("apps: selected hello"),
         b"\x7f", wait_for("apps: quit hello in slot 10?"), pause(0.4), snap("fq-confirm"),
         b"\r", wait_for("apps: quit hello in slot 10 ->"), wait_for("apps: running: 2"), pause(0.6), snap("fq-after"),
         b"\x1b[B", wait_for("apps: selected clock"), b"\x1b[B", wait_for("apps: selected spin"),
         *wclick("Apps", *QUIT), wait_for("apps: quit spin in slot 12?"),
         b"x", wait_for("apps: quit cancelled"),
         *wclick("Apps", *QUIT), wait_for("apps: quit spin in slot 12?", 2),
         *wclick("Apps", *QUIT), wait_for("apps: quit spin in slot 12 ->"),
         *usb_key("q", ctrl=True), wait_for("apps: showing the programs"),
         *click(*DOCK["Terminal"]), pause(0.3), *keys("run hello\r"), wait_for("hello: opened", 2),
         *wclick("Terminal", 230, 150), *keys("ps\r")]
sys.exit(boot(150, steps=steps, until="terminal: ps", sd=sys.argv[1], usb=True, settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(apps: |terminal: (run|ps)|hello: opened|clock: opened|chaos: |display: .*(gone|stopped))" \
  | grep -vE "^apps: (time zone|saved)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"

has() { echo "$out" | grep -qxE "$1" || fail "no line: $1"; }
# 1. the list: three programs, named, who started them, their windows
has "apps: spin started in slot 12"
has "apps: running: 3 programs"
has "apps: slot 10: hello, 1 window, started elsewhere, for [0-9]+ s"
has "apps: slot 11: clock, 1 window, started elsewhere, for [0-9]+ s"
has "apps: slot 12: spin, no window, for [0-9]+ s"
echo "$out" | grep -qx "chaos: spin in slot 12: spinning" || fail "spin did not spin"
# 2. hello, after asking, by Return; its window goes
has "apps: selected hello in slot 10"
has "apps: quit hello in slot 10\? Return to confirm, or click Quit again"
has "apps: quit hello in slot 10 -> stopped"
has "display: a program from the SD card stopped; its window is gone"
has "apps: running: 2 programs"
# 3. a stray key stops nothing; Quit twice stops spin
has "apps: quit cancelled"
[ "$(echo "$out" | grep -c "^apps: quit spin in slot 12? Return")" = 2 ] || fail "Quit did not ask twice for spin"
has "apps: quit spin in slot 12 -> stopped"
has "apps: running: 1 program"
echo "$out" | grep -A2 -x "apps: running: 1 program" | grep -qxE "apps: slot 11: clock, 1 window, started elsewhere, for [0-9]+ s" \
  || fail "clock is not the one left"
# nothing was stopped but what was confirmed
[ "$(echo "$out" | grep -c -- "^apps: quit .* -> stopped$")" = 2 ] || fail "more than two programs were stopped"
# 4. the slot is free again, clock still runs
[ "$(echo "$out" | grep -c "^terminal: run hello -> slot 10$")" = 2 ] || fail "hello's slot was not free again"
echo "$out" | grep -qx "terminal: run clock -> slot 11" || fail "clock did not start in slot 11"
# the times grew: each program's "for N s" in the last list is at least its first
python3 - "$T/serial.txt" <<'PY' || fail "the times did not grow"
import re, sys
first, last = {}, {}
for line in open(sys.argv[1]):
    m = re.match(r"apps: slot (\d+): (\w+), .*, for (\d+) s$", line.strip())
    if m:
        first.setdefault(m.group(2), int(m.group(3)))
        last[m.group(2)] = int(m.group(3))
assert last["clock"] > first["clock"], (first, last)
print("ok: clock had run", first["clock"], "s, then", last["clock"], "s")
PY
has "terminal: ps -> 8 running"

python3 - "$T" <<'PY' || fail "the screen is not what the Running view drew"
import os, re, sys
sys.path.insert(0, "test")
from run import OPENED, TITLE_H
T = sys.argv[1]
def load(name):
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
listed, asked, after = load("fq-list"), load("fq-confirm"), load("fq-after")
# the windows as they were when hello was quit: where each opened (none was moved)
lines = open(os.path.join(T, "serial.txt")).read().splitlines()
lines = lines[:next(i for i, l in enumerate(lines) if l.startswith("apps: quit hello in slot 10 ->"))]
wins = {}
for l in lines:
    m = OPENED.match(l)
    if m:
        wins[m.group(1)] = (int(m.group(4)), int(m.group(5)), int(m.group(2)), int(m.group(3)) + TITLE_H)
ax, ay = wins["Apps"][0], wins["Apps"][1] + TITLE_H
row = lambda i: ay + 58 + 34 * i
# three rows: hello's and clock's icons (many colors), spin's tile (its initial on green)
colors = lambda at, i: len({at(ax + 28 + x, row(i) + 3 + y) for y in range(28) for x in range(28)})
assert colors(listed, 0) > 40 and colors(listed, 1) > 40, ("the icons", colors(listed, 0), colors(listed, 1))
assert listed(ax + 32, row(2) + 16) == (46, 170, 110), ("spin's tile", listed(ax + 32, row(2) + 16))
assert set(listed(ax + 28 + x, row(3) + 16) for x in range(28)) == {(247, 247, 250)}, "a fourth row"
# asked: hello's row ringed in red, the Quit button red; before, the button gray
red = (214, 64, 64)
assert asked(ax + 20, row(0) + 16) == red, ("hello's row", asked(ax + 20, row(0) + 16))
assert asked(ax + 480 - 20 - 42, ay + 276 + 4) == red and listed(ax + 480 - 20 - 42, ay + 276 + 4) != red, "the Quit button"
# hello's window, where no other window covers it: its light pixels before, the desktop after
hx, hy, hw, hh = wins["hello"]
covered = lambda x, y: any(n != "hello" and wx <= x < wx + ww and wy <= y < wy + wh for n, (wx, wy, ww, wh) in wins.items())
bare = [(x, y) for y in range(hy + TITLE_H, hy + hh) for x in range(hx, hx + hw) if not covered(x, y)]
assert len(bare) > 200, ("too little of hello's window shows", len(bare))
light = lambda at: sum(1 for x, y in bare if min(at(x, y)) > 200)
assert light(asked) > len(bare) // 2 and light(after) < len(bare) // 20, ("hello's window", light(asked), light(after), len(bare))
# clock still ticks: its digits changed between the two captures
cx, cy, cw, ch = wins["clock"]
digits = lambda at: [at(x, y) for y in range(cy + TITLE_H + 40, cy + TITLE_H + 80) for x in range(cx + 40, cx + cw - 40)]
assert digits(asked) != digits(after), "clock stopped drawing"
print(f"ok: three rows with their icons, the question in red, hello's window gone ({len(bare)} pixels), clock ticking")
PY
echo "ok: the Running view lists hello, clock and spin, and quits hello and spin, each only after asking"
