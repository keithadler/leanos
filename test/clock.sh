#!/bin/bash
# Clock's stopwatch and timer. Clock starts from the dock on the Clock tab. A click on the
# Stopwatch tab shows it; space starts it, L takes a lap a second in, and a click on its Stop
# button stops it a second later. T shows the Timer; 3 sets it to 3 seconds, and a click on
# its Start button starts it. At zero it flashes on its tab until a key stops it.
#
# The times, by the CPU's counter (what Clock measures with) against the host's: the
# stopwatch ran at least the 2 s the test waited between starting it and stopping it, and
# about as long as the host saw between its log lines; the timer ended no sooner than 3 s
# after it started and within 400 ms after, and the host saw about 3 s go by. The kernel's
# clock, logged beside, never ran ahead of the counter (its ticks come at least 10 ms apart)
# and kept at least a third of its pace (a tick that comes late puts it behind for good:
# under QEMU, about a quarter).
#
# The pixels: each tab, when shown, is the one lit in the pill at the top (and the others are
# not); the stopwatch, stopped, offers Start; the timer, done, flashes red behind the numbers
# in at least one of four captures 0.3 s apart, and after a key it is back on the dark
# background, still on the Timer tab.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/clock-*.ppm "$T"/clock-*.png

out=$(python3 - <<'PY'
import sys, time
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK, snap, pause, wclick, TITLE_H
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
def on_line(line):
    print(f"{time.monotonic():.3f} {line}", flush=True)
# user/progs/clock.c: the tabs, 78 px each from x 33, y 6 to 28; the buttons from y 116 to 142,
# three (84 px, 6 apart) on the Stopwatch tab, four (63 px) on the Timer tab, from x 15
tab = lambda i: wclick("clock", 33 + 78 * i + 39, TITLE_H + 17)
button = lambda n, i: wclick("clock", 15 + i * ((270 - 6 * (n - 1)) // n + 6) + 20, TITLE_H + 129)
steps = [*click(*DOCK["Clock"]), wait_for("clock: ticked 3 times"), snap("clock-clock"),
         *tab(1), wait_for("clock: showing the stopwatch"),
         b" ", wait_for("clock: stopwatch started"), pause(1.0),
         b"l", wait_for("clock: stopwatch lap 1"), pause(1.0),
         *button(3, 2), wait_for("clock: stopwatch stopped"), pause(0.3), snap("clock-stopwatch"),
         b"t", wait_for("clock: showing the timer"), b"3", wait_for("clock: timer set to 00:03"),
         pause(0.3), snap("clock-timer"),
         *button(4, 3), wait_for("clock: timer started"), wait_for("clock: timer done"),
         snap("clock-done-1"), pause(0.3), snap("clock-done-2"), pause(0.3), snap("clock-done-3"),
         pause(0.3), snap("clock-done-4"),
         b"x", wait_for("clock: timer reset to 00:03"), pause(0.3), snap("clock-after")]
sys.exit(boot(90, on_line=on_line, steps=steps, until="clock: timer reset", settle=0.5))
PY
)
status=$?
echo "$out" > "$T/stamped.txt"                   # each line with the host's time it came
echo "$out" | cut -d' ' -f2- > "$T/serial.txt"
echo "$out" | grep -E "^[0-9.]+ (clock: |display: clock )" | cut -d' ' -f2- | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"

python3 - "$T" <<'PY' || fail "the stopwatch or the timer kept the wrong time, or showed the wrong thing"
import os, re, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
T = sys.argv[1]
stamped = [l.split(" ", 1) for l in open(os.path.join(T, "stamped.txt")).read().splitlines() if " " in l]
def line(prefix):
    """The host's time the first line starting with prefix came, and the line."""
    got = next(((float(t), l) for t, l in stamped if l.startswith(prefix)), None)
    assert got, "missing: " + prefix
    return got

# the stopwatch: at least the 2 s the test waited, about what the host saw, both clocks agree
h0, _ = line("clock: stopwatch started")
h1, stopped = line("clock: stopwatch stopped at ")
m = re.fullmatch(r"clock: stopwatch stopped at 00:(\d\d)\.(\d\d) \((\d+) ms by the counter, (\d+) by the kernel's clock\)", stopped)
assert m, stopped
ms, kms = int(m.group(3)), int(m.group(4))
assert int(m.group(1)) * 1000 + int(m.group(2)) * 10 == ms // 10 * 10, ("shown is not what it measured", stopped)
assert 2000 <= ms <= 2000 + 2500, ("the stopwatch ran for", ms)
host = (h1 - h0) * 1000
assert abs(ms - host) <= 800, ("the stopwatch measured", ms, "and the host saw", host)
assert ms // 3 <= kms <= ms + 20, ("the kernel's clock and the counter disagree", ms, kms)
_, lap = line("clock: stopwatch lap 1, ")
lm = re.fullmatch(r"clock: stopwatch lap 1, 00:(\d\d)\.(\d\d)", lap)
assert lm and 1000 <= int(lm.group(1)) * 1000 + int(lm.group(2)) * 10 < ms, ("lap 1", lap)

# the timer: 3 s, never early, and on time by both clocks and the host's
line("clock: timer set to 00:03")
h2, _ = line("clock: timer started, 00:03")
h3, done = line("clock: timer done after ")
m = re.fullmatch(r"clock: timer done after 3 s \((\d+) ms by the counter, (\d+) by the kernel's clock\)", done)
assert m, done
tms, tkms = int(m.group(1)), int(m.group(2))
assert 3000 <= tms <= 3400, ("the timer ended after", tms)
assert tms // 3 <= tkms <= tms + 20, ("the kernel's clock and the counter disagree", tms, tkms)
assert abs(tms - (h3 - h2) * 1000) <= 800, ("the timer took", tms, "and the host saw", (h3 - h2) * 1000)
line("clock: showing the timer")
line("clock: timer reset to 00:03")

# the pixels: which tab is lit, the stopwatch's Start, the flash
log = open(os.path.join(T, "serial.txt")).read()
wx, wy = window_pos(log, "clock")
def load(name):
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[((wy + TITLE_H + y) * w + wx + x) * 3:((wy + TITLE_H + y) * w + wx + x) * 3 + 3])
BG, LIT, PILL, GO, FLASH = (20, 22, 32), (56, 62, 90), (32, 35, 50), (30, 86, 116), (196, 64, 56)
def lit(at, tab):
    got = [at(33 + 78 * i + 39, 9) for i in range(3)]
    assert got == [LIT if i == tab else PILL for i in range(3)], ("the lit tab is not", tab, got)
for name, tab in (("clock-clock", 0), ("clock-stopwatch", 1), ("clock-timer", 2), ("clock-after", 2)):
    lit(load(name), tab)
    assert load(name)(5, 60) == BG, (name, "background", load(name)(5, 60))
assert load("clock-stopwatch")(195 + 6, 116 + 13) == GO, ("the stopwatch does not offer Start", load("clock-stopwatch")(201, 129))
flashes = [load(f"clock-done-{k}")(5, 60) for k in range(1, 5)]
assert FLASH in flashes, ("no flash", flashes)
assert all(f in (FLASH, BG) for f in flashes), flashes
for k in range(1, 5):
    lit(load(f"clock-done-{k}"), 2)
print(f"ok: the stopwatch ran {ms} ms by the counter ({kms} by the kernel's clock, {host:.0f} by the host's); "
      f"the timer of 3 s ended after {tms} ms ({tkms}); each tab lit when shown; the flash in {flashes.count(FLASH)} of 4 captures")
PY
echo "ok: Clock's stopwatch and timer keep the kernel's and the counter's time, and show the tab they are on"
