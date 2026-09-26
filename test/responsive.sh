#!/bin/bash
# The desktop stays responsive while programs hog the CPU (LeanOS/Kernel.lean, `schedule`,
# `preempt`): a task an interrupt or a message wakes runs next on the core that woke it,
# instead of waiting its turn behind every program that only computes.
#
# chaos (user/progs/chaos.c) runs as `keys`, a window that shows each key it gets, drawn on
# the screen before it takes the next. A run of 96 keys is typed at once, three times; QEMU
# holds what the UART cannot take yet, so the machine takes them at its own pace: the input
# driver wakes on the UART's interrupt, sends each key to the display, the display hands it
# to `keys`, which draws and has the display put its window on the screen. `keys` says how
# many timer ticks (the kernel's clock) each run took. Then five `spin` programs start, each
# a loop that never makes a system call (one more program than there are cores), and the
# three runs are typed again.
#
# Loaded, the runs must take at most four times as many ticks as idle. Before, each task in
# that chain waited for a timer tick to give it a turn, and a run took about ten times as
# many ticks. Both are counted in ticks of the machine's own clock, not in seconds: a host
# that stops QEMU for a while costs a tick or two, not the whole time it was stopped, and a
# slow host is slow in both runs. The times are printed for the record.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/chaos.elf || fail "chaos did not build"
card=$T/sd-responsive.img
python3 tools/mksd.py "$card" keys=build/progs/chaos.elf spin=build/progs/chaos.elf >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys, time
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, pause, wclick, DOCK, TITLE_H
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
t0 = time.monotonic()
def line(l):
    print(f"{time.monotonic() - t0:8.2f} {l}", flush=True)
KEYS = 96
run_keys = ("[" + "".join(chr(ord("a") + k % 26) for k in range(KEYS)) + "]").encode()
done = [0]
def three_runs():
    steps = []
    for _ in range(3):
        done[0] += 1
        steps += [run_keys, wait_for("chaos: keys in slot 10: drew ", done[0]), pause(0.2)]
    return steps
# the program's window has no icon: the display calls it this
win = "a program from the SD card"
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         b"run keys\r", wait_for("chaos: keys in slot 10: a window"), pause(0.5)]
steps += three_runs()
steps += click(*DOCK["Terminal"])
for k in range(11, 16):
    steps += [b"run spin\r", wait_for(f"chaos: spin in slot {k}: spinning")]
steps += [pause(1), *wclick(win, 30, TITLE_H + 20), pause(0.5)]    # the keys go to `keys` again
steps += three_runs()
steps += [*click(*DOCK["Terminal"]), b"ps\r", wait_for("terminal: ps")]
sys.exit(boot(240, steps=steps, sd=card, on_line=line, until="terminal: ps"))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^ *[0-9.]+ (chaos: (keys|spin) in slot|terminal: (run|ps)|leanos: PANIC)" | sed 's/^/  | /'
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
runs=$(echo "$out" | sed -n 's/.*chaos: keys in slot 10: drew \([0-9]*\) keys in \([0-9]*\) ticks, \([0-9]*\) us.*/\1 \2 \3/p')
[ "$(echo "$runs" | grep -c .)" -eq 6 ] || fail "not all six runs of keys came through (status $status)"
echo "$runs" | awk '$1 != 96 { exit 1 }' || fail "a run lost keys: $(echo "$runs" | awk '{print $1}' | tr '\n' ' ')"
median() { sort -n | sed -n 2p; }
idle=$(echo "$runs" | head -3 | awk '{print $2}' | median)
loaded=$(echo "$runs" | tail -3 | awk '{print $2}' | median)
idle_ms=$(echo "$runs" | head -3 | awk '{print int($3 / 1000)}' | median)
loaded_ms=$(echo "$runs" | tail -3 | awk '{print int($3 / 1000)}' | median)
echo "96 keys typed at once: $idle ticks idle ($idle_ms ms), $loaded ticks beside five programs that never stop computing ($loaded_ms ms); the medians of three runs"
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
# at least 3 ticks idle, so a fast host is not held to a round-off
floor=$(( idle > 3 ? idle : 3 ))
[ "$loaded" -le $((4 * floor)) ] || fail "typing is $loaded ticks loaded against $idle idle: more than four times as slow"
echo "ok: 96 keys reach the screen in $loaded ticks beside programs hogging every core, $idle on an idle machine"
