#!/bin/bash
# The self-test (user/progs/selftest.c) on the self-test card, before it goes to a Pi. The card
# is `make pi-selftest`'s, built with QEMU's kernel and stand-in firmware in place of the Pi's:
# its config.txt must be the bring-up card's, marked as the self-test card, with the
# firmware's log on. Booted, Apps must list all 16 programs, selftest first, and
# start it from startup.txt. When selftest waits for input, a key and a click go to its
# window. Then it must finish, every check with a result line and none FAIL: memory, sd,
# sdfiles, clock, sleep, screen and input PASS; cpu, usb and time INFO. The window shows each
# check's state in its pill (green PASS, blue INFO). tools/serial.py's summary of the run
# must give the same report and counts.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
head -c 2300000 /dev/urandom > "$tmp/start4.elf"
head -c 5400 /dev/urandom > "$tmp/fixup4.dat"
card=$T/sd-selftest.img
make -s pi-selftest SELFTEST_IMG="$card" SELFTEST_KERNEL=build/kernel8.img SELFTEST_FIRMWARE="$tmp" >/dev/null \
  || fail "the self-test card was not built"
python3 - "$card" <<'PY' || fail "the self-test card's config.txt is not the bring-up card's"
import sys
sys.path.insert(0, "tools")
from mkpiimage import bringup_config
card = open(sys.argv[1], "rb").read()
config = bringup_config(True)
assert config.startswith(b"# The self-test card (make pi-selftest)") and b"\nuart_2ndstage=1\n" in config
assert card.find(config) >= 0, "config.txt is not on the card"
PY

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, wait_for, wclick
steps = [wait_for("selftest: input: waiting"), b"k", *wclick("selftest", 200, 150)]
sys.exit(boot(150, steps=steps, until="selftest: done", sd=sys.argv[1], settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(selftest|apps): " | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the self-test did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -E "^leanos: .* stopped: " | grep -vE "^leanos: (mallory|carol) stopped: " && fail "a task stopped"
echo "$out" | grep -qx "apps: 16 programs, 16 with icons" || fail "Apps did not list the 16 programs"
echo "$out" | grep -qE "^apps: selftest started in slot [0-9]+$" || fail "startup.txt did not start selftest"

python3 - "$T" <<'PY' || fail "the self-test's report is wrong"
import os, re, sys
sys.path.insert(0, "test")
sys.path.insert(0, "tools")
from run import window_pos, TITLE_H
from serial import summarize
T = sys.argv[1]
lines = open(os.path.join(T, "serial.txt")).read().splitlines()
results = {}
for l in lines:
    m = re.match(r"^selftest: (\S+): (PASS|FAIL|INFO) (.+)$", l)
    if m:
        assert m.group(1) not in results, ("two results for", m.group(1))
        results[m.group(1)] = m.group(2)
want = {"memory": "PASS", "sd": "PASS", "sdfiles": "PASS", "clock": "PASS", "sleep": "PASS", "screen": "PASS",
        "cpu": "INFO", "usb": "INFO", "time": "INFO", "input": "PASS"}
assert results == want, ("results", results)
done = [l for l in lines if l.startswith("selftest: done: ")]
assert done == ["selftest: done: 7 passed, 0 failed, 3 info"], done
assert any(re.match(r"^selftest: sd: PASS 1 MiB written in [\d.]+ ms \([\d.]+ MiB/s\), read in [\d.]+ ms "
                    r"\([\d.]+ MiB/s\), every byte right; deleted$", l) for l in lines), "the sd line"
assert any(l == "selftest: input: PASS a key (k) and a click at 200,120, through the display" for l in lines), \
    "the input line"

# the window: each check's pill in its state's color, just inside its left end
data = open(os.path.join(T, "screen.ppm"), "rb").read()
magic, dims, maxval, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
x0, y0 = window_pos(lines, "selftest")
color = {"PASS": b"\x2e\x9e\x5b", "INFO": b"\x3a\x6e\xe6"}
for i, name in enumerate(want):
    x, y = x0 + 17, y0 + TITLE_H + 54 + 28 * i + 14
    got = px[(y * w + x) * 3:(y * w + x) * 3 + 3]
    assert got == color[want[name]], (name, "pill", got.hex(), "at", (x, y))

# serial.py --summary: the same report, from the same lines
s = summarize([("00:00:00.000", 0.0, l) for l in lines])
at = s.index("self-test: 7 passed, 0 failed, 3 info")
assert s[at + 1:] == ["  " + l for l in lines if re.match(r"^selftest: \S+: (PASS|FAIL|INFO)\b", l)] + ["  " + done[0]], s
PY
echo "ok: the self-test card starts selftest, whose checks all pass or inform under QEMU (0 FAIL), shown in its window and in serial.py's summary"
