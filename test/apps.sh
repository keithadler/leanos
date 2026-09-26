#!/bin/bash
# Starts the apps from the dock and checks what happened: Terminal answers from the kernel,
# Settings changes the background, the close button stops Terminal and the dock starts it
# again (the kernel takes back its memory and checks it again), and Security reports every
# program verified. Then the pixels.
set -u
cd "$(dirname "$0")/.."
# this run's files (screens, cards): test/all.py gives each test its own folder
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"

fail() { echo "FAIL: $*"; exit 1; }

rm -f "$T/screen.ppm" "$T/screen.png" "$T/notes-again.ppm"
out=$(python3 test/run.py 120 --apps)
status=$?
echo "$out" > "$T/serial.txt"            # where each window opened, for the pixel checks
echo "$out" | grep -vE "^(mallory|carol): " | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish the interaction (status $status)"

check_order() {
  local who=$1; shift
  local got expected
  got=$(echo "$out" | grep -E "^$who: ")
  expected=$(printf '%s\n' "$@")
  [ "$got" = "$expected" ] || { echo "expected for $who:"; echo "$expected"; echo "got:"; echo "$got"; fail "$who"; }
}

check_order alice \
  "alice: wrote secret 0x5ec12e7 to my data page" \
  "alice: no saved note yet" \
  "alice: opened a 480x320 window, read-only, 150 pages -> ok" \
  "alice: saved note 1 (2 bytes)" \
  "alice: window closed, exiting" \
  "alice: wrote secret 0x5ec12e7 to my data page" \
  "alice: 1 note; loaded notes/1.txt, 2 bytes" \
  "alice: opened a 480x320 window, read-only, 150 pages -> ok"

check_order terminal \
  "terminal: opened a window -> ok" \
  "terminal: caps -> 14 capabilities" \
  "terminal: boot -> 8 verified" \
  "terminal: write hello.txt -> ok" \
  "terminal: ls -> 14 files" \
  "terminal: ls -a -> 24 files" \
  "terminal: window closed, exiting" \
  "terminal: opened a window -> ok" \
  "terminal: caps -> 14 capabilities" \
  "terminal: write fast.txt -> ok" \
  "terminal: cat fast.txt -> 36 bytes" \
  "terminal: run welcome.txt -> not an ELF file" \
  "terminal: run hello -> slot 10" \
  "terminal: run clock -> slot 11"

check_order hello \
  "hello: opened a window -> ok"

# The clock shows the Lean kernel's time: its hours, minutes and seconds are its tick count
# (10 ms each) in whole seconds (`time_reads_clock`).
echo "$out" | grep -qx "clock: opened a window -> ok" || fail "clock did not open"
python3 - "$(echo "$out" | grep "^clock: ticked 3 times")" <<'PY2' || fail "the clock does not show the kernel's ticks"
import re, sys
m = re.fullmatch(r"clock: ticked 3 times, at tick (\d+) \((\d\d):(\d\d):(\d\d)\)", sys.argv[1])
assert m, sys.argv[1]
t, h, mi, s = map(int, m.groups())
assert t * 10 // 1000 == h * 3600 + mi * 60 + s, sys.argv[1]
PY2

# Settings reads the board through the kernel (QEMU's model of a Pi 4B: revision 0xb03115,
# 25 C, 700 MHz) and changes it: the CPU to 600 MHz, the activity light on.
check_order settings \
  "settings: opened a window -> ok" \
  "settings: Raspberry Pi 4 Model B, revision 0xb03115, 25.0 C, CPU at 700 MHz" \
  "settings: time zone UTC" \
  "settings: background Indigo" \
  "settings: background set to Graphite -> ok" \
  "settings: CPU speed 600 MHz -> ok" \
  "settings: the firmware reports the CPU at 600 MHz" \
  "settings: activity light on -> ok"

# Files: the list (the programs' ten icons left out; settings.txt, where Apps saved the
# background Settings chose, included), then the down arrow through the files, past the 12
# rows it shows at once, to hello.txt
echo "$out" | grep -qx "files: listed 17 files" || fail "files did not list the card"
echo "$out" | grep -qx "apps: saved the time zone, UTC, and the background, Graphite, in settings.txt -> ok" \
  || fail "Apps did not save the background Settings chose"
[ "$(echo "$out" | grep -c "^files: showing ")" = 14 ] || fail "the down arrow did not walk the list"
echo "$out" | grep -E "^files: showing " | tail -1 | grep -qx "files: showing hello.txt (19 bytes)" || fail "files did not reach hello.txt"

check_order security \
  "security: opened a window -> ok" \
  "security: 13 verified, 0 refused, 4 not loaded"

# The kernel loads and checks an app each time it is started, and only then.
[ "$(echo "$out" | grep -c "^leanos: terminal started$")" = 2 ] || fail "Terminal was not started twice"
[ "$(echo "$out" | grep -c "^leanos: terminal verified, sha256 ")" = 2 ] || fail "Terminal was not checked on each start"
[ "$(echo "$out" | grep -c "^leanos: alice started$")" = 1 ] || fail "Notes was not started again"
for app in settings security files; do
  [ "$(echo "$out" | grep -c "^leanos: $app verified, sha256 ")" = 1 ] || fail "$app was not checked once"
done
for app in terminal settings security files; do
  echo "$out" | grep -B1000 "^leanos: idle" | grep -q "^leanos: $app" && fail "$app was loaded before anyone started it"
done

display=$(echo "$out" | grep -E "^display: (start|closed|background)")
expected=$(printf '%s\n' "display: start Apps -> ok" "display: closed alice's window" "display: start Notes -> ok" \
  "display: start Terminal -> ok" "display: start Settings -> ok" \
  "display: background 1, as Settings asked" "display: start Apps -> ok" "display: closed Terminal's window" \
  "display: start Terminal -> ok" "display: start Files -> ok" "display: start Security -> ok")
echo "$out" | grep -qE "^leanos: slot 10 runs a program from its starter, not the manifest; sha256 " \
  || fail "the kernel did not load hello into slot 10"
[ "$display" = "$expected" ] || { echo "got:"; echo "$display"; fail "display did not start, close and restart as asked"; }

echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: apps start from the dock, are checked on every start, stop when closed, and keep their files"

python3 - "$T" <<'PY' || fail "the screen is not what the apps drew"
import os, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
def load(name):
    data = open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
at = load("screen")
log = open(os.path.join(sys.argv[1], "serial.txt")).read()
sx, sy = window_pos(log, "Security")
nx, ny = window_pos(log, "alice")
tx, ty = window_pos(log, "Terminal")

# Graphite: gray, not the default indigo (the desktop left of the dock, where no window goes)
r, g, b = at(100, 560)
assert b - r < 20 and max(r, g, b) < 90, ("graphite background", (r, g, b))
# Security's report: a green check beside each of the ten manifest programs, a blue one
# beside hello and clock (slots 10 and 11, from the SD card), nothing for the empty open slots
green = lambda r, g, b: g > 150 and r < 120 and b < 140
blue = lambda r, g, b: b > 180 and r < 100
def count(k, pred):
    y0 = sy + 72 + 14 * k
    return sum(1 for y in range(y0 + 2, y0 + 14) for x in range(sx + 20, sx + 36) if pred(*at(x, y)))
for k in range(10):
    assert count(k, green) > 60, ("check", k)
for k in (10, 11):
    assert count(k, blue) > 60 and count(k, green) == 0, ("open slot", k, count(k, blue))
for k in (12, 13, 14, 15):   # (the edge of Apps' check, just below slot 15, may show)
    assert count(k, blue) == 0 and count(k, green) < 12, ("empty open slot", k, count(k, green))
assert count(16, green) > 60, ("Apps, started at boot for the startup items", count(16, green))
# the note came back after Notes started again: dark text where "Hi" is, in the note and as
# its title in the list
notes = load("notes-again")
assert sum(1 for y in range(ny + 42, ny + 62) for x in range(nx + 160, nx + 200) if max(notes(x, y)) < 100) > 20, \
    "the saved note"
assert sum(1 for y in range(ny + 84, ny + 104) for x in range(nx + 18, nx + 36) if max(notes(x, y)) < 100) > 20, \
    "the saved note's title"
# Terminal's dark window, below Security's: its left edge, left of Security
assert tx + 6 < sx, ("Terminal is not beside Security", (tx, ty), (sx, sy))
assert max(at(tx + 6, ty + 100)) < 60, ("terminal", at(tx + 6, ty + 100))
print("ok: the Graphite background, Security's ten checks, Terminal and the saved note are on screen")
PY

# Restart the Pi with the same SD card: the files are still there.
again=$(python3 test/run.py 40 --keep-sd)
[ $? -eq 0 ] || fail "the second boot did not reach idle"
echo "$again" | grep -E "^(fs: |alice: |apps: time zone|display: background)" | sed 's/^/  | /'
echo "$again" | grep -qx "fs: ready, 26 files on the SD card" || fail "the files did not survive a restart"
echo "$again" | grep -qx "apps: time zone UTC, background Graphite, from settings.txt -> ok" || fail "Apps did not read the background back"
echo "$again" | grep -qx "display: background 1, saved on the card" || fail "the Graphite background did not survive a restart"
echo "$again" | grep -qx "alice: 1 note; loaded notes/1.txt, 2 bytes" || fail "Notes did not get its note back after a restart"

# And with no card at all, the system still comes up, with files in memory only.
nocard=$(python3 test/run.py 40 --no-sd)
[ $? -eq 0 ] || fail "the boot with no SD card did not reach idle"
echo "$nocard" | grep -qx "leanos: no SD card" || fail "the kernel did not notice the missing card"
echo "$nocard" | grep -qx "fs: no SD card; files are kept in memory only; ready, 1 file" || fail "the file server did not fall back to memory"
# A blank card is formatted on first boot.
blank=$(python3 test/run.py 40 --blank-sd)
[ $? -eq 0 ] || fail "the boot with a blank card did not reach idle"
echo "$blank" | grep -qx "fs: made a new file system on the SD card; ready, 1 file" || fail "a blank card was not formatted"
# A card with no partition table is left alone: no data partition, so no disk.
raw=$(python3 test/run.py 40 --raw-sd)
[ $? -eq 0 ] || fail "the boot with an unpartitioned card did not reach idle"
echo "$raw" | grep -qx "leanos: SD card has no data partition (type 0xDA); files stay in memory" || fail "an unpartitioned card was not noticed"
echo "$raw" | grep -qx "fs: no SD card; files are kept in memory only; ready, 1 file" || fail "the file server used an unpartitioned card"
python3 -c "import sys; d=open(sys.argv[1],'rb').read(); sys.exit(any(d))" "$T/sd-test.img" || fail "something was written to the unpartitioned card"
echo "ok: the files and the note survive a restart on the SD card, a blank card is formatted, an unpartitioned card is never written, and the system runs without a card"
