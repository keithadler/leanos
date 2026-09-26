#!/bin/bash
# What the file server gives programs from the card: its 48 records of who may reach what
# (user/fs.c) must never run out. Each open slot may hold 8 (its folder and 7 files, the
# most Terminal's run gives), what a stopped program was given is taken back (Terminal's
# kill, or the next start in its slot), and so a new program always gets its folder and
# its files, whatever ran before it.
#
# fsfuzz, on a card of its own as fsgbig, fsg1 to fsg6 and fsgx, asks the file server what
# it was given and reaches for each path: "given N paths, M reachable". Terminal writes 20
# files; `run fsgbig` with all 20 is refused (7 at most). Twice: fsg1 to fsg6, each given 7
# files, fill the six slots (all 48 records), then are killed in a jumbled order, and each
# kill takes its 8 back. Then fsg2 to fsg6 again, and fsgx, which ends by itself and leaves
# its 8 behind; the table is full, and fsg1, started in fsgx's slot, still gets all it names.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/fsfuzz.elf || fail "fsfuzz did not build"
card=$T/sd-grants.img
names="fsgbig fsg1 fsg2 fsg3 fsg4 fsg5 fsg6 fsgx"
python3 tools/mksd.py "$card" $(for n in $names; do echo "$n=build/progs/fsfuzz.elf"; done) >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
def cmd(line, done, times=1):
    return [(line + "\r").encode(), wait_for(done, times)]
files = [f"f{i}" for i in range(20)]
seven = " ".join(files[:7])
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened")]
for i, f in enumerate(files):
    steps += cmd(f"write {f} {i}", f"terminal: write {f} ")
steps += cmd("run fsgbig " + " ".join(files), "terminal: run fsgbig")
given = {}
def run(name):
    given[name] = given.get(name, 0) + 1
    return cmd(f"run {name} {seven}", f"fsfuzz: {name}: given", given[name])
kills = 0
for cycle in range(2):
    for k in range(1, 7):
        steps += run(f"fsg{k}")
    for slot in (12, 10, 15, 11, 14, 13):
        kills += 1
        steps += cmd(f"kill {slot}", "terminal: kill", kills)
for k in range(2, 7):
    steps += run(f"fsg{k}")
steps += run("fsgx")
steps += run("fsg1")
steps += cmd("ps", "terminal: ps")
sys.exit(boot(150, steps=steps, until="terminal: ps", sd=card, settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(fsfuzz: |fs: took back|terminal: (run|kill|ps) |leanos: (slot 1. stopped|PANIC))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -qx "terminal: run fsgbig -> more than 7 files" || fail "a run naming 20 files was not refused"
echo "$out" | grep -q "^fsfuzz: fsgbig" && fail "fsgbig ran"
# every program got its folder and its 7 files, and reached each: 12 in the cycles, 7 after
n=$(echo "$out" | grep -c "^fsfuzz: fsg[1-6x]: given 8 paths, 8 reachable$")
[ "$n" = 19 ] || fail "$n of 19 programs were given their folder and 7 files: $(echo "$out" | grep '^fsfuzz: fsg' | grep -v 'given 8 paths, 8 reachable' | head -1)"
# Each kill took back the 8 its program was given, at once (the file server says so just
# before Terminal says the kill is done), so a start found nothing left to take back; but
# fsg1's, in the slot fsgx ended in by itself (15, the one free), which took back fsgx's 8.
for slot in 10 11 12 13 14 15; do
  [ "$(echo "$out" | grep -c "^terminal: kill $slot -> stopped$")" = 2 ] || fail "kill $slot did not stop its program twice"
done
order=$(echo "$out" | grep -E "^(fs: took back|terminal: (run|kill) )" | awk '
  /^terminal: kill/ && prev != "fs: took back 8 paths from slot " $3 { print "kill " $3 " took nothing back"; exit }
  /^terminal: run/ && prev ~ /^fs: took back/ && $0 != "terminal: run fsg1 -> slot 15" { print "a start took back: " prev; exit }
  /^terminal: run fsg1 -> slot 15$/ && prev != "fs: took back 8 paths from slot 15" { print "fsg1 took nothing back from fsgx"; exit }
  { prev = $0 }')
[ -z "$order" ] || fail "$order"
echo "$out" | grep -qx "terminal: run fsg1 -> slot 15" || fail "fsg1 did not start in fsgx's slot"
[ "$(echo "$out" | grep -c "^fs: took back")" = 13 ] || fail "not 13 takings back: $(echo "$out" | grep '^fs: took back' | tr '\n' ';')"
# the five tasks test/kill.sh counts, and a program in each of the six open slots
echo "$out" | grep -qx "terminal: ps -> 11 running" || fail "not a program in every open slot: $(echo "$out" | grep '^terminal: ps ->')"
echo "ok: 20 files for one program refused; 19 programs given their folder and 7 files each, over kills, a program that ended by itself and a full table"
