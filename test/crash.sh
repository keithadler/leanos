#!/bin/bash
# Power cuts. Terminal rewrites a 200 KB file over and over (fill: written in pieces to
# f.tmp, then renamed over f in one step), and the machine is killed at a random moment,
# twelve times. After each cut, the card must check clean on the next boot (the journal
# either finishes or drops the interrupted change: nothing to repair), and f must be one
# whole version, never half of each: 204800 bytes all the same letter (or not there yet),
# and never older than the last change the file server said was done.
#
# The cuts run on CRASH_LANES cards at once (default 3; 1 is one card cut twelve times):
# cut i on card i mod CRASH_LANES, each card cut again and again, booted from where the last
# cut left it. The twelve cut times are the same whatever the number of cards, from one seed.
set -u
cd "$(dirname "$0")/.."
# this run's files (screens, cards): test/all.py gives each test its own folder
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
lanes=${CRASH_LANES:-3}
[[ "$lanes" =~ ^[0-9]+$ ]] && [ "$lanes" -ge 1 ] && [ "$lanes" -le 12 ] || fail "CRASH_LANES must be 1 to 12"

# card k of the lanes: its own folder (for the screen captures) and its own copy of the card
lane() {
  local dir=$T/crash-$1
  mkdir -p "$dir"
  cp build/sd-template.img "$dir/sd-crash.img"
  LEANOS_TEST_DIR=$dir python3 - "$dir/sd-crash.img" "$1" "$lanes" <<'PY'
import random, sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card, lane, lanes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
random.seed(20260923)
quiet = lambda line: None
finished = dropped = 0
for i in range(12):
    # the cut: some time into a stream of rewrites
    cut = random.uniform(9, 22)
    if i % lanes != lane:
        continue                # another card's cut
    steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened")]
    for k in range(40):     # one at a time: a typed-ahead queue only holds so much
        steps += keys(f"fill f 200 {'abcdefghij'[k % 10]}\r") + [wait_for("terminal: fill f", k + 1)]
    lines = []
    boot(cut, on_line=lines.append, steps=steps, until="never", sd=card, cut=True)
    fills = sum(l.startswith("terminal: fill f -> ok") for l in lines)
    # the next boot: check the card, then look at f
    lines = []
    boot(60, on_line=lines.append, sd=card, until="terminal: verify", settle=0.5,
         steps=[*click(*DOCK["Terminal"]), wait_for("terminal: opened"), *keys("verify f\r")])
    got = [l for l in lines if l.startswith(("fs:", "terminal: verify", "leanos: PANIC"))]
    finished += any(l.startswith("fs: finished") for l in got)
    dropped += any(l.startswith("fs: dropped") for l in got)
    # durable: f is the last fill the log saw finish, or the one after (its commit made it,
    # its log line did not): never an older one
    import re
    m = [re.search(r"verify f -> 204800 bytes of '(.)'", l) for l in got]
    letter = next((x.group(1) for x in m if x), None)
    ok = fills == 0 or letter in ("abcdefghij"[(fills - 1) % 10], "abcdefghij"[fills % 10])
    print(f"cut {i + 1}, card {lane + 1}: after {cut:.1f} s, {fills} fills logged{'' if ok else ', LOST'}; " + " / ".join(got), flush=True)
print(f"crash: card {lane + 1}: journal finished {finished} interrupted changes and dropped {dropped}", flush=True)
PY
}

logs=()
for ((k = 0; k < lanes; k++)); do
  logs+=("$T/crash-$k.log")
  lane $k > "$T/crash-$k.log" 2>&1 &
done
wait
out=$(cat "${logs[@]}")
{ echo "$out" | grep "^cut " | sort -n -k2,2; echo "$out" | grep -v "^cut "; } | sed 's/^/  | /'
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
[ "$(echo "$out" | grep -c "^cut ")" = 12 ] || fail "the twelve cuts did not all run"
echo "$out" | grep "^cut " | grep -q "fs: repaired" && fail "a power cut left something to repair"
echo "$out" | grep "^cut " | grep -q "mixed" && fail "a power cut left half of one version and half of another"
echo "$out" | grep "^cut " | grep -vq "fs: checked" && fail "a boot did not check the card"
echo "$out" | grep "^cut " | grep -q ", LOST;" && fail "a change the file server had committed was lost"
# a cut before the first fill finished leaves no f yet (and then no fill was logged: a
# logged fill with f missing is caught as LOST above)
bad=$(echo "$out" | grep "^cut " | grep "terminal: verify f -> " | grep -v "terminal: verify f -> 204800 bytes of '[a-j]'" | grep -v "verify f -> no such file")
[ -z "$bad" ] || fail "f was not one whole version: $bad"
# and the rewrites really happened: most cuts find a whole f (a fill that never succeeds
# would leave no f at all, and prove nothing)
[ "$(echo "$out" | grep "^cut " | grep -c "verify f -> 204800 bytes of")" -ge 6 ] || fail "the fills did not run"
# on every card: at least half of its cuts (6 of 12 on one card, 2 of 4 on each of three)
for ((k = 1; k <= lanes; k++)); do
  cuts=$(echo "$out" | grep -c "^cut [0-9]*, card $k: ")
  whole=$(echo "$out" | grep "^cut [0-9]*, card $k: " | grep -c "verify f -> 204800 bytes of")
  [ "$whole" -ge $((cuts / 2)) ] || fail "the fills did not run on card $k ($whole of $cuts cuts found f)"
done
echo "ok: twelve power cuts in the middle of writes, and every time the card was consistent and the file whole"
