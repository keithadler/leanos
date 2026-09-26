#!/bin/bash
# The file server under fire: fsfuzz (user/progs/fsfuzz.c), on a card of its own under the
# names fsfuzz to fsfuzz5, run from Terminal into the open slots, where a program reaches only
# its own folder, apps/NAME, and what Terminal names for it.
#
#   Boot 1. Notes saves a note; Terminal writes a secret (zzsecret.txt, the bytes fsfuzz
#   looks for in every answer) and a file of 20 KiB, and gives each fsfuzz its seed.
#   fsfuzz4, given apps too, fills apps to 64 entries. fsfuzz makes its fixed requests (every
#   operation, bad paths, other folders, every limit, bad buffers, a folder 40 deep, a folder
#   of 300 entries, the card's totals as a file and a folder come and go), then fills the card
#   until the file server says full (and its totals say so); with the card full,
#   Terminal starts fsfuzz5, whose folder cannot be made (apps would need a cluster more).
#   Then fsfuzz empties the card and makes random requests checked against a model, fsfuzz2
#   and fsfuzz3 make theirs beside it, and Terminal writes and reads files at the same time.
#   Boot 2. The card must check clean (no repairs). Terminal writes the secret again (a new
#   file takes a free inode), then fsfuzz reads back every file it left, one 40 folders deep;
#   Notes' note and Terminal's files must be as they were.
#
# Every answer each fsfuzz got must be the one the protocol allows, a refusal must say
# nothing more, no answer may hold the secret, and the file server must answer every request
# (it cannot be restarted). The seed is printed: FSFUZZ_SEED=N test/fsfuzz.sh runs it again.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/fsfuzz.elf || fail "fsfuzz did not build"
seed=${FSFUZZ_SEED:-$(( (RANDOM << 15 | RANDOM) + 1 ))}
echo "seed $seed (FSFUZZ_SEED=$seed test/fsfuzz.sh runs this again)"
card=$T/sd-fsfuzz.img
python3 tools/mksd.py "$card" fsfuzz=build/progs/fsfuzz.elf fsfuzz2=build/progs/fsfuzz.elf \
  fsfuzz3=build/progs/fsfuzz.elf fsfuzz4=build/progs/fsfuzz.elf fsfuzz5=build/progs/fsfuzz.elf >/dev/null || fail "no card"

out=$(python3 - "$card" "$seed" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card, seed = sys.argv[1], int(sys.argv[2])
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [s.encode()]           # a whole command at once
def cmd(line, done):
    return [*keys(line + "\r"), wait_for(done)]
SECRET = "fsfuzz-must-never-read-this"
steps = [*[b"k"] * 3, *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *cmd("mkdir apps", "terminal: mkdir apps "),
         *cmd(f"write zzsecret.txt {SECRET}", "terminal: write zzsecret.txt"),
         *cmd("fill keep 20 k", "terminal: fill keep")]
for k, name in enumerate(["fsfuzz", "fsfuzz2", "fsfuzz3"]):
    steps += cmd(f"mkdir apps/{name}", f"terminal: mkdir apps/{name} ")
    steps += cmd(f"write apps/{name}/seed {seed + k}", f"terminal: write apps/{name}/seed")
# fsfuzz4, given apps as well as its own folder, fills apps to 64 entries (one cluster)
steps += cmd("run fsfuzz4 apps", "terminal: run fsfuzz4 -> slot")
steps += [wait_for("fsfuzz: fsfuzz4 in slot 10: apps has")]
steps += cmd("run fsfuzz", "terminal: run fsfuzz -> slot")
# with the card full, a program whose folder cannot be made: apps would need a cluster more
steps += [wait_for("fsfuzz: fsfuzz in slot 11: the card is full")] + cmd("run fsfuzz5", "terminal: run fsfuzz5 -> slot")
steps += [wait_for("fsfuzz: fsfuzz in slot 11: regressions and a full card")]
steps += cmd("run fsfuzz2", "terminal: run fsfuzz2 -> slot") + cmd("run fsfuzz3", "terminal: run fsfuzz3 -> slot")
# Terminal is a client too, beside them
for i in range(3):
    steps += cmd(f"fill t{i} {10 + 10 * i} {'xyz'[i]}", f"terminal: fill t{i}")
    steps += cmd(f"verify t{i}", f"terminal: verify t{i}")
steps += cmd("verify notes.txt", "terminal: verify notes.txt")
steps += [wait_for("fsfuzz: fsfuzz2 in slot 13: all done"), wait_for("fsfuzz: fsfuzz3 in slot 14: all done"),
          wait_for("fsfuzz: fsfuzz in slot 11: all done")]
first = boot(180, steps=steps, until="fsfuzz: fsfuzz in slot 11: all done", sd=card)
print("---- boot 2", flush=True)
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *cmd(f"write zzsecret2.txt {SECRET}", "terminal: write zzsecret2.txt"),
         *cmd("run fsfuzz", "terminal: run fsfuzz -> slot"), wait_for("fsfuzz: fsfuzz in slot 10: checked after a restart"),
         *cmd("verify keep", "terminal: verify keep"), *cmd("verify notes.txt", "terminal: verify notes.txt"),
         *cmd("cat zzsecret.txt", "terminal: cat zzsecret.txt")]
for i in range(3):
    steps += cmd(f"verify t{i}", f"terminal: verify t{i}")
sys.exit(first or boot(120, steps=steps, until="terminal: verify t2", sd=card))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^(fsfuzz: |---- boot|fs: (ready|checked|repaired|finished|dropped)|terminal: (run|verify|cat) |leanos: (slot 1. stopped|PANIC)|alice: loaded)" \
  | grep -v "random requests so far" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: ([a-z]+|slot 1[0-5]) stopped" | grep -vE "^leanos: (mallory|carol) stopped" | head -1)
[ -z "$bad" ] || fail "a server or program stopped: $bad"
boot2=$(echo "$out" | sed -n '/^---- boot 2/,$p')
[ -n "$boot2" ] || fail "no second boot"

# Every fsfuzz finished, and every answer was the one allowed.
for line in "fsfuzz in slot 11: fixed requests" "fsfuzz in slot 11: regressions and a full card" \
            "fsfuzz in slot 11: all done" "fsfuzz2 in slot 13: all done" "fsfuzz3 in slot 14: all done"; do
  echo "$out" | grep -q "^fsfuzz: $line: [0-9]* requests, 0 wrong" || fail "fsfuzz: $line: $(echo "$out" | grep "^fsfuzz: $line" | head -1)"
done
echo "$out" | grep -q "^fsfuzz: fsfuzz4 in slot 10: apps has 64 entries" || fail "fsfuzz4 did not fill apps"
echo "$out" | grep -q "^fsfuzz: fsfuzz in slot 11: the card is full after [0-9]* KiB" || fail "the card did not fill"
echo "$out" | grep -q "^fsfuzz: fsfuzz5 in slot 12: given 0 paths (the card was full)" || fail "fsfuzz5 was given a folder on a full card"
echo "$out" | grep -q "WRONG" && fail "a wrong answer: $(echo "$out" | grep WRONG | head -1)"
# the file server answered each request in time (the slowest is the fill's, a few ms)
slow=$(echo "$out" | sed -n 's/^fsfuzz: .* slowest answer \([0-9]*\) ms, .*/\1/p' | sort -n | tail -1)
[ -n "$slow" ] && [ "$slow" -le 2000 ] || fail "an answer took ${slow:-?} ms"
# a change that fails costs about what a stat of the same path does, not a reload of every
# block of metadata from the card as well (17 ms each, before): 200 of each, timed, and the
# failed changes may take at most 1.5 times as long, however they fail
for what in "failed changes" "failed changes on a full card"; do
  t=$(echo "$out" | sed -n "s/^fsfuzz: fsfuzz in slot 11: $what: 200 in \([0-9]*\) us, 200 stats of the same paths in \([0-9]*\) us$/\1 \2/p")
  read -r us stat <<<"$t"
  [ -n "${stat:-}" ] && [ $((us * 2)) -le $((stat * 3)) ] || fail "200 $what took ${us:-?} us, 200 stats ${stat:-?} us"
done

# Terminal, a client beside them, got its files back whole
for i in 0 1 2; do
  n=$(( (10 + 10 * i) * 1024 )); c=$(echo xyz | cut -c$((i + 1)))
  [ "$(echo "$out" | grep -c "^terminal: verify t$i -> $n bytes of '$c'")" = 2 ] || fail "Terminal's t$i was not whole, before and after the restart"
done

# The next boot: the card checks clean, fsfuzz finds every file it left, the others' files are intact.
echo "$boot2" | grep -q "^fs: checked: " || fail "the card was not checked"
echo "$boot2" | grep -q "^fs: repaired" && fail "the card needed repairs: $(echo "$boot2" | grep '^fs: repaired')"
echo "$boot2" | grep -q "^fsfuzz: fsfuzz in slot 10: checked after a restart: [0-9]* requests, 0 wrong" \
  || fail "fsfuzz did not find its files as it left them"
echo "$boot2" | grep -q "^alice: loaded notes.txt, 3 bytes" || fail "Notes' note was not loaded"
echo "$boot2" | grep -q "^terminal: verify notes.txt -> 3 bytes of 'k'" || fail "Notes' note changed"
echo "$boot2" | grep -q "^terminal: verify keep -> 20480 bytes of 'k'" || fail "Terminal's keep changed"
echo "$boot2" | grep -q "^terminal: cat zzsecret.txt -> 27 bytes" || fail "the secret changed"
total=$(echo "$out" | sed -n 's/^fsfuzz: .*: all done: \([0-9]*\) requests.*/\1/p' | awk '{ n += $1 } END { print n }')
echo "ok: $total requests from fsfuzz, and fsfuzz2 and fsfuzz3 beside it, every answer as allowed (seed $seed), slowest $slow ms; the card full and emptied; clean after a restart, every file as left"
