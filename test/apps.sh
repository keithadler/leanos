#!/bin/bash
# Starts the apps from the dock and checks what happened: Terminal answers from the kernel,
# Settings changes the background, the close button stops Terminal and the dock starts it
# again (the kernel takes back its memory and checks it again), and Security reports every
# program verified. Then the pixels.
set -u
cd "$(dirname "$0")/.."

fail() { echo "FAIL: $*"; exit 1; }

rm -f build/screen.ppm build/screen.png
out=$(python3 test/run.py 90 --apps)
status=$?
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
  "alice: opened a 300x200 window, read-only, 59 pages -> ok" \
  "alice: window closed, exiting" \
  "alice: wrote secret 0x5ec12e7 to my data page" \
  "alice: loaded notes.txt, 2 bytes" \
  "alice: opened a 300x200 window, read-only, 59 pages -> ok"

check_order terminal \
  "terminal: opened a window -> ok" \
  "terminal: caps -> 7 capabilities" \
  "terminal: boot -> 7 verified" \
  "terminal: write hello.txt -> ok" \
  "terminal: ls -> 3 files" \
  "terminal: window closed, exiting" \
  "terminal: opened a window -> ok" \
  "terminal: caps -> 7 capabilities" \
  "terminal: write fast.txt -> ok" \
  "terminal: cat fast.txt -> 36 bytes"

check_order settings \
  "settings: opened a window -> ok" \
  "settings: background set to Graphite -> ok"

check_order files \
  "files: listed 4 files" \
  "files: showing welcome.txt (169 bytes)" \
  "files: opened a window -> ok" \
  "files: listed 4 files" \
  "files: showing hello.txt (19 bytes)"

check_order security \
  "security: opened a window -> ok" \
  "security: 10 verified, 0 refused, 0 not loaded"

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
expected=$(printf '%s\n' "display: closed alice's window" "display: start Notes -> ok" \
  "display: start Terminal -> ok" "display: start Settings -> ok" \
  "display: background 1, as Settings asked" "display: closed Terminal's window" \
  "display: start Terminal -> ok" "display: start Files -> ok" "display: start Security -> ok")
[ "$display" = "$expected" ] || { echo "got:"; echo "$display"; fail "display did not start, close and restart as asked"; }

echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: apps start from the dock, are checked on every start, stop when closed, and keep their files"

python3 - <<'PY' || fail "the screen is not what the apps drew"
data = open("build/screen.ppm", "rb").read()
_, dims, _, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
at = lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])

# Graphite: gray, not the default indigo
r, g, b = at(1000, 300)
assert b - r < 20 and max(r, g, b) < 90, ("graphite background", (r, g, b))
# Security's report: a green check beside each of the ten programs
green = lambda r, g, b: g > 150 and r < 120 and b < 140
for k in range(10):
    y0 = 156 + 42 + 18 * k
    assert sum(1 for y in range(y0, y0 + 16) for x in range(276, 292) if green(*at(x, y))) > 60, ("check", k)
# the note came back after Notes started again: dark text where "Hi" is
assert sum(1 for y in range(160, 180) for x in range(114, 132) if max(at(x, y)) < 100) > 20, "the saved note"
# Terminal's dark window, below Security's
assert max(at(170, 400)) < 60, ("terminal", at(170, 400))
print("ok: the Graphite background, Security's ten checks, Terminal and the saved note are on screen")
PY

# Restart the Pi with the same SD card: the files are still there.
again=$(python3 test/run.py 40 --keep-sd)
[ $? -eq 0 ] || fail "the second boot did not reach idle"
echo "$again" | grep -E "^(fs|alice): " | sed 's/^/  | /'
echo "$again" | grep -qx "fs: ready, 4 files on the SD card" || fail "the files did not survive a restart"
echo "$again" | grep -qx "alice: loaded notes.txt, 2 bytes" || fail "Notes did not get its note back after a restart"

# And with no card at all, the system still comes up, with files in memory only.
nocard=$(python3 test/run.py 40 --no-sd)
[ $? -eq 0 ] || fail "the boot with no SD card did not reach idle"
echo "$nocard" | grep -qx "leanos: no SD card" || fail "the kernel did not notice the missing card"
echo "$nocard" | grep -qx "fs: no SD card; files are kept in memory only; ready, 1 file" || fail "the file server did not fall back to memory"
echo "ok: the files and the note survive a restart on the SD card, and the system runs without one"
