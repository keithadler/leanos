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

check_order terminal \
  "terminal: opened a window -> ok" \
  "terminal: caps -> 6 capabilities" \
  "terminal: boot -> 6 verified" \
  "terminal: window closed, exiting" \
  "terminal: opened a window -> ok" \
  "terminal: caps -> 6 capabilities"

check_order settings \
  "settings: opened a window -> ok" \
  "settings: background set to Graphite -> ok"

check_order security \
  "security: opened a window -> ok" \
  "security: 8 verified, 0 refused, 0 not loaded"

# The kernel loads and checks an app each time it is started, and only then.
[ "$(echo "$out" | grep -c "^leanos: terminal started$")" = 2 ] || fail "Terminal was not started twice"
[ "$(echo "$out" | grep -c "^leanos: terminal verified, sha256 ")" = 2 ] || fail "Terminal was not checked on each start"
for app in settings security; do
  [ "$(echo "$out" | grep -c "^leanos: $app verified, sha256 ")" = 1 ] || fail "$app was not checked once"
done
for app in terminal settings security; do
  echo "$out" | grep -B1000 "^leanos: idle" | grep -q "^leanos: $app" && fail "$app was loaded before anyone started it"
done

display=$(echo "$out" | grep -E "^display: (start|closed|background)")
expected=$(printf '%s\n' "display: start Terminal -> ok" "display: start Settings -> ok" \
  "display: background 1, as Settings asked" "display: closed Terminal's window" \
  "display: start Terminal -> ok" "display: start Security -> ok")
[ "$display" = "$expected" ] || { echo "got:"; echo "$display"; fail "display did not start, close and restart as asked"; }

echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: apps start from the dock, are checked on every start, and stop when closed"

python3 - <<'PY' || fail "the screen is not what the apps drew"
data = open("build/screen.ppm", "rb").read()
_, dims, _, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
at = lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])

# Graphite: gray, not the default indigo
r, g, b = at(1000, 300)
assert b - r < 20 and max(r, g, b) < 90, ("graphite background", (r, g, b))
# Security's report: a green check beside each of the eight programs
green = lambda r, g, b: g > 150 and r < 120 and b < 140
for k in range(8):
    y0 = 184 + 44 + 20 * k
    assert sum(1 for y in range(y0, y0 + 16) for x in range(236, 252) if green(*at(x, y))) > 60, ("check", k)
# Terminal's dark window, below Security's
assert max(at(170, 400)) < 60, ("terminal", at(170, 400))
print("ok: the Graphite background, Security's eight checks and Terminal are on screen")
PY
