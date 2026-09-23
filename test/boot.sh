#!/bin/bash
# Boots leanos on QEMU's Raspberry Pi 4 and checks what it did: the axioms every proof rests
# on, the serial transcript, and the pixels on the screen.
set -u
cd "$(dirname "$0")/.."

fail() { echo "FAIL: $*"; exit 1; }

# Axioms: only Lean's standard three, and never sorryAx.
axioms=$(lake env lean test/Axioms.lean 2>&1) || fail "axiom check did not run: $axioms"
echo "$axioms" | grep -q sorryAx && fail "a theorem depends on sorry"
echo "$axioms" | grep -v "depends on axioms: \[\(propext\|Classical.choice\|Quot.sound\)\(, \(propext\|Classical.choice\|Quot.sound\)\)*\]" \
  | grep -q . && fail "unexpected axiom: $axioms"
echo "ok: $(echo "$axioms" | wc -l | tr -d ' ') theorems rest only on Lean's standard axioms"

rm -f build/screen.ppm build/screen.png
out=$(python3 test/run.py 30)
status=$?
echo "$out" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not reach idle (status $status)"

# Each task's lines must appear in this order; tasks may interleave with each other.
check_order() {
  local who=$1; shift
  local got
  got=$(echo "$out" | grep -E "^($who: |leanos: $who )")
  local expected
  expected=$(printf '%s\n' "$@")
  [ "$got" = "$expected" ] || { echo "expected for $who:"; echo "$expected"; echo "got:"; echo "$got"; fail "$who"; }
}

check_order alice \
  "alice: wrote secret 0x5ec12e7 to my data page" \
  "alice: sent the display a 240x100 window, read-only, 24 pages -> ok" \
  "alice: secret intact, exiting"

check_order mallory \
  "mallory: I am task 2" \
  "mallory: map capability 9 (not mine) at page 5 -> refused, no such capability" \
  "mallory: print 16 bytes of kernel memory at 0x80000 -> refused, not allowed" \
  "mallory: receive on the display's endpoint -> refused, not allowed" \
  "mallory: send the display a window of my pixels -> refused, not allowed" \
  "mallory: map the framebuffer (capability 5, which is the display's) -> refused, no such capability" \
  "mallory: map the endpoint as memory -> refused, not allowed" \
  "mallory: asked for every right on the endpoint, got send" \
  "mallory: ask the display for a window without pixels -> ok" \
  "mallory: writing to the screen's physical address 0x3c100000 directly" \
  "leanos: mallory stopped: data access not allowed at 0x3c100000"

check_order carol \
  "carol: asked for write+execute on my data frame, got -w-" \
  "carol: jumping into the instruction I wrote in my data page" \
  "leanos: carol stopped: instruction fetch not allowed at 0x80010000"

# The display's messages may arrive in any order; each must arrive exactly once.
display=$(echo "$out" | grep -E "^display: ")
[ "$(echo "$display" | head -1)" = "display: desktop drawn on the 640x480 framebuffer" ] || fail "display did not draw the desktop"
for line in \
  "display: alice's window, 240x100 from a read-only capability to 24 pages, drawn at (60, 70)" \
  "display: mallory asked for a window but sent no pixels; ignored"; do
  [ "$(echo "$display" | grep -cxF "$line")" = 1 ] || fail "display line missing or repeated: $line"
done
[ "$(echo "$display" | wc -l | tr -d ' ')" = 3 ] || fail "display printed unexpected lines"

echo "$out" | grep -q "^leanos: framebuffer 640x480 at 0x3c100000$" || fail "no framebuffer"
echo "$out" | grep -q "^leanos: idle, 1 task waiting for a message" || fail "did not settle with the display waiting"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: boot transcript matches"

# The screen itself.
python3 - <<'PY' || fail "the screen is not what the display drew"
data = open("build/screen.ppm", "rb").read()
_, dims, _, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
assert (w, h) == (640, 480), (w, h)

def at(x, y):
    i = (y * w + x) * 3
    return tuple(px[i:i + 3])

exact = {
    (0, 0): (245, 243, 236),     # menu bar, where mallory tried to write 0xbad
    (1, 0): (245, 243, 236),
    (100, 80): (58, 96, 150),    # alice's title bar
    (272, 104): (58, 150, 96),   # the green square alice drew
}
for (x, y), want in exact.items():
    assert at(x, y) == want, ((x, y), at(x, y), want)
r, g, b = at(320, 400)           # the desktop gradient
assert 20 < r < 40 and 80 < g < 110 and 90 < b < 120, (r, g, b)
print("ok: the screen shows the desktop and alice's window; mallory's write never landed")
PY
