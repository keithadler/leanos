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

rm -f build/screen.ppm build/screen.png build/logo.ppm build/logo.png
# Boot, wait for the desktop to settle, type "Hi!" into the Notes window, drag it by its
# title bar, then capture the screen (test/run.py, DEMO_STEPS).
out=$(python3 test/run.py 40 --demo)
status=$?
echo "$out" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish the interaction (status $status)"

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
  "alice: opened a 300x200 window, read-only, 59 pages -> ok"

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

check_order input \
  "input: listening on the UART"

# The display: logo, desktop, the two window requests in either order, then the keys and
# the drag, in order.
display=$(echo "$out" | grep -E "^display: ")
expected_head=$(printf '%s\n' "display: boot logo drawn" "display: desktop drawn on the 1024x600 framebuffer")
[ "$(echo "$display" | head -2)" = "$expected_head" ] || fail "display did not draw the logo and desktop"
for line in \
  "display: alice opened a 300x200 window from a read-only capability to 59 pages" \
  "display: mallory asked for a window but sent no pixels; ignored"; do
  [ "$(echo "$display" | grep -cxF "$line")" = 1 ] || fail "display line missing or repeated: $line"
done
expected_tail=$(printf '%s\n' "display: key 'H' to alice" "display: key 'i' to alice" "display: key '!' to alice" \
  "display: moved alice's window to (276, 208)")
[ "$(echo "$display" | tail -4)" = "$expected_tail" ] || fail "keys or drag not handled"
[ "$(echo "$display" | wc -l | tr -d ' ')" = 8 ] || fail "display printed unexpected lines"

echo "$out" | grep -q "^leanos: framebuffer 1024x600 at 0x3c100000$" || fail "no framebuffer"
echo "$out" | grep -q "^leanos: idle, 3 tasks waiting" || fail "did not settle with three tasks waiting"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: boot transcript matches"

# The screens themselves.
python3 - <<'PY' || fail "the screen is not what the display drew"
def load(path):
    data = open(path, "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    assert (w, h) == (1024, 600), (w, h)
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])

logo = load("build/logo.ppm")
r, g, b = logo(566, 172)          # the logo tile, off the lambda: indigo to teal
assert b > r + 40 and b > 120, ("logo", (r, g, b))
assert logo(512, 434)[1] > 150, ("progress bar, full", logo(512, 434))
assert sum(1 for x in range(440, 590) if max(logo(x, 567)) > 80) > 20, "copyright line"
assert sum(1 for x in range(430, 600) if min(logo(x, 340)) > 200) > 20, "the wordmark"

at = load("build/screen.ppm")
# mallory wrote 0xbad over the first two pixels of the menu bar; they match their neighbors
assert at(0, 0) == at(2, 0) == at(3, 0) and at(1, 0) == at(2, 0), ("menu bar", at(0, 0), at(2, 0))
assert min(at(500, 214)) > 220, ("title bar after the drag", at(500, 214))
# where the window was: the background pattern again, a dot at every 32 px brighter than
# the gradient between the dots
r, g, b = at(150, 150)
assert b > r + 40 and b > 90, ("background between the dots", (r, g, b))
for x, y in ((144, 144), (16, 48), (976, 560)):
    dot, between = at(x, y), at(x + 8, y + 8)
    assert sum(dot) > sum(between) + 40, ("pattern dot", (x, y), dot, between)
dark = sum(1 for y in range(292, 314) for x in range(292, 330) if max(at(x, y)) < 100)
assert dark > 20, ("typed text", dark)
assert max(at(376, 548)) > 120, ("the Notes icon in the dock", at(376, 548))
print("ok: the boot screen, the desktop, the dock, the typed note and the moved window are on screen; mallory's write never landed")
PY
