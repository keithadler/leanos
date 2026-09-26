#!/bin/bash
# Boots leanos on QEMU's Raspberry Pi 4 and checks what it did: the axioms every proof rests
# on, the serial transcript, and the pixels on the screen.
set -u
cd "$(dirname "$0")/.."
# this run's files (screens, cards): test/all.py gives each test its own folder
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"

fail() { echo "FAIL: $*"; exit 1; }

# Axioms: only Lean's standard three, and never sorryAx.
axioms=$(lake env lean test/Axioms.lean 2>&1) || fail "axiom check did not run: $axioms"
echo "$axioms" | grep -q sorryAx && fail "a theorem depends on sorry"
echo "$axioms" | grep -v "depends on axioms: \[\(propext\|Classical.choice\|Quot.sound\)\(, \(propext\|Classical.choice\|Quot.sound\)\)*\]" \
  | grep -v "does not depend on any axioms$" | grep -q . && fail "unexpected axiom: $axioms"
echo "ok: $(echo "$axioms" | wc -l | tr -d ' ') theorems rest only on Lean's standard axioms"

rm -f "$T/screen.ppm" "$T/screen.png" "$T/logo.ppm" "$T/logo.png" "$T/console.ppm" "$T/console.png"
# Boot, wait for the desktop to settle, type "Hi!" into the Notes window, wait for Notes to
# save it, drag the window by its title bar, then capture the screen (test/run.py, DEMO_STEPS).
out=$(python3 test/run.py 40 --demo)
status=$?
echo "$out" > "$T/serial.txt"            # where the window opened, for the pixel checks
echo "$out" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish the interaction (status $status)"

# All four cores come up and run tasks.
for c in 1 2 3; do echo "$out" | grep -q "^leanos: core $c up$" || fail "core $c did not come up"; done
echo "$out" | grep -q "^leanos: idle, .*tasks ran on 4 cores)$" || fail "tasks did not run on all four cores"
echo "ok: all four cores are up and every one of them ran tasks"

# Each task's lines must appear in this order; tasks may interleave with each other.
check_order() {
  local who=$1; shift
  local got
  got=$(echo "$out" | grep -E "^($who: |leanos: $who stopped)")
  local expected
  expected=$(printf '%s\n' "$@")
  [ "$got" = "$expected" ] || { echo "expected for $who:"; echo "$expected"; echo "got:"; echo "$got"; fail "$who"; }
}

check_order alice \
  "alice: wrote secret 0x5ec12e7 to my data page" \
  "alice: no saved note yet" \
  "alice: opened a 480x320 window, read-only, 150 pages -> ok" \
  "alice: saved note 1 (3 bytes)"

check_order fs \
  "fs: ready, 22 files on the SD card" \
  "fs: checked: 22 files in 1 folder, 6656 KiB free of 6968, journal 128 KiB"

check_order mallory \
  "mallory: I am task 2" \
  "mallory: map capability 9 (not mine) at page 5 -> refused, no such capability" \
  "mallory: print 16 bytes of kernel memory at 0x80000 -> refused, not allowed" \
  "mallory: receive on the display's endpoint -> refused, not allowed" \
  "mallory: send the display a window of my pixels -> refused, not allowed" \
  "mallory: map the framebuffer (capability 5, which is the display's) -> refused, no such capability" \
  "mallory: map the endpoint as memory -> refused, not allowed" \
  "mallory: asked for every right on the endpoint, got send" \
  "mallory: read block 0 of the SD card through capability 20, which I do not have -> refused, no such capability" \
  "mallory: read block 0 of the SD card through my endpoint capability -> refused, not allowed" \
  "mallory: ask the display for a window without pixels -> ok" \
  "mallory: ask the display for what was copied -> refused, it has no such request" \
  "mallory: put text on the clipboard without being asked -> refused" \
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
# The display's timing lines (checked below) are not part of its story.
timing=$(echo "$out" | grep -E "^display: (a full redraw took|a click on a window redrew in|the drag drew)")
display=$(echo "$out" | grep -E "^display: " | grep -vE "^display: (a full redraw took|a click on a window redrew in|the drag drew)")
expected_head=$(printf '%s\n' "display: boot checks shown: 6 verified, 0 refused" "display: boot logo drawn" \
  "display: desktop drawn on the 1024x600 framebuffer")
[ "$(echo "$display" | head -3)" = "$expected_head" ] || fail "display did not show the boot checks, logo and desktop"
for line in \
  "display: start Apps -> ok" \
  "display: alice opened a 480x320 window at 8,38 from a read-only capability to 150 pages" \
  "display: mallory sent a copy nobody asked for; refused"; do
  [ "$(echo "$display" | grep -cxF "$line")" = 1 ] || fail "display line missing or repeated: $line"
done
# mallory's window without pixels, and her request for the clipboard, which does not exist
[ "$(echo "$display" | grep -cxF "display: mallory sent a request it cannot make; ignored")" = 2 ] \
  || fail "the display did not refuse mallory's two requests it does not have"
# the drag (DEMO_STEPS in test/run.py) moves Notes 180 px right and 132 down, from the top
# left of the desktop, where the first window goes
expected_tail=$(printf '%s\n' "display: key 'H' to alice" "display: key 'i' to alice" "display: key '!' to alice" \
  "display: moved alice's window to (188, 170)")
[ "$(echo "$display" | tail -4)" = "$expected_tail" ] || fail "keys or drag not handled"
[ "$(echo "$display" | wc -l | tr -d ' ')" = 12 ] || fail "display printed unexpected lines"
# Startup items: the display starts Apps, which finds no startup.txt on this card and leaves.
echo "$out" | grep -q "^apps: opened a window" && fail "Apps opened a window with no startup.txt"
for who in alice display mallory carol input fs; do
  echo "$out" | grep -q "^leanos: $who verified, sha256 " || fail "$who was not verified at boot"
done

echo "$out" | grep -q "^leanos: framebuffer 1024x600 at 0x3c100000$" || fail "no framebuffer"
echo "$out" | grep -qx "leanos: SD card ready, data partition of 7 MiB" || fail "no SD card data partition"
echo "$out" | grep -q "^leanos: idle, 5 tasks waiting" || fail "did not settle with five tasks waiting"
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: boot transcript matches"

# The boot steps (arch/bootcon.c): each announced before it runs, its results after it, and
# nothing else of the kernel's in between; the last before any task runs.
# the hashes change with every build, and the card's power-up time with the host's load
boot_head=$(echo "$out" | sed -n '1,/^leanos: \[13\/13\]/p' | sed 's/sha256 0x[0-9a-f]*\.\.\.$/sha256 .../' \
  | sed 's/powered up after [0-9]* ms$/powered up after N ms/')
expected_boot=$(printf '%s\n' "leanos © 2026 Keith Adler" \
  "leanos: [1/13] serial console: PL011 on GPIO 14/15, 115200 8N1" \
  "leanos: Raspberry Pi 4, booting on EL1" \
  "leanos: [2/13] board: the firmware's mailbox; revisions, RAM, USB power" \
  "leanos: board revision 0xb03115, firmware 0x548e1" \
  "leanos: serial console: PL011, 115200 baud from a 3000000 Hz clock (the firmware's)" \
  "leanos: system counter: 62500000 Hz" \
  "leanos: RAM for the ARM: 0x0 to 0x3c000000" \
  "leanos: USB controller powered on" \
  "leanos: [3/13] Lean runtime: initializing the kernel's Lean code" \
  "leanos: [4/13] framebuffer: asking the firmware's mailbox for the screen" \
  "leanos: the firmware's framebuffer: 1024x600 (screen 1024x600), 32 bits, pitch 4096, BGR, alpha mode 2, 2457600 bytes at bus address 0x3c100000" \
  "leanos: framebuffer 1024x600 at 0x3c100000" \
  "leanos: [5/13] MMU: kernel page tables, then the caches" \
  "leanos: MMU on" \
  "leanos: [6/13] SD card: EMMC2, then EMMC; the partition table" \
  "leanos: SD: EMMC2: SDHCI 3.0, base clock 700000 kHz (the firmware's)" \
  "leanos: SD: EMMC2: I/O lines at 3.3 V" \
  "leanos: SD: EMMC2: identification clock 400 kHz" \
  "leanos: SD: EMMC2: no card answered CMD8 or ACMD41" \
  "leanos: SD: EMMC: SDHCI 3.0, base clock 50000 kHz (the firmware's)" \
  "leanos: SD: EMMC: identification clock 396 kHz" \
  "leanos: SD: EMMC: a standard-capacity card, powered up after N ms" \
  "leanos: SD: EMMC: ready, transfer clock 25000 kHz" \
  "leanos: SD card ready, data partition of 7 MiB" \
  "leanos: [7/13] Lean kernel: the first state, from the boot manifest" \
  "leanos: Lean kernel initialized, 18 tasks" \
  "leanos: [8/13] memory: clearing the task frames; SHA-256 self-test" \
  "leanos: [9/13] programs: loading each, checking it against the manifest" \
  "leanos: alice verified, sha256 ..." "leanos: display verified, sha256 ..." "leanos: mallory verified, sha256 ..." \
  "leanos: carol verified, sha256 ..." "leanos: input verified, sha256 ..." "leanos: fs verified, sha256 ..." \
  "leanos: usb verified, sha256 ..." \
  "leanos: [10/13] page tables: every task's address space" \
  "leanos: [11/13] interrupts: the GIC-400 and the 10 ms timer" \
  "leanos: [12/13] cores 1-3: releasing them from the spin table" \
  "leanos: [13/13] first task: the display server takes the screen")
[ "$boot_head" = "$expected_boot" ] || { echo "expected:"; echo "$expected_boot"; echo "got:"; echo "$boot_head"; fail "the boot steps"; }
[ "$(echo "$out" | grep -c "^leanos: \[")" = 13 ] || fail "a boot step printed twice"
echo "ok: the 13 boot steps are announced in order, each before it runs, the last before any task"

# Drawing speed: each timing is reported, and a drag frame stays well under the 35 ms it
# took before drawing was reworked (the bound is loose: QEMU shares this machine).
for what in "a full redraw took" "a click on a window redrew in" "the drag drew"; do
  echo "$timing" | grep -q "^display: $what" || fail "no timing for: $what"
done
frame_ms=$(echo "$timing" | sed -n 's/^display: the drag drew [0-9]* frames, \([0-9]*\)\..* ms each$/\1/p')
[ -n "$frame_ms" ] && [ "$frame_ms" -lt 20 ] || fail "a drag frame took $frame_ms ms"
echo "ok: drawing speed: $(echo "$timing" | sed 's/^display: //' | paste -sd ';' - | sed 's/;/; /g')"

# The screens themselves.
python3 - "$T" <<'PY' || fail "the screen is not what the display drew"
import os, sys
def load(path):
    data = open(path, "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    assert (w, h) == (1024, 600), (w, h)
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])

# The boot console (arch/bootcon.c), as the last boot step began: its title, the full
# progress bar, and a green "ok" beside each step already done.
con = load(os.path.join(sys.argv[1], "console.ppm"))
assert max(con(8, 590)) < 40, ("console background", con(8, 590))
assert sum(1 for y in range(26, 48) for x in range(40, 470) if min(con(x, y)) > 200) > 300, "console title"
assert all(con(x, 101)[1] > 150 and con(x, 101)[0] < 120 for x in (41, 512, 982)), "console progress bar"
oks = sum(1 for y in range(114, 600) for x in range(960, 986) if con(x, y)[1] > 150 and con(x, y)[0] < 120)
assert oks > 12 * 20, ("the ok marks", oks)
assert sum(1 for y in range(114, 600) for x in range(40, 900) if min(con(x, y)) > 200) > 3000, "console text"

logo = load(os.path.join(sys.argv[1], "logo.ppm"))
r, g, b = logo(566, 172)          # the logo tile, off the lambda: indigo to teal
assert b > r + 40 and b > 120, ("logo", (r, g, b))
assert logo(512, 434)[1] > 150, ("progress bar, full", logo(512, 434))
assert sum(1 for x in range(440, 590) if max(logo(x, 575)) > 80) > 20, "copyright line"
assert sum(1 for x in range(430, 600) if min(logo(x, 340)) > 200) > 20, "the wordmark"
green = lambda r, g, b: g > 150 and r < 120
for k in range(6):               # a green check beside every program on the boot screen
    y0 = 462 + k * 16
    assert sum(1 for y in range(y0, y0 + 14) for x in range(382, 396) if green(*logo(x, y))) > 30, ("check", k)

at = load(os.path.join(sys.argv[1], "screen.ppm"))
sys.path.insert(0, "test")
from run import window_pos, OPENED
log = open(os.path.join(sys.argv[1], "serial.txt")).read().splitlines()
ox, oy = next((int(m.group(4)), int(m.group(5))) for m in map(OPENED.match, log) if m and m.group(1) == "alice")
mx, my = window_pos(log, "alice")          # where the drag left it
# mallory wrote 0xbad over the first two pixels of the menu bar; they match their neighbors
assert at(0, 0) == at(2, 0) == at(3, 0) and at(1, 0) == at(2, 0), ("menu bar", at(0, 0), at(2, 0))
assert min(at(mx + 224, my + 6)) > 220, ("title bar after the drag", at(mx + 224, my + 6))
# where the window was: the background pattern again, a dot at every 32 px brighter than
# the gradient between the dots
assert not (mx <= ox + 54 < mx + 480), "the window did not move off where it was"
r, g, b = at(ox + 54, oy + 74)
assert b > r + 40 and b > 90, ("background between the dots", (r, g, b))
for x, y in ((144, 144), (16, 48), (976, 560)):
    dot, between = at(x, y), at(x + 8, y + 8)
    assert sum(dot) > sum(between) + 40, ("pattern dot", (x, y), dot, between)
# the note, right of the list (the window's title bar is 30 px), and its first line as its
# title in the list
dark = sum(1 for y in range(my + 42, my + 62) for x in range(mx + 160, mx + 200) if max(at(x, y)) < 100)
assert dark > 20, ("typed text", dark)
dark = sum(1 for y in range(my + 84, my + 106) for x in range(mx + 14, mx + 54) if max(at(x, y)) < 100)
assert dark > 20, ("the note's title in the list", dark)
assert max(at(215, 548)) > 120, ("the Notes icon in the dock", at(215, 548))
print("ok: the boot console, the boot screen, the desktop, the dock, the typed note and the moved window are on screen; mallory's write never landed")
PY
