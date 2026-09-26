#!/bin/bash
# The display server under fire: dfuzz (user/progs/dfuzz.c), on a card of its own under the
# names dfuzz, dfuzz2, dfuzzx, dfuzzf and dfuzzc, run from Terminal into the open slots, where
# a program reaches only the display server (endpoint 0), its own memory and its folder.
#
# The display owns the framebuffer and composites every window from memory apps grant it. It
# is trusted user-space code that cannot be restarted: a crash freezes the machine. So it
# must answer every message, whatever its op, words and grant hold, with an answer the
# protocol (user/app.h) allows, never stop or hang, never draw a program's pixels or words
# where the stacking rules do not put them, and keep nothing it was not meant to.
#
#   1. Notes closed and Terminal dragged right. dfuzz, first, opens a window one pixel wide
#      with a wide title; screenshots before and after show what it drew.
#   2. dfuzz and dfuzz2, side by side in slots 10 and 11: fixed adversarial requests (every
#      op, bad sizes, too few and too many pages, the code run, no grant, bad icons, SETs,
#      STARTs, RAISEs and PENDINGs a card program may not make, ZONE, COPY unasked, grants by
#      plain send, unknown ops), without a window and with one; requests made near the
#      limits, checked against the display's rule; floods; random requests; RAISEs of their
#      own names; windows until the table is full. A screenshot with every window up.
#   3. dfuzz killed while it waits on its window, run again to its end, run again and killed
#      in the middle of its random requests; dfuzzx exits and dfuzzf faults, each just after
#      grants sent by plain send. All in slot 10, beside dfuzz2: the kernel heap after each
#      of these starts must be the same.
#   4. dfuzz2 killed. dfuzzc, one window: Ctrl+C answered with more than the clipboard holds,
#      Ctrl+V, Ctrl+C answered late, its close button, then a copy nobody asked for.
#   5. Settings opens (the display let every window of the stopped programs go) and Terminal
#      writes a file. A screenshot at the end.
#
# Every answer must be the one the protocol allows (no WRONG line); nothing may panic or stop
# but dfuzzf; the display's log must say a few lines of each flood, not all of them; the menu
# bar and the dock's icons must be the same with every fuzzer window up as at the end; the
# narrow window must draw nothing past its frame and shadow. The seed is printed:
# DFUZZ_SEED=N test/dfuzz.sh runs it again (DFUZZ_COUNT=N: random requests each).
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/dfuzz.elf || fail "dfuzz did not build"
seed=${DFUZZ_SEED:-$(( (RANDOM << 15 | RANDOM) + 1 ))}
count=${DFUZZ_COUNT:-1500}
echo "seed $seed (DFUZZ_SEED=$seed test/dfuzz.sh runs this again), $count random requests each"
card=$T/sd-dfuzz.img
p=build/progs/dfuzz.elf
python3 tools/mksd.py "$card" dfuzz=$p dfuzz2=$p dfuzzx=$p dfuzzf=$p dfuzzc=$p >/dev/null || fail "no card"

out=$(python3 - "$card" "$seed" "$count" <<'PY'
import sys
from collections import Counter
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, snap, pause, wmouse, wclick, CLOSE, DOCK
card, seed, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rerun = max(1, count // 4)
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [s.encode()]           # a whole command at once
front = click(*DOCK["Terminal"])        # a program's new window takes focus: give it back to Terminal
NAMES = ["dfuzz", "dfuzz2"]
seen = Counter()
def cmd(line, done):
    seen[done] += 1                     # the same command again waits for its next line
    return [*keys(line + "\r"), wait_for(done, seen[done])]
# Notes closed, and Terminal dragged 540 px to the right, from the top left where the first
# window goes: the left of the screen is clear for dfuzz's first window, one pixel wide
steps = [*wclick("alice", *CLOSE), wait_for("alice: window closed"),
         *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         wmouse("d", "Terminal", 164, 12), wmouse("v", "Terminal", 164 + 270, 12),
         wmouse("v", "Terminal", 164 + 540, 12), wmouse("u", "Terminal", 164 + 540, 12),
         wait_for("display: moved Terminal's window"),
         *cmd("mkdir apps", "terminal: mkdir apps ")]
for k, name in enumerate(NAMES):
    steps += cmd(f"mkdir apps/{name}", f"terminal: mkdir apps/{name} ")
    steps += cmd(f"write apps/{name}/seed {seed + k} {count}{' n' if k == 0 else ''}", f"terminal: write apps/{name}/seed")
# start each into an open slot, refocusing Terminal first (a new window takes the focus); the
# next is typed after the last has its first window, and while it pauses before it opens more
for k, name in enumerate(NAMES):
    steps += [*front, *cmd(f"run {name}", f"terminal: run {name} -> slot")]
    if k == 0:
        steps += [wait_for("dfuzz: dfuzz in slot 10: about to open a narrow window"), pause(0.3), snap("before-narrow"),
                  wait_for("dfuzz: dfuzz in slot 10: a narrow window is up"), pause(0.3), snap("narrow")]
    steps += [wait_for(f"dfuzz: {name} in slot {10 + k}: with a window")]
for k, name in enumerate(NAMES):
    steps += [wait_for(f"dfuzz: {name} in slot {10 + k}: all done")]
steps += [snap("fuzzed")]              # every window the fuzzers opened, still up
# dfuzz killed while it waits on its window (the display holds the call), and run again in
# its slot twice more, beside dfuzz2 as it was
for again in (1, 2):
    steps += [*front, *cmd("kill 10", "terminal: kill 10"),
              *cmd(f"write apps/dfuzz/seed {seed + 10 * again} {rerun}", "terminal: write apps/dfuzz/seed"),
              *front, *cmd("run dfuzz", "terminal: run dfuzz -> slot")]
    # the first run again to its end; the second killed in the middle of its random requests
    steps += [wait_for("dfuzz: dfuzz in slot 10: all done", 2)] if again == 1 else \
             [wait_for("dfuzz: dfuzz in slot 10: random requests start", 3), *front, *cmd("kill 10", "terminal: kill 10")]
# then in the same slot a dfuzz that exits, and one that faults, each just after grants sent
# by plain send; the heap after each start must be as after the others
steps += [*front, *cmd("run dfuzzx", "terminal: run dfuzzx -> slot 10"), wait_for("dfuzz: dfuzzx in slot 10: exiting"), pause(0.3),
          *front, *cmd("run dfuzzf", "terminal: run dfuzzf -> slot 10"),
          wait_for("leanos: slot 10 stopped: data access not allowed")]
# then dfuzz2 killed
steps += [*front, *cmd("kill 11", "terminal: kill 11")]
# dfuzzc, one window, alone: Ctrl+C (answered with more than the clipboard holds), Ctrl+V,
# Ctrl+C again (answered late), then its close button (a copy after it)
C = "dfuzz: dfuzzc in slot 10: "
SD = "a program from the SD card"      # dfuzzc's window: it lends no name, so the display's log calls it this
steps += [*front, *cmd("run dfuzzc", "terminal: run dfuzzc -> slot 10"), wait_for(C + "copy and paste: window 1"),
          b"\x03", wait_for(C + "copy: sent"), b"\x16", wait_for(C + "paste: got"),
          b"\x03", wait_for(C + "copy: a late answer"), *wclick(SD, *CLOSE), wait_for(C + "closed; all done")]
steps += [*click(*DOCK["Settings"]), wait_for("settings: opened"),
          *front, *cmd("write after.txt still here", "terminal: write after.txt")]
sys.exit(boot(150, steps=steps, until="terminal: write after.txt", sd=card, settle=1))
PY
)
status=$?
echo "$out" > "$T/serial.txt"                # the whole transcript, for a failure
echo "$out" | grep -E "^(dfuzz: |terminal: (run|write|kill|mkdir apps/)|settings: opened|leanos: (slot 1. stopped|PANIC)|display: (a program from the SD card (sent|keeps|may not|stopped)|dfuzz2? is already))" \
  | grep -v "requests so far" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status): the display froze or stopped?"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
bad=$(echo "$out" | grep -E "^leanos: ([a-z]+|slot 1[0-5]) stopped" | grep -vE "^leanos: (mallory|carol) stopped" \
  | grep -vx "leanos: slot 10 stopped: data access not allowed at 0x80000000" | head -1)
[ -z "$bad" ] || fail "a server or program stopped: $bad"

# Every dfuzz finished, and every answer was one the protocol allows.
echo "$out" | grep -q "WRONG" && fail "a wrong answer: $(echo "$out" | grep WRONG | head -1)"
[ "$(echo "$out" | grep -c "^dfuzz: dfuzz in slot 10: all done: [0-9]* requests, 0 wrong$")" = 2 ] \
  || fail "dfuzz did not finish clean twice: $(echo "$out" | grep "^dfuzz: dfuzz in slot 10: all done")"
echo "$out" | grep -q "^dfuzz: dfuzzx in slot 10: exiting after [0-9]* requests, 0 wrong so far$" || fail "dfuzzx did not exit clean"
echo "$out" | grep -q "^dfuzz: dfuzzf in slot 10: faulting after [0-9]* requests, 0 wrong so far$" || fail "dfuzzf did not get to its fault"
[ "$(echo "$out" | grep -c "^leanos: slot 10 stopped: data access not allowed at 0x80000000$")" = 1 ] || fail "dfuzzf did not fault"
# Copy and paste by the user's hand, in dfuzzc's window: the calls past 4096 bytes refused
# (300 calls of 16 bytes, 256 taken), the paste exactly what was taken, a late answer and a
# copy after the window closed refused.
C="dfuzz: dfuzzc in slot 10: "
has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
has "${C}copy: sent 4800 bytes; the calls past 4096 refused: 44"
has "display: copied 4096 bytes from a program from the SD card"
has "display: paste: 4096 bytes to a program from the SD card"
has "${C}paste: got 4096 bytes, as copied"
has "${C}copy: a late answer refused"
echo "$out" | grep -q "^${C}closed; all done: [0-9]* requests, 0 wrong$" || fail "dfuzzc: $(echo "$out" | grep "^${C}closed")"
echo "$out" | grep -q "^dfuzz: dfuzz2 in slot 11: all done: [0-9]* requests, 0 wrong$" \
  || fail "dfuzz2 did not finish clean: $(echo "$out" | grep "^dfuzz: dfuzz2 in slot 11: all done")"
# requests made near the limits got windows where the rule allows them, until the table was
# full. (A display that kept grants it does not use would fill its 64 capabilities, and every
# later grant would come back from the kernel as full: a wrong answer, above.)
echo "$out" | grep -q "^dfuzz: dfuzz in slot 10: near the limits: windows taken [1-9][0-9]*, checked$" \
  || fail "no window made near the limits was taken"
echo "$out" | grep -q "^dfuzz: dfuzz in slot 10: opened [0-9]* windows, then the display refused one$" \
  || fail "the display never refused a window"

# The display quieted every flood: each program's refused windows and raises of its own name
# (thousands between them) log 3 lines at most, as do its requests it cannot make and SETs (3)
# and its copies nobody asked for (3). A line holds the kernel while the serial port takes it.
said=$(echo "$out" | grep -c "^display: \(a program from the SD card sent a window that does not fit\|dfuzz2\? is already open\)")
[ "$said" -le 6 ] || fail "refused windows and raises reached the log: $said lines"
[ "$(echo "$out" | grep -c "^display: a program from the SD card \(sent a request\|keeps\|may not\)")" -le 6 ] \
  || fail "requests it cannot make reached the log"
[ "$(echo "$out" | grep -c "^display: a program from the SD card sent a copy nobody")" -le 6 ] \
  || fail "refused copies reached the log"
[ "$(echo "$out" | grep -c "^terminal: kill 1[01] -> stopped$")" = 4 ] || fail "the fuzzers were not killed"

# The kernel heap after the second to fifth start of slot 10, dfuzz2 running beside each as
# it was: after a whole run killed while it waited on the display, after one killed in the
# middle, after one that exited: the same, give or take the display's reply slots (a display
# that kept anything per request, or per run, would grow it).
heap=$(echo "$out" | sed -n 's/^leanos: kernel heap \([0-9]*\) bytes live, [0-9]* peak, after starting slot 10$/\1/p')
[ "$(echo "$heap" | wc -l | tr -d ' ')" = 6 ] || fail "expected six starts of slot 10"
runs=$(echo "$heap" | sed -n '2,5p')       # the sixth (dfuzzc) comes after dfuzz2 is gone
h2=$(echo "$runs" | sort -n | head -1); h3=$(echo "$runs" | sort -n | tail -1)
[ $((h3 - h2)) -le 1024 ] || fail "the kernel heap after a start of slot 10 ranged from $h2 to $h3 bytes: $(echo $runs)"

# The display and the file server still work at the end.
echo "$out" | grep -q "^settings: opened" || fail "the display did not open a window after the fuzzers"
echo "$out" | grep -q "^terminal: write after.txt -> ok" || fail "the file server stopped answering"

# The screenshots: the desktop is drawn at the end (not blank, not garbage), what no window
# may cover is untouched, and the narrow window stayed in its frame.
python3 - "$T" <<'PYS' || fail "the screen at the end is not a live desktop"
import os, sys
data = open(os.path.join(sys.argv[1], "screen.ppm"), "rb").read()
_, dims, _, px = data.split(b"\n", 3)
w, h = map(int, dims.split())
at = lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
# the menu bar (top 30 px) has light text on a dark bar: some bright pixels, not blank
bar_bright = sum(1 for x in range(0, w) for y in range(0, 30) if min(at(x, y)) > 180)
assert bar_bright > 40, ("the menu bar is blank or garbage", bar_bright)
# the dock sits at the bottom center: its rounded panel is drawn there
dock_px = sum(1 for x in range(360, 660) for y in range(540, 590) if 20 < max(at(x, y)) < 200)
assert dock_px > 200, ("the dock is missing", dock_px)
# What no window may ever cover must be the same, pixel for pixel, with every window the
# fuzzers opened still up as at the end with them gone: the menu bar right of the focused
# window's name (windows stay below it, as a drag keeps them), and the dock's own icons (drawn
# over every window).
fz = open(os.path.join(sys.argv[1], "fuzzed.ppm"), "rb").read().split(b"\n", 3)[3]
def changed(x0, y0, x1, y1):
    return sum(1 for y in range(y0, y1) for x in range(x0, x1)
               if fz[(y * w + x) * 3:(y * w + x) * 3 + 3] != px[(y * w + x) * 3:(y * w + x) * 3 + 3])
bar = changed(400, 0, 1024, 30)
assert bar == 0, ("a window was drawn over the menu bar", bar)
# (the dock's panel is translucent, and so are parts of its icons: a window may show through
# them, as a window dragged down does. Its icons' opaque pixels, from the display's assets
# (tools/mkassets.py), are drawn over every window: at x 189 + 66 i, y 522, 52 px square.)
import struct
blob = open("build/assets/display.bin", "rb").read()
opaque = []
for n in range(struct.unpack_from("<I", blob, 8)[0]):
    kind, ident, off, _ = struct.unpack_from("<IIII", blob, 12 + 16 * n)
    if kind == 2 and 10 <= ident < 20:
        size = struct.unpack_from("<I", blob, off)[0]
        for j in range(size):
            for i in range(size):
                if struct.unpack_from("<I", blob, off + 8 + 4 * (j * size + i))[0] >> 24 == 255:
                    opaque.append((189 + 66 * (ident - 10) + i, 522 + j))
assert len(opaque) > 10000, ("the dock's icons were not found in the assets", len(opaque))
icons = sum(1 for x, y in opaque if fz[(y * w + x) * 3:(y * w + x) * 3 + 3] != px[(y * w + x) * 3:(y * w + x) * 3 + 3])
assert icons == 0, ("a window was drawn over the dock's icons", icons)
# A window one pixel wide, with a wide title, drew only inside its frame and its shadow: on
# the clear left of the screen (below the menu bar, above the dock) nothing else changed.
def load(name):
    return open(os.path.join(sys.argv[1], name + ".ppm"), "rb").read().split(b"\n", 3)[3]
a, b = load("before-narrow"), load("narrow")
box = [(x, y) for y in range(40, 500) for x in range(0, 500)
       if a[(y * w + x) * 3:(y * w + x) * 3 + 3] != b[(y * w + x) * 3:(y * w + x) * 3 + 3]]
assert box, "the narrow window was not drawn"
bw = max(x for x, _ in box) - min(x for x, _ in box) + 1
assert bw <= 1 + 2 * 12, ("the narrow window drew outside its frame", bw, min(box), max(box))
# the far bottom-left corner is background (no window reaches below the dock's top, and the
# dock is centered): it must be a colour, not black or white noise
corner = at(8, 560)
assert 8 < max(corner) < 240, ("the corner is not the desktop background", corner)
print(f"ok: a window one pixel wide changed a strip {bw} px wide; the desktop is drawn ({bar_bright} bright menu-bar pixels, {dock_px} dock pixels, corner {corner}); "
      f"the menu bar and the dock's icons are the same with the fuzzers' windows up as at the end")
PYS

total=$(echo "$out" | sed -n 's/^dfuzz: .* \([0-9]*\) requests, 0 wrong.*/\1/p' | awk '{ n += $1 } END { print n }')
echo "ok: $total requests from dfuzz (five runs in one slot, killed, exiting and faulting), dfuzz2 and dfuzzc (copy and paste) at the display, every answer as the protocol allows (seed $seed); kernel heap $h2 to $h3 bytes after each restart of slot 10; the display and file server still work, the desktop still drawn"
