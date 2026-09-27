#!/bin/bash
# view, the picture viewer, on a card of its own (tools/mksd.py) with pictures made here by
# tools/mksamples.py's writers: given.ppm in the top folder, and in view's folder, apps/view,
# every kind it reads and some it must refuse. Terminal runs `run view given.ppm`: view shows
# that file first, then N goes through its folder's pictures, in the order of their names.
#
#   a..h   small pictures, each shown at its own size in the middle of the window: 24-bit BMP
#          bottom-up (63 px wide, so its rows are padded) and top-down, 8-, 4- and 1-bit BMP
#          with a palette, 32-bit BMP with color masks in a V4 header, PPM (P6) and PGM (P5).
#          Each is four quadrants of known colors, with a white top-left pixel and a black
#          bottom-right one, so a picture upside down or mirrored does not pass.
#   i      1000 x 700, 24-bit (2 MB, read in pieces): fitted, 417 x 292, its quadrants are
#          their colors and a checkerboard of single pixels is gray (averaged, not sampled);
#          then 1 shows it 1:1 around its middle, the Right arrow moves across it, and the
#          quadrants' corner moves 125 px left; a click on it brings it back to the middle, and
#          the Fit button fits the picture again.
#   j..q   refused, each with its reason in the window and the log, and nothing else goes
#          wrong: a BMP cut short, one compressed (RLE8), 100000 x 100000 pixels, a pixel
#          offset past the end, text that is not a picture, a text PPM (P3), a PPM of 16-bit
#          samples, an empty file.
#   r, s   shown, though made to trip it: a 32-bit BMP whose color masks are all 32 bits (white),
#          and an 8-bit one whose right half's palette index, 200, is past its palette of 2
#          (black).
#
# Last, N wraps around to given.ppm, drawn again, and + zooms it to 150%: view is still there
# and still works.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
make -s build/progs/view.elf build/icons/view.icon || fail "view did not build"
pics=$T/view-pics
rm -rf "$pics" && mkdir -p "$pics"

python3 - "$pics" <<'PY' || fail "could not make the pictures"
import os, struct, sys
sys.path.insert(0, "tools")
from mksamples import bmp, ppm
out = sys.argv[1]
TL, TR, BL, BR, WHITE, BLACK = (220, 40, 40), (40, 200, 60), (40, 60, 220), (240, 220, 40), (255, 255, 255), (0, 0, 0)
def index(x, y, w, h):
    """The pattern, as a palette index: the quadrant, and the two marked corners."""
    if (x, y) == (0, 0):
        return 4
    if (x, y) == (w - 1, h - 1):
        return 5
    return (x >= w // 2) + 2 * (y >= h // 2)
PAL = [TL, TR, BL, BR, WHITE, BLACK]
def color(w, h):
    return lambda x, y: PAL[index(x, y, w, h)]
def write(name, data):
    open(os.path.join(out, name), "wb").write(data)
write("given.ppm", ppm(45, 33, color(45, 33)))
write("a-bottomup.bmp", bmp(63, 47, color(63, 47)))
write("b-topdown.bmp", bmp(50, 31, color(50, 31), topdown=True))
write("c-pal8.bmp", bmp(41, 27, lambda x, y: index(x, y, 41, 27), bpp=8, palette=PAL))
write("d-pal4.bmp", bmp(37, 25, lambda x, y: index(x, y, 37, 25), bpp=4, palette=PAL))
# 1 bit: two colors, the quadrants alternating
write("e-pal1.bmp", bmp(35, 23, lambda x, y: ((x >= 17) + (y >= 11)) % 2, bpp=1, palette=[TL, BL]))
write("f-v4-32.bmp", bmp(59, 39, color(59, 39), bpp=32, header=108))
write("g-p6.ppm", ppm(61, 43, color(61, 43)))
GRAYS = [40, 100, 170, 230, 255, 0]
write("h-p5.pgm", ppm(57, 41, lambda x, y: GRAYS[index(x, y, 57, 41)], gray=True))
# 1000 x 700: the quadrants, and in the bottom-right one a checkerboard of single pixels
def big(x, y):
    if x >= 750 and y >= 525:
        return WHITE if (x + y) % 2 else BLACK
    return PAL[(x >= 500) + 2 * (y >= 350)]
write("i-big.bmp", bmp(1000, 700, big))
good = bmp(640, 480, lambda x, y: TL)
write("j-cut.bmp", good[:1000])
rle = bytearray(bmp(16, 16, lambda x, y: 0, bpp=8, palette=PAL))
struct.pack_into("<I", rle, 30, 1)                      # compression: RLE8
write("k-rle.bmp", bytes(rle))
huge = bytearray(bmp(4, 4, lambda x, y: TL))
struct.pack_into("<ii", huge, 18, 100000, 100000)
write("l-huge.bmp", bytes(huge))
far = bytearray(bmp(10, 10, lambda x, y: TL))
struct.pack_into("<I", far, 10, 0xFFFFFFF0)             # the pixels, 4 GiB in
write("m-offset.bmp", bytes(far))
write("n-text.bmp", b"hello, this is not a picture\n")
write("o-p3.ppm", b"P3\n2 2\n255\n255 0 0  0 255 0\n0 0 255  255 255 0\n")
write("p-16bit.ppm", b"P6\n2 2\n65535\n" + bytes(24))
write("q-empty.bmp", b"")
# shown, but made to trip it: color masks of all 32 bits, and palette indexes past the palette
masks = bytearray(bmp(20, 10, lambda x, y: TL, bpp=32, header=108))
struct.pack_into("<III", masks, 54, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF)
write("r-masks.bmp", bytes(masks))
write("s-index.bmp", bmp(30, 20, lambda x, y: 0 if x < 15 else 200, bpp=8, palette=[TL, TR]))
PY

card=$T/sd-view.img
python3 tools/mksd.py "$card" view=build/progs/view.elf view.icon=build/icons/view.icon given.ppm="$pics/given.ppm" \
  $(cd "$pics" && for f in [a-s]-*; do echo "apps/view/$f=$pics/$f"; done) >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, snap, pause, DOCK, TITLE_H
card = sys.argv[1]
VW, AH = 500, 292
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
GOOD = ["a-bottomup.bmp", "b-topdown.bmp", "c-pal8.bmp", "d-pal4.bmp", "e-pal1.bmp", "f-v4-32.bmp", "g-p6.ppm",
        "h-p5.pgm"]
BAD = ["j-cut.bmp", "k-rle.bmp", "l-huge.bmp", "m-offset.bmp", "n-text.bmp", "o-p3.ppm", "p-16bit.ppm", "q-empty.bmp"]
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys("run view given.ppm\r"), wait_for("view: drew given.ppm"), pause(0.3), snap("view-given")]
for name in GOOD:
    steps += [b"n", wait_for("view: drew " + name), pause(0.3), snap("view-" + name.split(".")[0])]
steps += [b"n", wait_for("view: drew i-big.bmp at "), pause(0.3), snap("view-i-fit"),
          b"1", wait_for("view: drew i-big.bmp at 100%"), pause(0.3), snap("view-i-one"),
          b"\x1b[C", wait_for("view: drew i-big.bmp at 100%", 2), pause(0.3), snap("view-i-right"),
          *wclick("view", 125, TITLE_H + 146), wait_for("view: drew i-big.bmp at 100%", 3), pause(0.3),
          snap("view-i-click"),
          *wclick("view", VW - 132 + 18, TITLE_H + AH + 14), wait_for("view: drew i-big.bmp at 42% (fit)", 2)]
for name in BAD:
    steps += [b"n", wait_for("view: cannot show apps/view/" + name), pause(0.5), snap("view-" + name.split(".")[0])]
steps += [b"n", wait_for("view: drew r-masks.bmp"), pause(0.3), snap("view-r-masks"),
          b"n", wait_for("view: drew s-index.bmp"), pause(0.3), snap("view-s-index")]
steps += [b"n", wait_for("view: drew given.ppm", 2), pause(0.3), snap("view-again"), b"+"]
sys.exit(boot(180, sd=card, steps=steps, until="view: drew given.ppm at 150%", settle=0.3))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(view: |terminal: (run|gave)|display: view)" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
# (carol and mallory, the kernel's own test tasks, are stopped at boot on purpose)
echo "$out" | grep -E "^leanos: .* stopped: " | grep -qvE "^leanos: (carol|mallory) stopped: " && fail "a program stopped on a fault"
echo "$out" | grep -qx "view: 1 file given, 19 pictures in apps/view" || fail "view did not find its file and folder"

python3 - "$T" <<'PY' || fail "view showed the wrong thing"
import os, re, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
T = sys.argv[1]
log = open(os.path.join(T, "serial.txt")).read()
VW, AH = 500, 292
wx, wy = window_pos(log, "view")
def load(name):
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    def at(x, y):
        i = ((wy + TITLE_H + y) * w + wx + x) * 3
        return tuple(px[i:i + 3])
    return at
TL, TR, BL, BR, WHITE, BLACK = (220, 40, 40), (40, 200, 60), (40, 60, 220), (240, 220, 40), (255, 255, 255), (0, 0, 0)
BG = (30, 31, 36)
def small(snapname, w, h, colors, corners=True):
    """A picture of w x h at its own size in the middle: each quadrant's middle, its corners."""
    at = load(snapname)
    ix, iy = (VW - w) // 2, (AH - h) // 2
    qs = [(w // 4, h // 4), (w // 2 + w // 4, h // 4), (w // 4, h // 2 + h // 4), (w // 2 + w // 4, h // 2 + h // 4)]
    got = [at(ix + x, iy + y) for x, y in qs]
    assert got == colors, (snapname, "quadrants", got, "expected", colors)
    if corners:
        assert at(ix, iy) == WHITE and at(ix + w - 1, iy + h - 1) == BLACK, (snapname, "corners", at(ix, iy), at(ix + w - 1, iy + h - 1))
    assert at(ix - 1, iy + h // 4) == BG and at(ix + w, iy + h // 4) == BG, (snapname, "the picture is not where it should be")
    assert at(ix + w // 4, iy - 1) == BG and at(ix + w // 4, iy + h) == BG, (snapname, "the picture is not where it should be")
Q = [TL, TR, BL, BR]
small("view-given", 45, 33, Q)
small("view-a-bottomup", 63, 47, Q)
small("view-b-topdown", 50, 31, Q)
small("view-c-pal8", 41, 27, Q)
small("view-d-pal4", 37, 25, Q)
small("view-e-pal1", 35, 23, [TL, BL, BL, TL], corners=False)
small("view-f-v4-32", 59, 39, Q)
small("view-g-p6", 61, 43, Q)
G = [(g, g, g) for g in (40, 100, 170, 230)]
small("view-h-p5", 57, 41, G)
small("view-again", 45, 33, Q)
small("view-r-masks", 20, 10, [WHITE] * 4, corners=False)
small("view-s-index", 30, 20, [TL, BLACK, TL, BLACK], corners=False)

# the big one, fitted: 417 x 292 from x 41; the quadrants' middles, and the checkerboard gray
for name, fmt in (("a-bottomup.bmp", "BMP 24-bit"), ("b-topdown.bmp", "BMP 24-bit, top-down"),
                  ("c-pal8.bmp", "BMP 8-bit"), ("d-pal4.bmp", "BMP 4-bit"), ("e-pal1.bmp", "BMP 1-bit"),
                  ("f-v4-32.bmp", "BMP 32-bit"), ("g-p6.ppm", "PPM"), ("h-p5.pgm", "PGM"), ("i-big.bmp", "BMP 24-bit")):
    assert re.search(rf"^view: opened apps/view/{re.escape(name)}: \d+x\d+, {re.escape(fmt)}$", log, re.M), (name, fmt)
m = re.search(r"^view: drew i-big.bmp at (\d+)% \(fit\), (\d+)x(\d+) on the screen, in (\d+) ms from (\d+) reads \((\d+) ms of it reading\)$", log, re.M)
assert m and m.group(2, 3) == ("417", "292"), ("the big picture was not fitted to 417 x 292", m and m.group(0))
fit_ms, fit_reads, fit_reading = int(m.group(4)), int(m.group(5)), int(m.group(6))
at = load("view-i-fit")
ix = (VW - 417) // 2
for (fx, fy), c in (((0.25, 0.25), TL), ((0.75, 0.2), TR), ((0.25, 0.75), BL), ((0.6, 0.6), BR)):
    got = at(ix + int(417 * fx), int(292 * fy))
    assert got == c, ("fitted", fx, fy, got, c)
gray = at(ix + int(417 * 0.875), int(292 * 0.875))
assert all(100 <= g <= 160 for g in gray) and max(gray) - min(gray) <= 2, ("the checkerboard is not averaged to gray", gray)
assert at(ix - 1, 100) == BG and at(ix + 417, 100) == BG, "the fitted picture is not in the middle"
# 1:1 around the middle: the quadrants meet at the window's middle (250, 146)
at = load("view-i-one")
for (x, y), c in (((200, 100), TL), ((300, 100), TR), ((200, 200), BL), ((300, 200), BR)):
    assert at(x, y) == c, ("1:1", x, y, at(x, y), c)
assert at(249, 145) == TL and at(250, 145) == TR and at(249, 146) == BL, ("1:1: the middle is not the picture's", at(249, 145), at(250, 145))
# the Right arrow: a quarter of the window, 125 px: the corner at x 125
at = load("view-i-right")
assert at(124, 100) == TL and at(125, 100) == TR and at(124, 200) == BL and at(125, 200) == BR, \
    ("after the Right arrow", at(124, 100), at(125, 100))
# a click on that corner brings it to the middle again
at = load("view-i-click")
assert at(249, 145) == TL and at(250, 145) == TR and at(249, 146) == BL, ("after the click", at(249, 145), at(250, 145))

# the refused ones: the reason in the log, a heading in the window, no picture
reasons = {"j-cut.bmp": "the file ends before its pixels do", "k-rle.bmp": "a compressed BMP (RLE8)",
           "l-huge.bmp": "100000 x 100000 pixels is too large: view takes pictures up to 16384 x 16384",
           "m-offset.bmp": "the file ends before its pixels do", "n-text.bmp": "not a picture view knows",
           "o-p3.ppm": "a PNM written as text", "p-16bit.ppm": "samples up to 65535", "q-empty.bmp": "the file is empty"}
for name, why in reasons.items():
    line = next((l for l in log.splitlines() if l.startswith("view: cannot show apps/view/" + name + ": ")), None)
    assert line and why in line, (name, line)
    at = load("view-" + name.split(".")[0])
    bright = sum(1 for y in range(AH // 2 - 32, AH // 2 - 10) for x in range(28, 300) if min(at(x, y)) > 200)
    assert bright > 30, (name, "no heading in the window", bright)
    assert at(VW - 20, 20) == BG and at(VW // 2, AH - 20) == BG, (name, "something else in the window")
print(f"ok: 9 kinds of picture shown where and as they should be; 1000 x 700 fitted in {fit_ms} ms from "
      f"{fit_reads} reads ({fit_reading} ms of it reading), the checkerboard gray {gray}; 1:1, the Right arrow, "
      f"a click and the Fit button; "
      f"8 refused with their reasons, 2 made to trip it shown safely")
PY
echo "ok: view shows BMP, PPM and PGM at their size, fitted and 1:1, and refuses what it cannot read without harm"
