#!/bin/bash
# paint, from the card. Terminal runs it with no file: it works on apps/paint/untitled.bmp,
# new. Scripted drags draw a red line 3 pixels wide, a blue filled rectangle, a black
# rectangle's outline, a filled orange ellipse and a green ellipse's outline; a click with
# the fill tool fills the black rectangle's inside yellow; a purple brush stroke is undone
# (Ctrl+Z), redone (Ctrl+Y) and undone again; a line that leaves the window on its left
# still draws up to the edge (the display gives the window the whole drag); Ctrl+S saves.
# The BMP is then read off the card image in Python: its header fields, its size, and the
# pixels where each thing was drawn (and white where the undone stroke was). A second boot
# opens the saved picture again and shows it.
#
# Then, on a card of its own: `run paint pic.bmp` opens a 100 x 60 top-down BMP made here, a
# click with the pencil changes one pixel, and the picture saves itself: still 100 x 60
# (bottom-up now), every other pixel as it was. And `run paint noise.bmp`, 416 x 208 of
# random bytes, where no tile packs: 16 lines fill undo's memory (the oldest go), clearing
# the picture keeps all of it (all but the last line go), and undo, redo, redo and undo
# again bring back the lines on the noise, pixel for pixel. No save.part~ is left behind.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

card=$T/sd-paint.img
cp build/sd-template.img "$card" || fail "no card"
pic=$T/paint-pic.bmp
card2=$T/sd-paint-pic.img
python3 - "$pic" <<'PY' || fail "could not make pic.bmp"
import struct, sys
w, h = 100, 60
stride = (w * 3 + 3) & ~3
rows = b""
for y in range(h):                       # top-down: the first row is the top one
    row = b"".join(bytes(((x * 2) & 255, (y * 4) & 255, (x + y) & 255)) for x in range(w))  # b, g, r
    rows += row + b"\0" * (stride - len(row))
head = b"BM" + struct.pack("<IHHI", 54 + len(rows), 0, 0, 54)
head += struct.pack("<IiiHHIIiiII", 40, w, -h, 1, 24, 0, len(rows), 2835, 2835, 0, 0)
open(sys.argv[1], "wb").write(head + rows)
PY
noise=$T/paint-noise.bmp
python3 - "$noise" <<'PY' || fail "could not make noise.bmp"
import struct, sys
w, h, seed = 416, 208, 1
rows = bytearray()
for i in range(w * h * 3):               # bottom-up, as paint writes them; 1248 bytes a row, no padding
    seed = (seed * 1103515245 + 12345) & 0x7fffffff
    rows.append(seed >> 16 & 255)
head = b"BM" + struct.pack("<IHHI", 54 + len(rows), 0, 0, 54)
head += struct.pack("<IiiHHIIiiII", 40, w, h, 1, 24, 0, len(rows), 2835, 2835, 0, 0)
open(sys.argv[1], "wb").write(head + rows)
PY
python3 tools/mksd.py "$card2" paint=build/progs/paint.elf paint.icon=build/icons/paint.icon pic.bmp="$pic" \
  noise.bmp="$noise" >/dev/null || fail "no card for pic.bmp"

out=$(python3 - "$card" "$card2" <<'PY'
import sys
sys.path.insert(0, "test")
import os, shutil
from run import boot, mouse, wmouse, wclick, wait_for, snap, window_pos, DOCK, TITLE_H, SCRATCH
card, card2 = sys.argv[1], sys.argv[2]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
CY = TITLE_H + 36                        # the canvas, in the window: under the title and the tool bar
at = lambda kind, x, y: wmouse(kind, "paint", x, CY + y)
def drag(x0, y0, x1, y1):
    mid = ((x0 + x1) // 2, (y0 + y1) // 2)
    return [at("d", x0, y0), at("v", *mid), at("v", x1, y1), at("u", x1, y1)]
def color(i):                            # a swatch of the palette, under the canvas
    return wclick("paint", 50 + 18 * (i % 8) + 8, TITLE_H + 244 + 6 + 18 * (i // 8) + 8)
RED, BLUE, BLACK, ORANGE, GREEN, YELLOW, PURPLE = 4, 12, 0, 6, 8, 7, 13
NOISE_LINES = [16 * r + 8 for r in range(13)] + [16 * r + 4 for r in range(3)]   # each in one row of tiles
start = [*click(*DOCK["Terminal"]), wait_for("terminal: opened")]
steps = start + [*keys("run paint\r"), wait_for("paint: opened a window"),
         *keys("l"), *color(RED), *drag(20, 20, 200, 20), wait_for("paint: line,"),
         *keys("R"), *color(BLUE), *drag(40, 50, 120, 100), wait_for("paint: filled rectangle,"),
         *keys("r"), *color(BLACK), *drag(200, 60, 300, 140), wait_for("paint: rectangle,"),
         *keys("O"), *color(ORANGE), *drag(320, 20, 400, 60), wait_for("paint: filled ellipse,"),
         *keys("o"), *color(GREEN), *drag(20, 130, 120, 190), wait_for("paint: ellipse,"),
         *keys("f"), *color(YELLOW), at("d", 250, 100), at("u", 250, 100), wait_for("paint: fill,"),
         *keys("b"), *color(PURPLE), *drag(330, 150, 400, 190), wait_for("paint: brush,"),
         b"\x1a", wait_for("paint: undid the brush"), b"\x19", wait_for("paint: redid the brush"),
         b"\x1a", wait_for("paint: undid the brush", 2),
         *keys("l"), *color(BLACK), at("d", 60, 200), wmouse("v", "paint", -40, CY + 200),
         wmouse("u", "paint", -40, CY + 200), wait_for("paint: line,", 2),
         snap("paint-drawn"), b"\x13", wait_for("paint: saved")]
boot(120, steps=steps, until="paint: saved", sd=card)
print("-- again")
steps = start + [*keys("run paint\r")]
lines = []
boot(90, steps=steps, until="paint: opened a window", settle=1, sd=card, on_line=lambda l: (lines.append(l), print(l)))
shutil.copyfile(os.path.join(SCRATCH, "screen.ppm"), os.path.join(SCRATCH, "paint-again.ppm"))
magic, dims, _, screen = open(os.path.join(SCRATCH, "screen.ppm"), "rb").read().split(b"\n", 3)
sw = int(dims.split()[0])
wx, wy = window_pos(lines, "paint")
shown = lambda x, y: screen[3 * ((wy + CY + y) * sw + wx + x):3 * ((wy + CY + y) * sw + wx + x) + 3].hex()
seen = [shown(110, 20), shown(80, 75), shown(250, 100), shown(10, 100)]
print("check: shown again:", "ok" if seen == ["ed1c24", "3f48cc", "fff200", "ffffff"] else seen)
print("-- given pic.bmp")
steps = start + [*keys("run paint pic.bmp\r"), wait_for("paint: opened a window"),
                 *keys("p"), *color(RED), at("d", 50, 30), at("u", 50, 30), wait_for("paint: pencil,")]
boot(90, steps=steps, until="paint: saved", sd=card2)
print("-- given noise.bmp")
steps = start + [*keys("run paint noise.bmp\r"), wait_for("paint: opened a window"), *keys("l"), *color(BLACK)]
for k, y in enumerate(NOISE_LINES):
    steps += [at("d", 0, y), at("v", 200, y), at("v", 415, y), at("u", 415, y), wait_for("paint: line,", k + 1)]
steps += [b"\x7f", wait_for("paint: clear,"), b"\x1a", wait_for("paint: undid the clear"),
          b"\x1a", wait_for("paint: undid the line"), b"\x19", wait_for("paint: redid the line"),
          b"\x19", wait_for("paint: redid the clear"), b"\x1a", wait_for("paint: undid the clear", 2),
          b"\x13", *keys("p")]
boot(120, steps=steps, until="paint: tool pencil", sd=card2)
PY
)
echo "$out" | grep -E "^(paint|-- |check|terminal: gave|display: paint opened|fs: refused|run.py)" | sed 's/^/  | /'
echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qx "paint: opened apps/paint/untitled.bmp (416x208, new)" || fail "paint did not start a new picture"
for what in "line" "filled rectangle" "rectangle" "filled ellipse" "ellipse" "fill" "brush"; do
  echo "$out" | grep -q "^paint: $what, [0-9]* tiles\? changed" || fail "no $what was drawn"
done
echo "$out" | grep -q "^paint: redid the brush; 7 steps to undo, 0 to redo" || fail "the brush stroke was not redone"
echo "$out" | grep -q "^paint: undid the brush; 6 steps to undo, 1 to redo" || fail "the brush stroke was not undone"
echo "$out" | grep -qx "paint: saved apps/paint/untitled.bmp (416x208, 259638 bytes) in [0-9]* ms -> ok" || fail "paint did not save"
echo "$out" | grep -qx "paint: opened apps/paint/untitled.bmp (416x208, from the card)" || fail "paint did not open its picture again"
echo "$out" | grep -qx "check: shown again: ok" || fail "the picture opened again does not show what was drawn: $(echo "$out" | grep "^check:")"
echo "$out" | grep -qx "paint: opened pic.bmp (100x60, from the card)" || fail "paint did not open the picture it was given"
echo "$out" | grep -qx "paint: saved pic.bmp (100x60, 18054 bytes) in [0-9]* ms -> ok" || fail "paint did not save the picture it was given by itself"
# On noise nothing packs: a line 3 pixels wide keeps 26 tiles whole, 20184 bytes, so undo
# holds 14 lines, and the 15th and 16th make room by dropping the oldest; clearing keeps
# all 338 tiles, and room is made for it by dropping all but the last line; it is undone,
# and redone, and undone again.
steps() { echo "$out" | grep -q "^paint: $1 $2" || fail "$3: $(echo "$out" | grep "^paint: $1" | tail -1)"; }
[ "$(echo "$out" | grep -c "^paint: line, 26 tiles changed; 14 steps to undo, 0 to redo (282576 of 290816 bytes)")" = 3 ] \
  || fail "undo did not keep the last 14 lines on noise: $(echo "$out" | grep "^paint: line, 26" | tail -1)"
steps "clear," "338 tiles changed; 2 steps to undo, 0 to redo" "clearing noise did not keep the whole picture"
steps "undid the clear;" "1 step to undo, 1 to redo" "the clear was not undone"
steps "undid the line;" "0 steps to undo, 2 to redo" "the line was not undone"
steps "redid the line;" "1 step to undo, 1 to redo" "the line was not redone"
steps "redid the clear;" "2 steps to undo, 0 to redo" "the clear was not redone"
echo "$out" | grep -q "^paint: saved noise.bmp (416x208, 259638 bytes) in [0-9]* ms -> ok" || fail "noise.bmp was not saved"

# The pictures, off the cards: the file system of user/fs.c (tools/mksd.py writes the same).
python3 - "$card" "$card2" "$noise" <<'PY' || fail "the saved pictures are wrong"
import struct, sys

def files(path):
    img = open(path, "rb").read()
    start = next(struct.unpack_from("<I", img, 446 + 16 * i + 8)[0] for i in range(4) if img[446 + 16 * i + 4] == 0xDA)
    part = img[start * 512:]
    (magic, version, total, jstart, jblocks, bstart, bblocks, istart, icount, dstart,
     clusters) = struct.unpack_from("<8s10I", part, 0)
    assert magic == b"LEANOSF2", magic
    cl = lambda c: part[(dstart + c * 8) * 512:(dstart + c * 8) * 512 + 4096]
    def read(ino):
        kind, _, size, *rest = struct.unpack_from("<HHI12III", part, istart * 512 + 64 * ino)
        direct, ind = rest[:12], rest[12]
        ptrs = list(direct) + (list(struct.unpack("<1024I", cl(ind))) if ind else [])
        return b"".join(cl(c) for c in ptrs[:(size + 4095) // 4096])[:size]
    def walk(ino, prefix):
        data = read(ino)
        for at in range(0, len(data), 64):
            e, kind = struct.unpack_from("<II", data, at)
            name = data[at + 8:at + 64].split(b"\0")[0].decode()
            if not e:
                continue
            yield prefix + name, e, kind
            if kind == 2:
                yield from walk(e, prefix + name + "/")
    return {name: (read(e) if kind == 1 else None) for name, e, kind in walk(1, "")}

def bmp(data, name):
    head = struct.unpack_from("<2sIHHIIiiHHIIiiII", data, 0)
    (magic, size, r1, r2, off, hsize, w, h, planes, bpp, comp, isize, xres, yres, used, important) = head
    stride = (w * 3 + 3) & ~3
    fields = dict(magic=magic, size=size, off=off, hsize=hsize, planes=planes, bpp=bpp, comp=comp, isize=isize,
                  used=used)
    want = dict(magic=b"BM", size=len(data), off=54, hsize=40, planes=1, bpp=24, comp=0, isize=stride * h, used=0)
    assert fields == want, (name, fields, want)
    assert len(data) == 54 + stride * h and h > 0, (name, len(data), w, h)
    for y in range(h):                   # the padding is zeros
        assert data[54 + stride * y + 3 * w:54 + stride * (y + 1)] == b"\0" * (stride - 3 * w), (name, "padding", y)
    def px(x, y):                        # (x, y) from the top left, as 0xRRGGBB
        at = 54 + stride * (h - 1 - y) + 3 * x
        b, g, r = data[at:at + 3]
        return r << 16 | g << 8 | b
    return w, h, px

f = files(sys.argv[1])
w, h, px = bmp(f["apps/paint/untitled.bmp"], "untitled.bmp")
assert (w, h) == (416, 208), (w, h)
RED, BLUE, BLACK, ORANGE, GREEN, YELLOW, WHITE = 0xed1c24, 0x3f48cc, 0, 0xff7f27, 0x22b14c, 0xfff200, 0xffffff
checks = [
    ((20, 20), RED, "the line's start"), ((110, 19), RED, "the line"), ((200, 21), RED, "the line's end"),
    ((110, 23), WHITE, "below the 3-pixel line"), ((110, 17), WHITE, "above it"),
    ((40, 50), BLUE, "the filled rectangle's corner"), ((80, 75), BLUE, "the filled rectangle"),
    ((120, 100), BLUE, "its far corner"), ((39, 50), WHITE, "left of it"), ((121, 100), WHITE, "right of it"),
    ((200, 100), BLACK, "the outline's left edge"), ((202, 100), BLACK, "3 pixels wide"), ((300, 140), BLACK, "its corner"),
    ((250, 100), YELLOW, "the fill inside the outline"), ((203, 63), YELLOW, "the fill to its corner"),
    ((250, 50), WHITE, "above the outline: not filled"), ((310, 100), WHITE, "right of it: not filled"),
    ((360, 40), ORANGE, "the filled ellipse's middle"), ((321, 22), WHITE, "its box's corner: not in it"),
    ((20, 160), GREEN, "the ellipse's left edge"), ((70, 130), GREEN, "its top"), ((70, 160), WHITE, "its inside"),
    ((365, 170), WHITE, "the undone brush stroke"), ((330, 150), WHITE, "the undone stroke's start"),
    ((0, 200), BLACK, "the line that left the window, at the edge"), ((30, 200), BLACK, "that line"),
    ((62, 200), WHITE, "past its start"), ((10, 100), WHITE, "the paper"),
]
bad = [f"{what} at {xy}: {px(*xy):06x}, not {c:06x}" for xy, c, what in checks if px(*xy) != c]
assert not bad, bad
print(f"untitled.bmp: {w}x{h}, 24 bits, {len(f['apps/paint/untitled.bmp'])} bytes, {len(checks)} pixels as drawn")
assert "apps/paint/save.part~" not in f, "save.part~ left behind"

f = files(sys.argv[2])
w, h, px = bmp(f["pic.bmp"], "pic.bmp")
assert (w, h) == (100, 60), (w, h)
diff = [(x, y) for y in range(h) for x in range(w)
        if px(x, y) != ((x + y) & 255) << 16 | ((y * 4) & 255) << 8 | ((x * 2) & 255)]
assert diff == [(50, 30)] and px(50, 30) == RED, diff[:10]
print("pic.bmp: 100x60, every pixel as it was but the one drawn")
w, h, px = bmp(f["noise.bmp"], "noise.bmp")
_, _, before = bmp(open(sys.argv[3], "rb").read(), "the noise")
lines = {y + d for y in [16 * r + 8 for r in range(13)] + [16 * r + 4 for r in range(3)] for d in (-1, 0, 1)}
diff = [(x, y) for y in range(h) for x in range(w) if px(x, y) != (0 if y in lines else before(x, y))]
assert not diff, diff[:10]
assert "apps/paint/save.part~" not in f, "save.part~ left behind"
print("noise.bmp: the 16 lines, the rest as it was, after the clear was undone")
PY
echo "ok: paint draws lines, shapes, fills and strokes, undoes and redoes, and saves a standard 24-bit BMP that opens again"
