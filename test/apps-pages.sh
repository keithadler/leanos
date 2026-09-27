#!/bin/bash
# Apps (user/launcher.c) with more programs than one page shows. The card holds the ten
# programs of the usual card and fourteen more, copies of hello under other names (every
# other one with hello's icon): 24 programs, three pages of ten.
#
#   1. Apps, from the dock, lists all 24 and shows the first page, with the pager on the card
#      heading's line. The next button, twice, turns to page 3, whose icons are loaded then
#      (maple's is hello's, the same pixels as hello's on page 1; lotus has none, and gets a
#      tile with its initial). A click on maple starts it.
#   2. With Apps in front again, the keys: Page Up turns back to page 2, Right selects its
#      first program, Left goes back past the page's start, to web on page 1. Typing "zu"
#      finds zulu (the last program, on page 3) and selects it; "x" finds nothing, Backspace
#      takes it off again (the field shows "zu", with zulu selected); Return starts zulu. Escape, from the USB keyboard, clears the field.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/apps-page1.* "$T"/apps-page3.* "$T"/apps-find.*
progs="hello clock tour calc snake life tiles fuzz edit web"
extra="amber birch cedar dune ember fjord grove heath iris jade kelp lotus maple zulu"
with_icon="amber cedar ember grove iris kelp maple"
make -s $(for p in $progs; do echo "build/progs/$p.elf build/icons/$p.icon"; done) || fail "the programs did not build"
card=$T/sd-apps-pages.img
python3 tools/mksd.py "$card" $(for p in $progs; do echo "$p=build/progs/$p.elf"; done) \
  $(for p in $extra; do echo "$p=build/progs/hello.elf"; done) \
  $(for p in $progs; do echo "$p.icon=build/icons/$p.icon"; done) \
  $(for p in $with_icon; do echo "$p.icon=build/icons/hello.icon"; done) >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, pause, snap, usb_key, DOCK, TITLE_H
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
# in the window: the next button on the card heading's line, and page 3's third cell (maple)
NEXT = (438 + 11, TITLE_H + 144 + 11)
MAPLE = (20 + 2 * 88 + 44, TITLE_H + 170 + 40)
steps = [*click(*DOCK["Apps"]), wait_for("apps: opened"), pause(0.3), snap("apps-page1"),
         *wclick("Apps", *NEXT), wait_for("apps: page 2 of 3"),
         *wclick("Apps", *NEXT), wait_for("apps: page 3 of 3"), pause(0.3), snap("apps-page3"),
         *wclick("Apps", *MAPLE), wait_for("apps: maple started"), wait_for("hello: opened"),
         *click(*DOCK["Apps"]), pause(0.5),        # Apps in front again
         b"\x1b[5~", wait_for("apps: page 2 of 3"), b"\x1b[C", wait_for("apps: selected amber"),
         b"\x1b[D", wait_for("apps: selected web"),
         *keys("zu"), wait_for('apps: find "zu"'), b"x", wait_for('apps: find "zux"'),
         b"\x7f", wait_for('apps: find "zu"', 2), pause(0.3), snap("apps-find"), b"\r", wait_for("apps: zulu started"), wait_for("hello: opened", 2),
         *click(*DOCK["Apps"]), pause(0.5), *usb_key("esc"), wait_for("apps: find cleared")]
sys.exit(boot(120, steps=steps, until="apps: find cleared", sd=sys.argv[1], usb=True, settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(apps|hello): " | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"

# (the first list is at boot, when Apps looks for startup.txt: this card has none)
got=$(echo "$out" | grep -E "^apps: " | grep -vE "^apps: (time zone|saved)")
expected=$(printf '%s\n' \
  "apps: 24 programs, 17 with icons" \
  "apps: 24 programs, 17 with icons" \
  "apps: opened a window -> ok" \
  "apps: page 2 of 3" \
  "apps: page 3 of 3" \
  "apps: maple started in slot 10" \
  "apps: page 2 of 3" \
  "apps: selected amber" \
  "apps: page 1 of 3" \
  "apps: selected web" \
  'apps: find "z": 2 of 24 programs' \
  "apps: selected zulu" \
  'apps: find "zu": 1 of 24 programs' \
  'apps: find "zux": 0 of 24 programs' \
  'apps: find "zu": 1 of 24 programs' \
  "apps: selected zulu" \
  "apps: zulu started in slot 11" \
  "apps: find cleared: 24 programs")
[ "$got" = "$expected" ] || { echo "expected:"; echo "$expected"; echo "got:"; echo "$got"; fail "Apps did not page, find and start as asked"; }

python3 - "$T" <<'PY' || fail "the pages are not what Apps drew"
import os, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
T = sys.argv[1]
log = open(os.path.join(T, "serial.txt")).read()
ax, ay = window_pos(log, "Apps")
ay += TITLE_H
def load(name):
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    return lambda x, y: tuple(px[(y * w + x) * 3:(y * w + x) * 3 + 3])
one, three, find = load("apps-page1"), load("apps-page3"), load("apps-find")
icon = lambda at, col: [at(ax + 20 + col * 88 + 20 + i, ay + 170 + 6 + j) for j in range(48) for i in range(48)]
# maple (page 3, third) shows hello's icon, as hello (page 1, first) does, pixel for pixel
assert icon(three, 2) == icon(one, 0), "maple's icon is not hello's"
assert len(set(icon(three, 2))) > 20, "no icon where maple is"
# lotus (page 3, second) has no icon: a tile of one color with its initial
tile = icon(three, 1)
assert tile[24 * 48 + 8] == tile[40 * 48 + 24] and tile[24 * 48 + 8] != (247, 247, 250), ("lotus's tile", tile[24 * 48 + 8])
# page 3 has four programs: the fifth cell and the second row are empty
assert set(icon(three, 4)) == {(247, 247, 250)}, "a fifth program on page 3"
# the pager: the previous button lit on page 3 (dark chevron), gray on page 1
dark = lambda at: sum(1 for y in range(ay + 144, ay + 166) for x in range(ax + 346, ax + 368) if max(at(x, y)) < 110)
assert dark(three) > 10 and dark(one) == 0, ("the previous button", dark(one), dark(three))
# "zu" typed: the search field has a blue edge, and zulu, the one match, first in the grid,
# the selection's blue ring; the field is gray with nothing typed
blue = (58, 110, 230)
assert find(ax + 235, ay + 144) == blue and one(ax + 235, ay + 144) != blue, "the search field"
assert find(ax + 25, ay + 210) == blue and find(ax + 20 + 88 + 25, ay + 210) != blue, "zulu is not selected"
assert set(icon(find, 1)) == {(247, 247, 250)}, "more than one match shown"
print("ok: page 3 shows its own icons (hello's for maple, a tile for lotus), the pager each page's buttons, "
      "and the search field what was typed, with the match selected")
PY
echo "ok: Apps lists 24 programs on three pages; one on the last page starts by paging, and by typing its name"
