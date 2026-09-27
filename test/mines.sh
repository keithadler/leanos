#!/bin/bash
# Minesweeper from the card (user/progs/mines.c), played by a script on a board the test knows.
#
# Terminal writes apps/mines/seed.txt, which seeds every game's mines (mines.c places them
# after the first click with a small generator; this test places them with a copy of it,
# below, and works out the board). Then `run mines`, on Beginner (9 x 9, 10 mines):
#   1. The first click, in the middle, opens an area: on the screen exactly the cells the
#      board says it opens are open, and the rest are not.
#   2. The Flag button, lit, makes a click flag a mine; out again, the keys move the cursor
#      to another cell, and F flags and unflags it. A right click (ESC m D, then U) flags a
#      third cell and another takes the flag back. On the screen: the flags, on closed cells.
#   3. A click on another mine loses: that one on red, every other mine shown, the flagged
#      one still flagged.
#   4. N starts a new game; the same first click places the same mines. The keys flag a mine
#      beside an open 1, and a click on the 1 opens the rest around it (a chord); the arrow
#      keys and Space open one safe cell, and clicks every other the board says is still
#      closed: won, each mine flagged and every other cell open on the screen, and a best
#      time, saved.
#   5. 3 shows Expert, 30 x 16 cells in the window, and a click on Beginner along the bottom
#      goes back. Closed and run again, mines reads its best time back (and 2 shows
#      Intermediate); on the card image, apps/mines/best.txt says it, in one line.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/mines-*.ppm "$T"/mines-*.png

SEED=28
cat > "$T/board.py" <<'PY'
# mines.c's placement, the same steps: xorshift32 from the seed, a cell index modulo the
# cells, taken unless it is a mine already or next to the first click.
def board(seed, cols, rows, count, fx, fy):
    x, mines = seed, set()
    while len(mines) < count:
        x ^= (x << 13) & 0xffffffff
        x ^= x >> 17
        x ^= (x << 5) & 0xffffffff
        i = x % (cols * rows)
        c = (i % cols, i // cols)
        if c in mines or (abs(c[0] - fx) <= 1 and abs(c[1] - fy) <= 1):
            continue
        mines.add(c)
    return mines

def around(c, cols, rows):
    return [(c[0] + dx, c[1] + dy) for dy in (-1, 0, 1) for dx in (-1, 0, 1)
            if (dx or dy) and 0 <= c[0] + dx < cols and 0 <= c[1] + dy < rows]

def near(c, mines, cols, rows):
    return sum(n in mines for n in around(c, cols, rows))

def flood(c, mines, opened, cols, rows):
    """What a click on safe cell c opens, as mines.c's flood does."""
    todo, got = [c], {c}
    while todo:
        d = todo.pop()
        if near(d, mines, cols, rows):
            continue
        for n in around(d, cols, rows):
            if n not in opened and n not in got and n not in mines:
                got.add(n)
                todo.append(n)
    return got
PY

out=$(SEED=$SEED python3 - "$T" <<'PY'
import os, sys
sys.path.insert(0, "test")
sys.path.insert(0, sys.argv[1])
from run import boot, mouse, wait_for, pause, snap, wclick, wmouse, CLOSE, DOCK, TITLE_H
from board import board, flood, around, near
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
line = lambda s: [s.encode() + b"\r"]
UP, DOWN, RIGHT, LEFT = b"\x1b[A", b"\x1b[B", b"\x1b[C", b"\x1b[D"
SEED = int(os.environ["SEED"])
# Beginner in mines.c's window: 28-pixel cells from (123, 42); the Flag button at (75, 6),
# 74 x 26; the levels along the bottom from (9, 300), 160 x 24 each
CS, BX, BY = 28, 123, 42
cell = lambda c: wclick("mines", BX + c[0] * CS + CS // 2, TITLE_H + BY + c[1] * CS + CS // 2)
right = lambda c: [wmouse(k, "mines", BX + c[0] * CS + CS // 2, TITLE_H + BY + c[1] * CS + CS // 2) for k in "DU"]
FLAG_BUTTON = wclick("mines", 75 + 37, TITLE_H + 6 + 13)
BEGINNER = wclick("mines", 9 + 80, TITLE_H + 300 + 12)
FIRST = (4, 4)
mines = board(SEED, 9, 9, 10, *FIRST)
opened = flood(FIRST, mines, set(), 9, 9)
closed = sorted(c for c in [(x, y) for y in range(9) for x in range(9)] if c not in opened)
m1, m2 = sorted(mines)[0], sorted(mines)[-1]            # the one flagged, the one that loses
other = next(c for c in closed if c != m1 and c not in mines)
third = next(c for c in closed if c not in (m1, other))           # flagged by the right button
def moves(a, b):
    """The arrow keys from cell a to cell b."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    return [RIGHT if dx > 0 else LEFT] * abs(dx) + [DOWN if dy > 0 else UP] * abs(dy)
# game 2: a flag by the keys beside a 1, a click on the 1 (a chord), one safe cell by the keys,
# then a click on each safe cell still closed
one = next(c for c in sorted(opened) if near(c, mines, 9, 9) == 1 and
           any(n not in opened and n not in mines for n in around(c, 9, 9)))
beside = next(n for n in around(one, 9, 9) if n in mines)
got = set(opened)
for n in around(one, 9, 9):
    if n not in got and n not in mines:
        got |= flood(n, mines, got, 9, 9)
chorded = len(got) - len(opened)
by_key = next(c for c in closed if c not in mines and c not in got)
by_key_opens = len(flood(by_key, mines, got, 9, 9))
got |= flood(by_key, mines, got, 9, 9)
clicks = []
for c in closed:
    if c not in mines and c not in got:
        clicks.append(c)
        got |= flood(c, mines, got, 9, 9)
assert len(got) == 81 - 10
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *line("mkdir apps"), wait_for("terminal: mkdir apps"),
         *line("mkdir apps/mines"), wait_for("terminal: mkdir apps/mines"),
         *line(f"write apps/mines/seed.txt {SEED}"), wait_for("terminal: write apps/mines/seed.txt"),
         *line("run mines"), wait_for("mines: opened a window"),
         # 1. the first click
         *cell(FIRST), wait_for(f"mines: opened {len(opened)} cells at 4,4"), pause(0.3), snap("mines-first"),
         # 2. flags: by the Flag button, and by the keys
         *FLAG_BUTTON, wait_for("mines: flag mode on"), *cell(m1), wait_for("mines: flagged"),
         *FLAG_BUTTON, wait_for("mines: flag mode off"),
         *moves(m1, other), b"f", wait_for("mines: flagged", 2), b"F", wait_for("mines: unflagged"),
         *right(third), wait_for("mines: flagged", 3), pause(0.3), snap("mines-right"),
         *right(third), wait_for("mines: unflagged", 2), pause(0.3), snap("mines-flag"),
         # 3. a mine
         *cell(m2), wait_for("mines: lost at"), pause(0.3), snap("mines-lost"),
         # 4. the same board again, won
         b"n", wait_for("mines: new game", 2), *cell(FIRST), wait_for("mines: mines placed", 2),
         *moves(FIRST, beside), b"f", wait_for("mines: flagged", 4),
         *cell(one), wait_for(f"mines: chord at {one[0]},{one[1]} opened {chorded} cell"),
         *moves(one, by_key), b" ", wait_for(f"mines: opened {by_key_opens} "),
         *[x for c in clicks for x in cell(c)], wait_for("mines: won beginner"),
         wait_for("mines: saved"), pause(0.3), snap("mines-won"),
         # 5. Expert and back; its best time read back
         b"3", wait_for("mines: new game, expert"), pause(0.3), snap("mines-expert"),
         *BEGINNER, wait_for("mines: new game, beginner", 3),
         *wclick("mines", *CLOSE), wait_for("mines: window closed"),
         *wclick("Terminal", 230, 60), *line("run mines"), wait_for("mines: best times", 2),
         wait_for("mines: opened a window", 2), b"2"]
print("test: board " + " ".join(f"{x},{y}" for x, y in sorted(mines)) +
      f" first-open {len(opened)} m1 {m1[0]},{m1[1]} m2 {m2[0]},{m2[1]} other {other[0]},{other[1]} third {third[0]},{third[1]}"
      f" chord {one[0]},{one[1]} opened {chorded} by-key {by_key[0]},{by_key[1]} clicks {len(clicks)}", flush=True)
sys.exit(boot(150, steps=steps, until="mines: new game, intermediate", settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(test: |mines: |terminal: (run|mkdir|write))" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -qx "mines: seed $SEED from apps/mines/seed.txt, for every game" || fail "mines did not read its seed"
echo "$out" | grep -qx "mines: lost at .* after [0-9]* s" || fail "a click on a mine did not lose"

python3 - "$T" <<'PY' || fail "the board on the screen, or the best time, is not what it should be"
import os, re, struct, sys
sys.path.insert(0, "test")
sys.path.insert(0, sys.argv[1])
from run import window_pos, TITLE_H
from board import board, flood
T = sys.argv[1]
log = open(os.path.join(T, "serial.txt")).read().splitlines()
info = next(l for l in log if l.startswith("test: board "))
m1, m2, other, third = (tuple(map(int, re.search(k + r" (\d+),(\d+)", info).groups())) for k in ("m1", "m2", "other", "third"))
seed = int(re.search(r"mines: seed (\d+)", "\n".join(log)).group(1))
mines = board(seed, 9, 9, 10, 4, 4)
first = flood((4, 4), mines, set(), 9, 9)
cells = [(x, y) for y in range(9) for x in range(9)]

assert f"mines: mines placed after the first click at 4,4 (seed {seed}, from seed.txt)" in log
assert f"mines: opened {len(first)} cells at 4,4" in log, ("the first click opened", len(first))
assert f"mines: flagged {m1[0]},{m1[1]} (9 left)" in log
assert f"mines: flagged {other[0]},{other[1]} (8 left)" in log and f"mines: unflagged {other[0]},{other[1]} (9 left)" in log
# the right button: flagged, then not; nothing else flagged or opened in between
ml = [l for l in log if l.startswith("mines: ")]
i = ml.index(f"mines: unflagged {other[0]},{other[1]} (9 left)")
assert ml[i + 1:i + 3] == [f"mines: flagged {third[0]},{third[1]} (8 left)", f"mines: unflagged {third[0]},{third[1]} (9 left)"], ml[i + 1:i + 4]
assert any(l.startswith(f"mines: lost at {m2[0]},{m2[1]} after ") for l in log)
won = next(l for l in log if l.startswith("mines: won beginner in "))
secs = int(re.match(r"mines: won beginner in (\d+) s \(\d+ ms\), a new best$", won).group(1))
assert "mines: saved apps/mines/best.txt -> ok" in log
assert "mines: new game, expert (30x16, 99 mines)" in log
assert log.count("mines: best times: beginner none, intermediate none, expert none") == 1
assert f"mines: best times: beginner {secs} s, intermediate none, expert none" in log, "the best time did not read back"

# the screens, from the window's first place (the second run may open elsewhere)
upto = log[:next(i for i, l in enumerate(log) if l.startswith("mines: window closed"))]
wx, wy = window_pos(upto, "mines")
def load(name):
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    def at(x, y):
        o = ((wy + TITLE_H + y) * w + wx + x) * 3
        return tuple(px[o:o + 3])
    return at
RAISED, FLAT, BOOM, MINE, FLAG = (184, 192, 207), (232, 234, 239), (232, 64, 52), (24, 24, 30), (226, 40, 36)
def board_px(name, cs, bx, by):
    at = load(name)
    bg = lambda c: at(bx + c[0] * cs + 3, by + c[1] * cs + 3)          # clear of any mark
    # the middle of a mine, a little up and left of the middle: the pointer is on a clicked one
    mid = lambda c: at(bx + c[0] * cs + cs // 2 - 2, by + c[1] * cs + cs // 2 - 2)
    flagged = lambda c: FLAG in [at(bx + c[0] * cs + i, by + c[1] * cs + j) for j in range(cs) for i in range(cs)]
    return bg, mid, flagged
CS, BX, BY = 28, 123, 42

bg, mid, flagged = board_px("mines-first", CS, BX, BY)
for c in cells:
    assert bg(c) == (FLAT if c in first else RAISED), ("after the first click", c, bg(c))

bg, mid, flagged = board_px("mines-right", CS, BX, BY)
assert bg(third) == RAISED and flagged(third), ("the right button's flag", third)
assert bg(m1) == RAISED and flagged(m1) and not flagged(other), ("the flags", m1, other)

bg, mid, flagged = board_px("mines-flag", CS, BX, BY)
assert bg(m1) == RAISED and flagged(m1), ("the flag", m1)
assert bg(other) == RAISED and not flagged(other), ("unflagged", other)
assert bg(third) == RAISED and not flagged(third), ("unflagged by the right button", third)

bg, mid, flagged = board_px("mines-lost", CS, BX, BY)
assert bg(m2) == BOOM and mid(m2) == MINE, ("the mine that went off", bg(m2), mid(m2))
assert bg(m1) == RAISED and flagged(m1), ("the flagged mine", m1)
for c in mines - {m1, m2}:
    assert bg(c) == FLAT and mid(c) == MINE, ("a mine not shown", c, bg(c), mid(c))
for c in cells:
    if c not in mines and c not in first:
        assert bg(c) == RAISED, ("a closed cell opened on the loss", c)

bg, mid, flagged = board_px("mines-won", CS, BX, BY)
for c in cells:
    if c in mines:
        assert bg(c) == RAISED and flagged(c), ("a mine not flagged on the win", c)
    else:
        assert bg(c) == FLAT, ("a cell not open on the win", c, bg(c))

bg, mid, flagged = board_px("mines-expert", 16, 9, 40)
for c in [(x, y) for y in range(16) for x in range(30)]:
    assert bg(c) == RAISED, ("expert", c, bg(c))

# apps/mines/best.txt on the card image: the file system of user/fs.c (tools/mksd.py)
card = open(os.path.join(T, "sd-test.img"), "rb").read()
part = 2048 * 512
magic, _, total, js, jb, bs, bb, ins, icount, ds, clusters = struct.unpack_from("<8s10I", card, part)
assert magic == b"LEANOSF2"
def inode(n):
    kind, _, size, *rest = struct.unpack_from("<HHI12III", card, part + ins * 512 + 64 * n)
    return kind, size, rest[:12]
def content(n):
    kind, size, direct = inode(n)
    assert size <= 12 * 4096
    data = b"".join(card[part + (ds + c * 8) * 512:part + (ds + c * 8 + 8) * 512] for c in direct if c)
    return data[:size]
def lookup(path):
    n = 1
    for name in path.split("/"):
        d = content(n)
        n = next(ino for ino, kind, nm in (struct.unpack_from("<II56s", d, o) for o in range(0, len(d), 64))
                 if ino and nm.rstrip(b"\0").decode() == name)
    return n
best = content(lookup("apps/mines/best.txt")).decode()
assert best == f"beginner {secs}\n", ("best.txt says", best)
print(f"ok: the first click opened {len(first)} cells, as the board says; flags, by the right button too; the loss showed all 10 mines; "
      f"the win in {secs} s flagged them; Expert drew 30 x 16; best.txt on the card: {best.strip()!r}")
PY
echo "ok: mines places its mines after the first click, flags (by a right click too), loses, wins, and keeps the best time"
