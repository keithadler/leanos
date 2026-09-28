#!/bin/bash
# Klondike from the card (user/progs/solitaire.c), played by a script on a deal the test knows.
#
# Terminal writes apps/solitaire/seed.txt, which seeds every deal (solitaire.c shuffles with a
# small generator; this test shuffles with a copy of it, below, and deals the same way). Seed
# 12 deals 9d Ad 9c 5s 8c 4c 2h face up. Then `run solitaire`, in Draw 1:
#   1. The deal on the screen, read by its pixels: on each pile, the face-down cards' backs,
#      and the top card face up, in its color, with its pips where its rank puts them (the ace:
#      one large suit); the stock face down, the waste and the foundations empty.
#   2. A drag of 8c from pile 5 onto 9d on pile 1 (legal): it moves, and Jd turns up under it.
#      A drag of 9c from pile 3 onto 5s on pile 4 (not legal): it goes back where it was.
#   3. A click on the stock draws 6s onto the waste. A double click on Ad sends it to a
#      foundation, and the card under it turns up. Ctrl+Z takes that back (the ace on its pile,
#      the card under it face down, the foundation empty); a right click sends it again, and
#      U takes it back again.
#   4. D deals again in Draw 3, and a click on the stock draws three; D again, Draw 1.
#   5. The whole game, by the keys (1 to 7 and W pick a pile or the waste, then 1 to 7 or F
#      the destination, Space the stock): the moves come from a small solver (below), which
#      searches the same deal for moves that reach the stock and waste empty and every card
#      face up; from there solitaire finishes by itself, and the game is won. The celebration
#      runs its frames; on the screen, each foundation shows a king and the panel says won.
#   6. Closed and run again, solitaire reads its stats back: 3 games played (each with a
#      move), 1 won, the best time the win's. On the card image, apps/solitaire/stats.txt
#      says so, in three lines.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/sol-*.ppm "$T"/sol-*.png

SEED=12
cat > "$T/klondike.py" <<'PY'
# solitaire.c's deal, and a small solver.
SUITS = "cdhs"                     # clubs, diamonds, hearts, spades: 1 and 2 are red
RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
name = lambda c: RANKS[c % 13] + SUITS[c // 13]
rank = lambda c: c % 13 + 1
red = lambda c: c // 13 in (1, 2)
fits = lambda c, d: rank(d) == rank(c) + 1 and red(c) != red(d)

def deal(seed):
    """The tableau (7 lists of [card, face up]) and the stock (its top last), as
    solitaire.c's new_game: xorshift32, Fisher-Yates from the last card down, dealt a row at
    a time."""
    x, deck = seed or 1, list(range(52))
    for i in range(51, 0, -1):
        x ^= (x << 13) & 0xffffffff
        x ^= x >> 17
        x ^= (x << 5) & 0xffffffff
        j = x % (i + 1)
        deck[i], deck[j] = deck[j], deck[i]
    tab, k = [[] for _ in range(7)], 0
    for r in range(7):
        for p in range(r, 7):
            tab[p].append([deck[k], p == r])
            k += 1
    return tab, deck[28:]

def solve(seed, limit=300000):
    """Keys for Draw 1 that reach the stock and waste empty and every card face up, by a
    depth-first search (foundation moves first, then tableau moves that uncover a card, the
    waste, the stock), or None. A key pair: a source ('1'-'7', 'w') and a destination
    ('1'-'7', 'f'), as solitaire.c's keys take them; ' ' is the stock."""
    tab, stock = deal(seed)
    start = (tuple(tuple((c, u) for c, u in p) for p in tab), tuple(stock), (), (0, 0, 0, 0))
    seen, path, nodes = set(), [], [0]

    def moves(st):
        tab, stock, waste, found = st
        home = lambda c: found[c // 13] == rank(c) - 1
        def put(c):
            f = list(found); f[c // 13] += 1; return tuple(f)
        def take(p, k):
            t = list(tab)
            rest = list(t[p][:len(t[p]) - k])
            if rest and not rest[-1][1]:
                rest[-1] = (rest[-1][0], True)
            t[p] = tuple(rest)
            return t
        if waste and home(waste[-1]):
            yield "wf", (tab, stock, waste[:-1], put(waste[-1]))
        for p in range(7):
            if tab[p] and home(tab[p][-1][0]):
                yield f"{p + 1}f", (tuple(take(p, 1)), stock, waste, put(tab[p][-1][0]))
        for p in range(7):
            pile = tab[p]
            if not pile:
                continue
            first = next(i for i, (c, u) in enumerate(pile) if u)
            for q in range(7):
                if q == p:
                    continue
                if tab[q]:
                    i = next((i for i in range(first, len(pile)) if fits(pile[i][0], tab[q][-1][0])), None)
                    if i is None or (i != first and not home(pile[i - 1][0])):
                        continue
                elif rank(pile[first][0]) == 13 and first > 0:
                    i = first
                else:
                    continue
                t = take(p, len(pile) - i)
                t[q] = tab[q] + pile[i:]
                yield f"{p + 1}{q + 1}", (tuple(t), stock, waste, found)
        if waste:
            c = waste[-1]
            for q in range(7):
                if (tab[q] and fits(c, tab[q][-1][0])) or (not tab[q] and rank(c) == 13):
                    t = list(tab)
                    t[q] = tab[q] + ((c, True),)
                    yield f"w{q + 1}", (tuple(t), stock, waste[:-1], found)
        if stock:
            yield " ", (tab, stock[:-1], waste + (stock[-1],), found)
        elif waste:
            yield " ", (tab, tuple(reversed(waste)), (), found)

    def dfs(st, depth):
        tab, stock, waste, found = st
        if not stock and not waste and all(u for p in tab for c, u in p):
            return found
        if st in seen or nodes[0] > limit or depth > 400:
            return None
        seen.add(st)
        nodes[0] += 1
        for k, nst in moves(st):
            path.append(k)
            got = dfs(nst, depth + 1)
            if got:
                return got
            path.pop()
        return None

    import sys
    sys.setrecursionlimit(10000)
    found = dfs(start, 0)
    return (path, 52 - sum(found)) if found else None
PY

out=$(SEED=$SEED python3 - "$T" <<'PY'
import collections, os, sys
sys.path.insert(0, "test")
sys.path.insert(0, sys.argv[1])
from run import boot, mouse, wait_for, pause, snap, wclick, wmouse, CLOSE, DOCK, TITLE_H
from klondike import deal, solve, name
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
line = lambda s: [s.encode() + b"\r"]
SEED = int(os.environ["SEED"])
# solitaire.c's layout, in the window: columns 59 px apart from x 7, the top row at y 38, the
# tableau from y 118, face-down cards 5 px apart, a card 52 x 72
COL = lambda i: 7 + 59 * i
TOP_Y, TAB_Y, CW, CH = 38, 118, 52, 72
at = lambda kind, x, y: wmouse(kind, "solitaire", x, TITLE_H + y)
park = at("v", 410, 386)                       # the pointer, off the cards, before a capture
def drag(x0, y0, x1, y1):
    return [at("d", x0, y0), at("v", (x0 + x1) // 2, (y0 + y1) // 2), at("v", x1, y1), at("u", x1, y1)]
tab, stock = deal(SEED)
assert [name(p[-1][0]) for p in tab] == ["9d", "Ad", "9c", "5s", "8c", "4c", "2h"], "the deal the test is written for"
turned_t5, turned_t2 = name(tab[4][-2][0]), name(tab[1][-2][0])
three = " ".join(name(c) for c in reversed(stock[-3:]))
keys, auto = solve(SEED)
moves = collections.Counter()                  # "solitaire: move N:" lines expected so far
def move():
    """A step that waits for the next move of the game being played (the move numbers start
    again with each game)."""
    moves[game[0]] += 1
    n = sum(1 for g, k in seen_moves if k == moves[game[0]]) + 1
    seen_moves.append((game[0], moves[game[0]]))
    return wait_for(f"solitaire: move {moves[game[0]]}:", n)
game, seen_moves = [0], []
def new_game():
    game[0] += 1
    moves[game[0]] = 0
def back():
    """An undo: the next move gets the number again."""
    moves[game[0]] -= 1

steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *line("mkdir apps"), wait_for("terminal: mkdir apps"),
         *line("mkdir apps/solitaire"), wait_for("terminal: mkdir apps/solitaire"),
         *line(f"write apps/solitaire/seed.txt {SEED}"), wait_for("terminal: write apps/solitaire/seed.txt"),
         *line("run solitaire"), wait_for("solitaire: opened a window"), pause(0.5), snap("sol-deal")]
new_game()
# 2. a legal drag, then one that is not
steps += [*drag(COL(4) + 26, TAB_Y + 20 + 40, COL(0) + 26, TAB_Y + 17 + 40), move(), park, pause(0.3), snap("sol-drag"),
          *drag(COL(2) + 26, TAB_Y + 10 + 40, COL(3) + 26, TAB_Y + 15 + 45), wait_for("solitaire: 9c "), park, pause(0.3), snap("sol-back")]
# 3. the stock; a double click on the ace, undone; a right click on it, undone
steps += [at("d", COL(0) + 26, TOP_Y + 36), at("u", COL(0) + 26, TOP_Y + 36), move(),
          *[at(k, COL(1) + 26, TAB_Y + 5 + 40) for k in "dudu"], move(), park, pause(0.3), snap("sol-ace")]
back()
steps += [b"\x1a", wait_for("solitaire: undid move 3"), park, pause(0.3), snap("sol-undo"),
          *[at(k, COL(1) + 26, TAB_Y + 5 + 40) for k in "DU"], move()]
back()
steps += [b"u", wait_for("solitaire: undid move 3", 2)]
# 4. Draw 3, and back to Draw 1
steps += [b"d", wait_for("solitaire: new game, draw 3")]
new_game()
steps += [b" ", move(), park, pause(0.3), snap("sol-draw3"), b"d", wait_for("solitaire: new game, draw 1", 2)]
new_game()
# 5. the whole game
for k in keys:
    steps += [k[0].encode()] + ([k[1].encode()] if len(k) > 1 else []) + [move()]
steps += [wait_for("solitaire: won in"), pause(1), snap("sol-bounce"), wait_for("solitaire: celebration"), pause(0.5), snap("sol-won"),
          *wclick("solitaire", *CLOSE), wait_for("solitaire: window closed"),
          *wclick("Terminal", 230, 60), *line("run solitaire")]
print(f"test: solver {len(keys)} moves, then {auto} by the automatic finish; turned up {turned_t5} and {turned_t2}; draw 3: {three}", flush=True)
print("test: keys " + "|".join(keys), flush=True)
sys.exit(boot(240, steps=steps, until="solitaire: stats: played 3", settle=0.5))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(test: solver|solitaire: |terminal: (run|mkdir|write))" | grep -vE "^solitaire: move ([0-9]*[02-9]|[0-9]+1[0-9]):" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -qx "solitaire: seed $SEED from apps/solitaire/seed.txt, for every deal" || fail "solitaire did not read its seed"

python3 - "$T" <<'PY' || fail "the game on the screen, or the stats, are not what they should be"
import os, re, struct, sys
sys.path.insert(0, "test")
sys.path.insert(0, sys.argv[1])
from run import window_pos, TITLE_H
from klondike import deal, name, rank, red
T = sys.argv[1]
log = open(os.path.join(T, "serial.txt")).read().splitlines()
sol = [l for l in log if l.startswith("solitaire: ")]
seed = int(re.search(r"solitaire: seed (\d+)", "\n".join(log)).group(1))
tab, stock = deal(seed)
info = next(l for l in log if l.startswith("test: solver "))
nkeys, nauto = map(int, re.match(r"test: solver (\d+) moves, then (\d+)", info).groups())
t5, t2 = tab[4][-2][0], tab[1][-2][0]

def after(prefix, n=1):
    """The solitaire lines after the n-th that starts with prefix."""
    i = [k for k, l in enumerate(sol) if l.startswith(prefix)][n - 1]
    return sol[i + 1:]
tops = " ".join(name(p[-1][0]) for p in tab)
first_run = sol[:sol.index("solitaire: window closed, exiting")]
assert first_run.count(f"solitaire: dealt {tops} face up, 24 in the stock") == 3, "the deals"
assert f"solitaire: move 1: 8c t5 -> t1, turned up {name(t5)}" in sol
assert "solitaire: 9c cannot go on t4; back to t3" in sol
assert f"solitaire: move 2: drew {name(stock[-1])} (stock 23)" in sol
assert sol.count(f"solitaire: move 3: Ad t2 -> f1, turned up {name(t2)}") == 2, "the double click and the right click"
assert sol.count("solitaire: undid move 3") == 2
draw3 = " ".join(name(c) for c in reversed(stock[-3:]))
assert f"solitaire: move 1: drew {draw3} (stock 21)" in sol, "Draw 3"
# the game played by the keys: every move one, then the automatic finish, and the win
game = after("solitaire: new game, draw 1", 2)
assert "solitaire: every card is face up: finishing" in game
won = next(l for l in game if l.startswith("solitaire: won in "))
m = re.match(r"solitaire: won in (\d+):(\d\d) \((\d+) ms\), (\d+) moves, a new best$", won)
assert m, won
secs, total = int(m.group(3)) // 1000, int(m.group(4))
assert int(m.group(1)) * 60 + int(m.group(2)) == secs, won
assert total == nkeys + nauto, (total, nkeys, nauto)
assert not any("cannot" in l or "nothing" in l for l in game[:game.index(won)]), "a key that did nothing"
assert re.match(r"solitaire: celebration done, \d+ frames, \d+ cards$", next(l for l in game if l.startswith("solitaire: celebration"))), "the celebration"
assert log.count("solitaire: stats: played 0, won 0, best none") == 1
assert f"solitaire: stats: played 3, won 1, best {secs} s" in sol, "the stats did not read back"

# the screens, from the window's first place
upto = log[:next(i for i, l in enumerate(log) if l.startswith("solitaire: window closed"))]
wx, wy = window_pos(upto, "solitaire")
def load(name):
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    def at(x, y):
        o = ((wy + TITLE_H + y) * w + wx + x) * 3
        return tuple(px[o:o + 3])
    return at
COL = lambda i: 7 + 59 * i
TOP_Y, TAB_Y = 38, 118
WHITE, SLOT, BACK, BACK_LINE = (255, 255, 255), (16, 88, 52), (38, 84, 170), (88, 136, 218)
# the pips' middles (solitaire.c: columns 15, 26, 37; rows 0 to 12 from y 19 to 52)
PIPS = {2: ["M0", "M12"], 3: ["M0", "M6", "M12"], 4: ["L0", "R0", "L12", "R12"], 5: ["L0", "R0", "M6", "L12", "R12"],
        6: ["L0", "R0", "L6", "R6", "L12", "R12"], 7: ["L0", "R0", "M3", "L6", "R6", "L12", "R12"],
        8: ["L0", "R0", "M3", "L6", "R6", "M9", "L12", "R12"],
        9: ["L0", "R0", "L4", "R4", "M6", "L8", "R8", "L12", "R12"],
        10: ["L0", "R0", "M2", "L4", "R4", "L8", "R8", "M10", "L12", "R12"]}
spot = lambda p: ({"L": 15, "M": 26, "R": 37}[p[0]], 19 + int(p[1:]) * 33 // 12)
SPOTS = {spot(p) for ps in PIPS.values() for p in ps}
def is_ink(c, card):
    return (c[0] > 150 and c[1] < 110 and c[2] < 110) if red(card) else max(c) < 110
def face(at, x, y, card):
    """Card `card` face up at (x, y): white, its pips (or the ace's suit, or a face card's
    frame) in its color, where its rank puts them."""
    assert at(x + 26, y + 8) == WHITE, ("not a face", name(card), at(x + 26, y + 8))
    r = rank(card)
    if r > 10:
        tint = (253, 234, 234) if red(card) else (230, 236, 248)
        assert at(x + 12, y + 20) == tint, ("a face card's frame", name(card), at(x + 12, y + 20))
        return
    mine = [spot(p) for p in PIPS[r]] if r > 1 else [(26, 36)]
    for sx, sy in SPOTS | {(26, 36)}:
        d = min(max(abs(sx - mx), abs(sy - my)) for mx, my in mine)
        c = at(x + sx, y + sy)
        if d == 0:
            assert is_ink(c, card), ("no pip", name(card), (sx, sy), c)
        elif d >= 5 and not (r == 1 and abs(sx - 26) <= 12 and 24 <= sy <= 47):
            assert c == WHITE, ("a pip that should not be there", name(card), (sx, sy), c)
def down(at, x, y):
    """A face-down card at (x, y), under another 5 px lower: its back shows at y + 4."""
    c = at(x + 26, y + 4)
    assert c in (BACK, BACK_LINE), ("not a back", c)
def empty(at, x, y):
    assert at(x + 26, y + 8) == SLOT, ("not empty", at(x + 26, y + 8))
def pile(at, p, cards):
    """Tableau pile p: cards, a list of (card, face up), from the bottom; face-up ones 17 px apart."""
    y = TAB_Y
    for i, (c, up) in enumerate(cards):
        last = i == len(cards) - 1
        if not up:
            down(at, COL(p), y)
            y += 5
        elif last:
            face(at, COL(p), y, c)
        else:
            y += 17

at = load("sol-deal")
for p in range(7):
    pile(at, p, tab[p])
down(at, COL(0), TOP_Y)                  # the stock
empty(at, COL(1), TOP_Y)
for f in range(4):
    empty(at, COL(3 + f), TOP_Y)

at = load("sol-drag")                    # 8c on 9d; Jd turned up on pile 5
pile(at, 0, [(tab[0][0][0], True), (tab[4][-1][0], True)])
pile(at, 4, [(c, False) for c, u in tab[4][:-2]] + [(t5, True)])

at = load("sol-back")                    # 9c went back; 5s as it was
pile(at, 2, tab[2])
pile(at, 3, tab[3])

at = load("sol-ace")                     # 6s drawn; Ad on the first foundation, the card under it up
face(at, COL(1), TOP_Y, stock[-1])
face(at, COL(3), TOP_Y, tab[1][-1][0])
pile(at, 1, [(t2, True)])

at = load("sol-undo")                    # the ace back on pile 2, the card under it down
empty(at, COL(3), TOP_Y)
pile(at, 1, tab[1])
face(at, COL(1), TOP_Y, stock[-1])

at = load("sol-draw3")                   # Draw 3: the three fanned 16 px apart, the last drawn on top
face(at, COL(1) + 2 * 16, TOP_Y, stock[-3])

at = load("sol-won")                     # a king on each foundation, the stock and piles empty
for f in range(4):
    assert at(COL(3 + f) + 12, TOP_Y + 20) in ((253, 234, 234), (230, 236, 248)), ("no king on a foundation", f)
empty(at, COL(0), TOP_Y)
for p in range(7):
    empty(at, COL(p), TAB_Y)

# apps/solitaire/stats.txt on the card image: the file system of user/fs.c (tools/mksd.py)
card = open(os.path.join(T, "sd-test.img"), "rb").read()
part = 2048 * 512
magic, _, total_blocks, js, jb, bs, bb, ins, icount, ds, clusters = struct.unpack_from("<8s10I", card, part)
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
    for nm in path.split("/"):
        d = content(n)
        n = next(ino for ino, kind, e in (struct.unpack_from("<II56s", d, o) for o in range(0, len(d), 64))
                 if ino and e.rstrip(b"\0").decode() == nm)
    return n
stats = content(lookup("apps/solitaire/stats.txt")).decode()
assert stats == f"played 3\nwon 1\nbest {secs}\n", ("stats.txt says", stats)
print(f"ok: the deal on the screen as the seed says; a drag moved 8c and one snapped back; 6s drawn; Ad home by a double "
      f"click and a right click, undone both times; Draw 3 drew {draw3}; the game won in {total} moves "
      f"({nkeys} by the keys, {nauto} by itself) in {secs} s; stats.txt on the card: {stats.strip()!r}")
PY
echo "ok: solitaire deals from its seed, drags, draws, sends a card home, undoes, plays a game to a win, and keeps its stats"
