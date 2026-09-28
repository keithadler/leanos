/* solitaire: Klondike, the patience every desktop ships. Seven piles on the table (the
   tableau), the stock and the waste above them on the left, and four foundations on the
   right, one for each suit. Build each foundation up by suit from the ace to the king; on
   the tableau, build down in alternating colors (a red 6 on a black 7), and only a king (or
   a run from one) goes to an empty pile. A card turned face down in the tableau turns up by
   itself when the cards on it go.

   With the mouse (the window is opened with app_open_drag, so it hears a drag's moves and
   its release, and the right button):
     a drag          takes a card, or a run of cards from the tableau, the waste's top card
                     or a foundation's, to a pile it may go on: it goes to the one it covers
                     most among those; dropped anywhere else, it goes back where it was
     a click         on the stock turns its top card over onto the waste (three in Draw 3);
                     on the empty stock, turns the whole waste back over
     a double click  (or a right click) on a top card sends it to its foundation, if it can go
   The buttons at the top: New (a new deal), Undo, Draw 1 or Draw 3 (a click changes it and
   deals again) and Auto; at the right, the moves made and the time since the first.

   The keys:
     1 to 7, W       pick a tableau pile, or the waste; then 1 to 7 puts what fits on that
                     pile (the part of the run that goes there), and F or Return sends its
                     top card to its foundation (so does the same key again). Escape drops
                     the pick
     Space           the stock, as a click on it
     U or Ctrl+Z     undo, the last 200 moves
     A               auto: every card that can go to a foundation goes
     D               Draw 1 or Draw 3, and a new deal
     N               a new deal

   The stock can be gone through as many times as you like, in Draw 1 and in Draw 3 (no
   limit, as Windows plays it without Vegas scoring). Once the stock and the waste are empty
   and every card is face up, the game is won whatever you do, and it finishes by itself: the
   cards go to the foundations one at a time. A won game bounces its cards off the foundations
   for a few seconds (a key or a click stops that), then says the time and the moves.

   A game counts as played at its first move. Games played, games won and the best time (in
   seconds) are kept in apps/solitaire/stats.txt, in the program's own folder, a line each
   ("played 12"; no best line before the first win), the whole file written in one request.

   The deal: a small generator (xorshift, 32 bits, as mines has) shuffles the 52 cards
   (Fisher-Yates, from the last card down), and they are dealt as at a table: a row at a time,
   from pile 1 to 7, each row one pile shorter, the first card of each row face up; the other
   24 go to the stock, the last one dealt on top. The generator is seeded from the CPU's
   counter; for tests, a number in apps/solitaire/seed.txt seeds every deal instead (so each
   new game is the same deal, which test/solitaire.sh works out with a copy of this). Every
   deal says its seed on the serial console.

   The window's title is Klondike: a title holds at most 8 letters, and Solitaire has 9.

   Memory. The window, 420 x 390 pixels of 4 bytes, is 160 pages of the spare run, from
   APP_WIN_OFFSET up to the file server's buffer (as in mines). The cards are drawn as they
   are needed, with nothing kept but the suits' shapes (four, at two sizes, worked out once
   at the start with 16 samples a pixel). The game (the 13 piles, 200 moves of undo) takes
   under 5 KiB of the 32 of data. */
#include "../ui.h"
#include "../fs.h"

/* The game runs when a key or a click comes: compiled for size, but for the drawing, the
   part that loops over pixels (as calendar and clock do). */
#define COLD __attribute__((cold, minsize))

#define WW 420
#define WH 390
_Static_assert((WW * WH * 4 + 4095) / 4096 <= FS_BUF_OFFSET - APP_WIN_OFFSET,
               "the window's pixels would run into the file server's buffer");
_Static_assert(FS_BUF_OFFSET - APP_WIN_OFFSET <= APP_WIN_PAGES, "more pages than a window may use");

#define BAR_H 30                 /* the buttons, the moves and the time */
#define CW 52                    /* a card */
#define CH 72
#define RADIUS 5
#define COL(i) (7 + (i) * 59)    /* the seven columns */
#define TOP_Y 38                 /* the stock, the waste and the foundations */
#define TAB_Y 118                /* the tableau */
#define TAB_END (WH - 6)
#define DOWN_DY 5                /* a face-down card under another shows this much */
#define UP_DY 17                 /* a face-up one: its rank and suit (less, on a long pile) */
#define FAN 16                   /* Draw 3's waste: its top three, fanned */
#define SMALL 9                  /* the suits in the corners, and the pips */
#define BIG 24                   /* an ace's suit */
#define NUNDO 200
#define DOUBLE_MS 500            /* a second press on a card within this: a double click */
#define DRAG_PX 3                /* a press that moves this far is a drag */
#define FRAMES 90                /* the win's bouncing cards: at most this many frames */
#define STEPS 10                 /* a card's places a frame (each drawn: its trail) */

#define STATS_FILE "apps/solitaire/stats.txt"
#define SEED_FILE "apps/solitaire/seed.txt"

/* The piles: the stock, the waste, the four foundations, the seven of the tableau. */
enum { STOCK = 0, WASTE = 1, FOUND = 2, TAB = 6, NPILE = 13 };
/* A card: 0 to 51, its suit c / 13 (clubs, diamonds, hearts, spades), its rank c % 13 + 1;
   in a pile, UP marks it face up. */
#define UP 0x40
#define CARD(e) ((e) & 0x3f)

/* The top bar's buttons. */
enum { B_NEW, B_UNDO, B_DRAW, B_AUTO, NBUTTON };
static const int button_x[NBUTTON] = {7, 57, 113, 179};
static const int button_w[NBUTTON] = {44, 50, 60, 46};
#define BUTTON_Y 5
#define BUTTON_H 20

/* What undo keeps of a move: MOVE takes the top n cards of `from` to `to` as they are (and
   `flip`: the card it uncovered was turned up); DEAL takes them one at a time, each turned
   to `flip` (1 up, 0 down): the stock onto the waste, or the waste back onto the stock.
   `chain`: undone with the one before it (auto's moves are undone together). */
enum { MOVE, DEAL };
struct rec { unsigned char kind, from, to, n, flip, chain; };

struct game {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    unsigned char card[NPILE][52], n[NPILE];
    int draw3;
    unsigned rng, seed, fixed_seed;            /* fixed_seed: from seed.txt, for tests (0: none) */
    int moves, won, shown;                     /* shown: the win's panel is up */
    u64 start, secs;                           /* the first move (ms, 0: none yet), the seconds shown */
    struct rec undo[NUNDO];
    int ut, un;                                /* undo: the next slot, how many kept */
    int held, dragging, hp, hi;                /* a press on a card: its pile and where in it */
    int hx, hy, px, py, gx, gy;                /* where it was, the pointer, the grab in the card */
    u64 last_ms;                               /* the last press on a card, for a double click */
    int last_p, last_i;
    int sel;                                   /* the keys' pick: a pile, or -1 */
    unsigned played, wins, best;               /* stats.txt; best in seconds, 0: none yet */
    unsigned char small[4][SMALL * SMALL], big[4][BIG * BIG];   /* the suits' coverage */
};
_Static_assert(sizeof(struct game) <= 8 * 4096, "solitaire's state must fit in its 8 data pages");

#define FELT rgb(24, 112, 66)
#define FELT_DARK rgb(16, 88, 52)
#define BAR rgb(12, 64, 38)
#define FACE rgb(255, 255, 255)
#define EDGE rgb(118, 124, 136)
#define RED rgb(204, 30, 44)
#define BLACK rgb(26, 28, 36)
#define BACK rgb(38, 84, 170)
#define BACK_LINE rgb(88, 136, 218)
#define PICK rgb(255, 196, 40)

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static int suit(int c) { return c / 13; }
static int rank(int c) { return c % 13 + 1; }
static int is_red(int c) { return suit(c) == 1 || suit(c) == 2; }
static unsigned ink(int c) { return is_red(c) ? RED : BLACK; }

static const char *const rank_name[14] = {"", "A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"};

COLD static void put_card(struct line *l, int c) {
    put_s(l, rank_name[rank(c)]);
    char s[2] = {"cdhs"[suit(c)], 0};
    put_s(l, s);
}

/* t1 to t7, f1 to f4, the stock, the waste */
COLD static void put_pile(struct line *l, int p) {
    if (p == STOCK) put_s(l, "stock");
    else if (p == WASTE) put_s(l, "waste");
    else {
        put_s(l, p < TAB ? "f" : "t");
        put_dec(l, (u64)(p < TAB ? p - FOUND + 1 : p - TAB + 1));
    }
}

static int top(struct game *g, int p) { return CARD(g->card[p][g->n[p] - 1]); }

/* ---- the suits ---- */

COLD static int circle(int u, int v, int cx, int cy, int r) { return (u - cx) * (u - cx) + (v - cy) * (v - cy) <= r * r; }
static int iabs(int v) { return v < 0 ? -v : v; }

/* The stem of a spade or a club, widening to its foot. */
COLD static int stem(int u, int v) {
    if (v < 520 || v > 1000) return 0;
    int w = v < 640 ? 44 : 44 + (v - 640) * 200 / 360;
    return iabs(u - 512) <= w;
}

/* Whether (u, v), each 0 to 1023 across the suit's square, is inside it. */
COLD static int in_suit(int s, int u, int v) {
    switch (s) {
    case 0:                                          /* clubs: three leaves and a stem */
        return circle(u, v, 512, 250, 215) || circle(u, v, 272, 590, 215) || circle(u, v, 752, 590, 215) ||
               circle(u, v, 512, 530, 130) || stem(u, v);
    case 1:                                          /* diamonds */
        return iabs(u - 512) * 500 + iabs(v - 512) * 410 <= 410 * 500;
    case 2:                                          /* hearts: two lobes and a point */
        return circle(u, v, 290, 330, 250) || circle(u, v, 734, 330, 250) ||
               (v >= 330 && v <= 980 && iabs(u - 512) * 650 <= 470 * (980 - v));
    default:                                         /* spades: a heart upside down, and a stem */
        return circle(u, v, 296, 560, 232) || circle(u, v, 728, 560, 232) ||
               (v >= 20 && v <= 560 && iabs(u - 512) * 540 <= 450 * (v - 20)) || stem(u, v);
    }
}

/* The suit's coverage at `size` pixels a side, 0 to 255: 4 x 4 samples a pixel. */
COLD static void make_suit(unsigned char *m, int s, int size) {
    for (int j = 0; j < size; j++)
        for (int i = 0; i < size; i++) {
            int k = 0;
            for (int b = 0; b < 4; b++)
                for (int a = 0; a < 4; a++) k += in_suit(s, ((i * 4 + a) * 2 + 1) * 1024 / (size * 8),
                                                         ((j * 4 + b) * 2 + 1) * 1024 / (size * 8));
            m[j * size + i] = (unsigned char)(k * 255 / 16);
        }
}

/* A suit's coverage `m` at (x, y), upside down if `flip`. */
static void stamp(struct surface *s, int x, int y, const unsigned char *m, int size, unsigned c, int flip) {
    for (int j = 0; j < size; j++)
        for (int i = 0; i < size; i++) blend(s, x + i, y + j, c, m[(flip ? size - 1 - j : j) * size + i]);
}

/* ---- drawing a card ---- */

/* The pips of 2 to 10: a column (0 left, 1 middle, 2 right) and a row, 0 to 12 down the
   card, in a byte each (column * 16 + row); those below the middle upside down. */
static const unsigned char pips[11][10] = {
    [2] = {0x10, 0x1c},
    [3] = {0x10, 0x16, 0x1c},
    [4] = {0x00, 0x20, 0x0c, 0x2c},
    [5] = {0x00, 0x20, 0x16, 0x0c, 0x2c},
    [6] = {0x00, 0x20, 0x06, 0x26, 0x0c, 0x2c},
    [7] = {0x00, 0x20, 0x13, 0x06, 0x26, 0x0c, 0x2c},
    [8] = {0x00, 0x20, 0x13, 0x06, 0x26, 0x19, 0x0c, 0x2c},
    [9] = {0x00, 0x20, 0x04, 0x24, 0x16, 0x08, 0x28, 0x0c, 0x2c},
    [10] = {0x00, 0x20, 0x12, 0x04, 0x24, 0x08, 0x28, 0x1a, 0x0c, 0x2c},
};
static const int pip_col[3] = {15, 26, 37};    /* the pips' middles, in the card */
#define PIP_Y0 19
#define PIP_Y1 52

/* The rank in the top left corner, and the same turned half round in the bottom right: drawn
   once into a small coverage buffer, then put down both ways. */
static void corners(struct game *g, struct surface *s, int x, int y, int c) {
    unsigned buf[20 * 17];
    struct surface t = surface_of(buf, 20, 17);
    fill(&t, 0, 0, 20, 17, 0);
    font_text(&t, &g->ui.bold, 1, 15, rank_name[rank(c)], 0xffffff);
    unsigned k = ink(c);
    for (int j = 0; j < 17; j++)
        for (int i = 0; i < 20; i++) {
            unsigned a = buf[j * 20 + i] & 0xff;
            if (!a) continue;
            blend(s, x + 3 + i, y + j, k, a);
            blend(s, x + CW - 4 - i, y + CH - 1 - j, k, a);
        }
    const unsigned char *m = g->small[suit(c)];
    stamp(s, x + CW - 4 - SMALL, y + 5, m, SMALL, k, 0);
    stamp(s, x + 4, y + CH - 5 - SMALL, m, SMALL, k, 1);
}

static void card_back(struct surface *s, int x, int y) {
    round_rect(s, x + 4, y + 4, CW - 8, CH - 8, 3, BACK, 255);
    /* a lattice of light lines, clear of the rounded corners */
    for (int j = 2; j < CH - 10; j++)
        for (int i = 2; i < CW - 10; i++)
            if ((i + j) % 7 == 0 || (i - j + 700) % 7 == 0) blend(s, x + 4 + i, y + 4 + j, BACK_LINE, 255);
}

static void draw_card(struct game *g, int x, int y, int e) {
    struct surface *s = &g->win;
    round_rect(s, x, y, CW, CH, RADIUS, EDGE, 255);
    round_rect(s, x + 1, y + 1, CW - 2, CH - 2, RADIUS - 1, FACE, 255);
    if (!(e & UP)) {
        card_back(s, x, y);
        return;
    }
    int c = CARD(e), r = rank(c);
    unsigned k = ink(c);
    corners(g, s, x, y, c);
    if (r == 1) stamp(s, x + (CW - BIG) / 2, y + (CH - BIG) / 2, g->big[suit(c)], BIG, k, 0);
    else if (r <= 10) {
        for (int i = 0; i < r; i++) {
            int p = pips[r][i], row = p & 15;
            int py = PIP_Y0 + row * (PIP_Y1 - PIP_Y0) / 12;
            stamp(s, x + pip_col[p >> 4] - SMALL / 2, y + py - SMALL / 2, g->small[suit(c)], SMALL, k, row > 6);
        }
    } else {                                           /* J, Q, K: a framed letter and the suit */
        unsigned tint = is_red(c) ? rgb(253, 234, 234) : rgb(230, 236, 248);
        round_rect(s, x + 9, y + 16, CW - 18, 40, 4, k, 255);
        round_rect(s, x + 10, y + 17, CW - 20, 38, 3, tint, 255);
        const struct font *f = &g->ui.title;
        const char *t = rank_name[r];
        font_text(s, f, x + (CW - font_width(f, t)) / 2, y + 42, t, k);
        stamp(s, x + (CW - SMALL) / 2, y + 45, g->small[suit(c)], SMALL, k, 0);
    }
}

/* An empty place: darker felt, and a hint of what goes there. */
static void slot(struct game *g, int x, int y, const char *hint) {
    struct surface *s = &g->win;
    round_rect(s, x, y, CW, CH, RADIUS, rgb(10, 60, 34), 110);
    round_rect(s, x + 2, y + 2, CW - 4, CH - 4, RADIUS - 1, FELT_DARK, 255);
    if (hint) {
        const struct font *f = &g->ui.title;
        font_text(s, f, x + (CW - font_width(f, hint)) / 2, y + CH / 2 + 9, hint, rgb(40, 124, 80));
    }
}

/* ---- where things are ---- */

/* How far apart the cards of tableau pile p are: face down, face up (closer on a long pile). */
static void spacing(struct game *g, int p, int *dd, int *du) {
    int n = g->n[p], nd = 0;
    while (nd < n && !(g->card[p][nd] & UP)) nd++;
    *dd = DOWN_DY;
    *du = UP_DY;
    int nu = n - nd, room = TAB_END - TAB_Y - CH - nd * DOWN_DY;
    if (nu > 1 && room < (nu - 1) * UP_DY) *du = room / (nu - 1) < 4 ? 4 : room / (nu - 1);
}

/* How many of the waste's top cards show: Draw 3 fans three. */
static int fanned(struct game *g) { return g->draw3 ? (g->n[WASTE] < 3 ? g->n[WASTE] : 3) : 1; }

/* Where card i of pile p is (or would be: i may be n, the next card's place). */
static void place(struct game *g, int p, int i, int *x, int *y) {
    if (p == STOCK) { *x = COL(0); *y = TOP_Y; }
    else if (p == WASTE) {
        int k = g->draw3 ? i - (g->n[WASTE] - fanned(g)) : 0;
        *x = COL(1) + (k > 0 ? k * FAN : 0);
        *y = TOP_Y;
    } else if (p < TAB) { *x = COL(3 + p - FOUND); *y = TOP_Y; }
    else {
        int dd, du, yy = TAB_Y;
        spacing(g, p, &dd, &du);
        for (int j = 0; j < i && j < g->n[p]; j++) yy += g->card[p][j] & UP ? du : dd;
        *x = COL(p - TAB);
        *y = yy;
    }
}

/* Which pile, and which of its cards, is at (x, y): 0 if none. i: the card, or -1 on an
   empty place. */
static int hit(struct game *g, int x, int y, int *pile, int *idx) {
    for (int p = 0; p < NPILE; p++) {
        int n = g->n[p];
        for (int i = n - 1; i >= (p >= TAB ? 0 : n - 1) && i >= 0; i--) {
            int cx, cy;
            place(g, p, i, &cx, &cy);
            if (x >= cx && x < cx + CW && y >= cy && y < cy + CH) {
                *pile = p;
                *idx = i;
                return 1;
            }
        }
        int cx, cy;
        place(g, p, 0, &cx, &cy);
        if (!n && x >= cx && x < cx + CW && y >= cy && y < cy + CH) {
            *pile = p;
            *idx = -1;
            return 1;
        }
    }
    return 0;
}

/* ---- drawing it all ---- */

static void button(struct game *g, int b, const char *label, int on) {
    struct surface *s = &g->win;
    int x = button_x[b], w = button_w[b];
    round_rect(s, x, BUTTON_Y, w, BUTTON_H, 7, on ? rgb(64, 150, 100) : rgb(34, 104, 68), 255);
    const struct font *f = &g->ui.small_bold;
    font_text(s, f, x + (w - font_width(f, label)) / 2, BUTTON_Y + 14, label, rgb(236, 246, 238));
}

static void put_time(struct line *t, u64 s) {
    put_dec(t, s / 60);
    put_s(t, s % 60 < 10 ? ":0" : ":");
    put_dec(t, s % 60);
}

static void draw_bar(struct game *g) {
    struct surface *s = &g->win;
    fill(s, 0, 0, WW, BAR_H, BAR);
    button(g, B_NEW, "New", 0);
    button(g, B_UNDO, "Undo", 0);
    button(g, B_DRAW, g->draw3 ? "Draw 3" : "Draw 1", g->draw3);
    button(g, B_AUTO, "Auto", 0);
    struct line t = {.n = 0};
    put_s(&t, "Moves ");
    put_dec(&t, (u64)g->moves);
    put_s(&t, "   ");
    put_time(&t, g->secs);
    t.b[t.n] = 0;
    const struct font *f = &g->ui.small_bold;
    font_text(s, f, WW - 8 - font_width(f, t.b), BUTTON_Y + 14, t.b, rgb(220, 238, 226));
}

/* What the keys have picked: a frame round the cards that would go. */
static void draw_pick(struct game *g) {
    int p = g->sel;
    if (p < 0 || !g->n[p]) return;
    int i = g->n[p] - 1;
    if (p >= TAB) while (i > 0 && (g->card[p][i - 1] & UP)) i--;
    int x0, y0, x1, y1;
    place(g, p, i, &x0, &y0);
    place(g, p, g->n[p] - 1, &x1, &y1);
    struct surface *s = &g->win;
    int w = x1 - x0 + CW + 4, h = y1 - y0 + CH + 4;
    fill(s, x0 - 2, y0 - 2, w, 2, PICK);
    fill(s, x0 - 2, y0 + h - 4, w, 2, PICK);
    fill(s, x0 - 2, y0 - 2, 2, h, PICK);
    fill(s, x0 + w - 4, y0 - 2, 2, h, PICK);
}

static void draw_won(struct game *g) {
    struct surface *s = &g->win;
    int w = 260, h = 74, x = (WW - w) / 2, y = 200;
    round_rect(s, x, y, w, h, 12, rgb(250, 250, 246), 240);
    const struct font *f = &g->ui.medium;
    font_text(s, f, x + (w - font_width(f, "You won!")) / 2, y + 28, "You won!", rgb(20, 90, 50));
    struct line t = {.n = 0};
    put_time(&t, g->secs);
    put_s(&t, ", ");
    put_dec(&t, (u64)g->moves);
    put_s(&t, " moves. N deals again.");
    t.b[t.n] = 0;
    f = &g->ui.small;
    font_text(s, f, x + (w - font_width(f, t.b)) / 2, y + 52, t.b, rgb(60, 66, 74));
}

static void draw(struct game *g) {
    struct surface *s = &g->win;
    gradient(s, 0, BAR_H, WW, WH - BAR_H, FELT, FELT_DARK);
    draw_bar(g);
    int moving = g->held && g->dragging;
    for (int p = 0; p < NPILE; p++) {
        int n = g->n[p], from = 0;
        if (moving && p == g->hp) n = g->hi;            /* the cards being dragged: drawn last */
        if (p == WASTE) from = g->n[WASTE] - fanned(g) - 1;   /* the fan, and the card under it */
        else if (p < TAB) from = n - 2;
        if (from < 0) from = 0;
        int x, y;
        place(g, p, 0, &x, &y);
        if (!n) {
            if (p == STOCK) slot(g, x, y, g->n[WASTE] ? "O" : 0);
            else if (p == WASTE) slot(g, x, y, 0);
            else slot(g, x, y, p < TAB ? "A" : "K");
            continue;
        }
        if (p == STOCK) {
            if (n > 1) draw_card(g, x + 2, y + 2, 0);   /* a card under it: there are more */
            draw_card(g, x, y, 0);
            continue;
        }
        for (int i = from; i < n; i++) {
            place(g, p, i, &x, &y);
            draw_card(g, x, y, g->card[p][i]);
        }
    }
    if (!moving) draw_pick(g);
    if (moving) {
        int x = g->px - g->gx, y = g->py - g->gy;
        for (int i = g->hi; i < g->n[g->hp]; i++, y += UP_DY) {
            round_rect(s, x + 2, y + 3, CW, CH, RADIUS, 0, 60);
            draw_card(g, x, y, g->card[g->hp][i]);
        }
    }
    if (g->won && g->shown) draw_won(g);
}

/* ---- the rules ---- */

/* Whether card c may go on pile p (as the bottom of n cards). */
static int fits(struct game *g, int c, int n, int p) {
    if (p >= TAB) {
        if (!g->n[p]) return rank(c) == 13;
        int d = top(g, p);
        return rank(d) == rank(c) + 1 && is_red(d) != is_red(c);
    }
    if (p >= FOUND && n == 1) {
        if (!g->n[p]) return rank(c) == 1;
        int d = top(g, p);
        return suit(d) == suit(c) && rank(d) + 1 == rank(c);
    }
    return 0;
}

/* Whether the cards of tableau pile p from i up are a run: face up, down in alternating colors. */
static int is_run(struct game *g, int p, int i) {
    for (int j = i; j < g->n[p]; j++) {
        if (!(g->card[p][j] & UP)) return 0;
        if (j > i) {
            int a = CARD(g->card[p][j - 1]), b = CARD(g->card[p][j]);
            if (rank(a) != rank(b) + 1 || is_red(a) == is_red(b)) return 0;
        }
    }
    return 1;
}

/* The foundation card c goes to: its suit's, or for an ace the first empty one; -1 if none. */
static int foundation_for(struct game *g, int c) {
    for (int f = FOUND; f < TAB; f++)
        if (g->n[f] && fits(g, c, 1, f)) return f;
    for (int f = FOUND; f < TAB; f++)
        if (!g->n[f] && rank(c) == 1) return f;
    return -1;
}

static int finished(struct game *g) {
    for (int f = FOUND; f < TAB; f++) if (g->n[f] != 13) return 0;
    return 1;
}

/* The stock and the waste empty, every card face up: the rest goes by itself. */
static int finishable(struct game *g) {
    if (g->n[STOCK] || g->n[WASTE]) return 0;
    for (int p = TAB; p < NPILE; p++)
        for (int i = 0; i < g->n[p]; i++) if (!(g->card[p][i] & UP)) return 0;
    return 1;
}

/* ---- the moves, and undo ---- */

static void move_cards(struct game *g, int from, int to, int n) {
    int base = g->n[from] - n;
    for (int i = 0; i < n; i++) g->card[to][g->n[to]++] = g->card[from][base + i];
    g->n[from] = (unsigned char)base;
}

static void deal_cards(struct game *g, int from, int to, int n, int up) {
    for (int i = 0; i < n; i++) {
        int c = CARD(g->card[from][--g->n[from]]);
        g->card[to][g->n[to]++] = (unsigned char)(c | (up ? UP : 0));
    }
}

COLD static void save_stats(struct game *g, struct line *l) {
    struct line f = {.n = 0};
    put_s(&f, "played ");
    put_dec(&f, g->played);
    put_s(&f, "\nwon ");
    put_dec(&f, g->wins);
    put_s(&f, "\n");
    if (g->best) {
        put_s(&f, "best ");
        put_dec(&f, g->best);
        put_s(&f, "\n");
    }
    u64 st = fs_write(&g->fs, STATS_FILE, f.b, f.n);
    put_s(l, "solitaire: saved " STATS_FILE);
    put_s(l, st == FS_OK ? " -> ok" : " -> refused");
    say(l);
}

/* A move made: kept for undo (the oldest goes when there are NUNDO), counted, and the first
   of a game starts the clock and counts the game as played. */
COLD static void made(struct game *g, struct line *l, struct rec r) {
    g->undo[g->ut] = r;
    g->ut = (g->ut + 1) % NUNDO;
    if (g->un < NUNDO) g->un++;
    g->moves++;
    if (!g->start) {
        g->start = millis();
        g->secs = 0;
        g->played++;
        save_stats(g, l);
    }
}

COLD static void put_move(struct line *l, struct game *g) {
    put_s(l, "solitaire: move ");
    put_dec(l, (u64)g->moves);
    put_s(l, ": ");
}

/* n cards from `from` to `to`, and the card under them turned up if it was down. */
COLD static void do_move(struct game *g, struct line *l, int from, int to, int n, int chain) {
    int c = CARD(g->card[from][g->n[from] - n]);
    move_cards(g, from, to, n);
    struct rec r = {MOVE, (unsigned char)from, (unsigned char)to, (unsigned char)n, 0, (unsigned char)chain};
    if (from >= TAB && g->n[from] && !(g->card[from][g->n[from] - 1] & UP)) {
        g->card[from][g->n[from] - 1] |= UP;
        r.flip = 1;
    }
    made(g, l, r);
    put_move(l, g);
    put_card(l, c);
    if (n > 1) {
        put_s(l, "+");
        put_dec(l, (u64)(n - 1));
    }
    put_s(l, " ");
    put_pile(l, from);
    put_s(l, " -> ");
    put_pile(l, to);
    if (r.flip) {
        put_s(l, ", turned up ");
        put_card(l, top(g, from));
    }
    say(l);
}

/* A click on the stock: its top card (three in Draw 3) onto the waste, or, empty, the waste
   back onto it. */
COLD static void stock(struct game *g, struct line *l) {
    int n = g->n[STOCK];
    if (!n && !g->n[WASTE]) return;
    struct rec r = {DEAL, STOCK, WASTE, 0, 1, 0};
    if (n) {
        int k = g->draw3 && n > 3 ? 3 : g->draw3 ? n : 1;
        deal_cards(g, STOCK, WASTE, k, 1);
        r.n = (unsigned char)k;
        made(g, l, r);
        put_move(l, g);
        put_s(l, "drew");
        for (int i = g->n[WASTE] - k; i < g->n[WASTE]; i++) {
            put_s(l, " ");
            put_card(l, CARD(g->card[WASTE][i]));
        }
    } else {
        r = (struct rec){DEAL, WASTE, STOCK, g->n[WASTE], 0, 0};
        deal_cards(g, WASTE, STOCK, g->n[WASTE], 0);
        made(g, l, r);
        put_move(l, g);
        put_s(l, "turned the waste over");
    }
    put_s(l, " (stock ");
    put_dec(l, g->n[STOCK]);
    put_s(l, ")");
    say(l);
}

COLD static void undo(struct game *g, struct line *l) {
    if (g->won) return;
    if (!g->un) {
        put_s(l, "solitaire: nothing to undo");
        say(l);
        return;
    }
    int last = g->moves, chain;
    do {
        g->ut = (g->ut + NUNDO - 1) % NUNDO;
        g->un--;
        struct rec r = g->undo[g->ut];
        if (r.kind == MOVE) {
            if (r.flip) g->card[r.from][g->n[r.from] - 1] &= (unsigned char)~UP;
            move_cards(g, r.to, r.from, r.n);
        } else deal_cards(g, r.to, r.from, r.n, !r.flip);
        g->moves--;
        chain = r.chain;
    } while (chain && g->un);
    put_s(l, "solitaire: undid move ");
    if (last - g->moves > 1) {
        put_dec(l, (u64)g->moves + 1);
        put_s(l, " to ");
    }
    put_dec(l, (u64)last);
    say(l);
}

/* The top card of pile p to its foundation, if it can go. */
COLD static int to_foundation(struct game *g, struct line *l, int p, int chain) {
    if (!g->n[p] || p == STOCK || (p >= FOUND && p < TAB)) return 0;
    int c = top(g, p), f = foundation_for(g, c);
    if (f < 0) {
        put_s(l, "solitaire: ");
        put_card(l, c);
        put_s(l, " cannot go to a foundation");
        say(l);
        return 0;
    }
    do_move(g, l, p, f, 1, chain);
    return 1;
}

/* Every card that can go to a foundation goes, the lowest first, until none can: one at a
   time on the screen if `shown`. How many went. */
COLD static int auto_play(struct game *g, struct line *l, int shown) {
    int moved = 0;
    for (;;) {
        int best = -1;
        for (int p = WASTE; p < NPILE; p++) {
            if (p >= FOUND && p < TAB) continue;
            if (!g->n[p] || foundation_for(g, top(g, p)) < 0) continue;
            if (best < 0 || rank(top(g, p)) < rank(top(g, best))) best = p;
        }
        if (best < 0) return moved;
        int c = top(g, best);
        do_move(g, l, best, foundation_for(g, c), 1, moved > 0);
        moved++;
        if (shown) {
            draw(g);
            struct event e = app_poll(1);
            if (e.kind == EV_CLOSE) exit_task();
            sleep_ms(25);
        }
    }
}

/* ---- a new game, and the end of one ---- */

static unsigned next_rand(struct game *g) {
    unsigned x = g->rng;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return g->rng = x;
}

COLD static void new_game(struct game *g, struct line *l) {
    unsigned seed = g->fixed_seed;
    if (!seed) {
        u64 t = ticks();
        seed = (unsigned)(t ^ t >> 32);
        if (!seed) seed = 1;
    }
    g->seed = g->rng = seed;
    unsigned char deck[52];
    for (int i = 0; i < 52; i++) deck[i] = (unsigned char)i;
    for (int i = 51; i > 0; i--) {
        int j = (int)(next_rand(g) % (unsigned)(i + 1));
        unsigned char t = deck[i];
        deck[i] = deck[j];
        deck[j] = t;
    }
    for (int p = 0; p < NPILE; p++) g->n[p] = 0;
    int k = 0;
    for (int row = 0; row < 7; row++)
        for (int p = row; p < 7; p++) {
            int t = TAB + p;
            g->card[t][g->n[t]++] = (unsigned char)(deck[k++] | (p == row ? UP : 0));
        }
    while (k < 52) g->card[STOCK][g->n[STOCK]++] = deck[k++];
    g->moves = g->won = g->shown = 0;
    g->start = g->secs = 0;
    g->ut = g->un = 0;
    g->held = g->dragging = 0;
    g->sel = -1;
    g->last_ms = 0;
    put_s(l, "solitaire: new game, draw ");
    put_s(l, g->draw3 ? "3" : "1");
    put_s(l, ", seed ");
    put_dec(l, seed);
    put_s(l, g->fixed_seed ? " (seed.txt)" : "");
    say(l);
    put_s(l, "solitaire: dealt");
    for (int p = TAB; p < NPILE; p++) {
        put_s(l, " ");
        put_card(l, top(g, p));
    }
    put_s(l, " face up, 24 in the stock");
    say(l);
}

/* The classic end: the cards leave the foundations one at a time, the kings first, each
   bouncing along the bottom and leaving its trail, until FRAMES frames or a key or a click. */
COLD static void celebrate(struct game *g, struct line *l) {
    int left[4] = {13, 13, 13, 13}, f = 0, frames = 0, cards = 0, skipped = 0, done = 0;
    int x = 0, y = 0, vx = 0, vy = 0, c = -1;
    g->rng = g->seed ^ 0x5eed;
    if (!g->rng) g->rng = 1;
    while (frames < FRAMES && !skipped && !done) {
        for (int step = 0; step < STEPS; step++) {
            if (c < 0) {                              /* the next card leaves its foundation */
                if (!left[f]) {
                    done = 1;
                    break;
                }
                int fx, fy;
                place(g, FOUND + f, 0, &fx, &fy);
                c = CARD(g->card[FOUND + f][--left[f]]);
                /* the foundation shows the card under it, or its empty place */
                if (left[f]) draw_card(g, fx, fy, g->card[FOUND + f][left[f] - 1] | UP);
                else slot(g, fx, fy, "A");
                x = fx * 16;
                y = fy * 16;
                vx = (int)(next_rand(g) % 64 + 48) * (next_rand(g) & 1 ? 1 : -1);
                vy = -(int)(next_rand(g) % 64);
                f = (f + 1) % 4;
                cards++;
            }
            x += vx;
            y += vy;
            vy += 10;
            if (y > (WH - CH) * 16) {
                y = (WH - CH) * 16;
                vy = -vy * 3 / 4;
            }
            draw_card(g, x / 16, y / 16, c | UP);
            if (x < -CW * 16 || x > WW * 16) c = -1;
        }
        frames++;
        struct event e = app_poll(1);
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind == EV_KEY || e.kind == EV_DOWN || e.kind == EV_RDOWN) skipped = 1;
        else sleep_ms(30);
    }
    put_s(l, skipped ? "solitaire: celebration skipped after " : "solitaire: celebration done, ");
    put_dec(l, (u64)frames);
    put_s(l, " frames, ");
    put_dec(l, (u64)cards);
    put_s(l, " cards");
    say(l);
    g->shown = 1;
}

static u64 seconds(struct game *g) { return g->start ? (millis() - g->start) / 1000 : 0; }

/* After each move: the automatic finish, and the win. */
COLD static void after(struct game *g, struct line *l) {
    if (g->won) return;
    if (!finished(g) && finishable(g)) {
        put_s(l, "solitaire: every card is face up: finishing");
        say(l);
        auto_play(g, l, 1);
    }
    if (!finished(g)) return;
    u64 ms = millis() - g->start;
    g->won = 1;
    g->secs = seconds(g);
    g->wins++;
    int best = !g->best || g->secs < g->best;
    if (best) g->best = (unsigned)g->secs;
    put_s(l, "solitaire: won in ");
    struct line t = {.n = 0};
    put_time(&t, g->secs);
    t.b[t.n] = 0;
    put_s(l, t.b);
    put_s(l, " (");
    put_dec(l, ms);
    put_s(l, " ms), ");
    put_dec(l, (u64)g->moves);
    put_s(l, best ? " moves, a new best" : " moves");
    say(l);
    save_stats(g, l);
    g->sel = -1;
    draw(g);
    celebrate(g, l);
}

/* ---- the mouse ---- */

/* The pile a drag lets go over: the one the cards cover most among those they may go on;
   -1 if none (*over: the pile covered most, whether or not they may). */
COLD static int target(struct game *g, int x, int y, int *over) {
    int c = CARD(g->card[g->hp][g->hi]), n = g->n[g->hp] - g->hi, best = -1, most = 0, any = 0;
    *over = -1;
    for (int p = FOUND; p < NPILE; p++) {
        if (p == g->hp) continue;
        int px, py;
        place(g, p, g->n[p] ? g->n[p] - 1 : 0, &px, &py);
        int w = (x < px ? x + CW - px : px + CW - x), h = (y < py ? y + CH - py : py + CH - y);
        if (w <= 0 || h <= 0) continue;
        int a = w * h;
        if (a > any) { any = a; *over = p; }
        if (a > most && fits(g, c, n, p)) { most = a; best = p; }
    }
    return best;
}

COLD static void drop(struct game *g, struct line *l) {
    int over, x = g->px - g->gx, y = g->py - g->gy;
    int to = target(g, x, y, &over), c = CARD(g->card[g->hp][g->hi]);
    if (to >= 0) {
        do_move(g, l, g->hp, to, g->n[g->hp] - g->hi, 0);
        g->last_ms = 0;
        return;
    }
    put_s(l, "solitaire: ");
    put_card(l, c);
    if (over >= 0) {
        put_s(l, " cannot go on ");
        put_pile(l, over);
        put_s(l, ";");
    }
    put_s(l, " back to ");
    put_pile(l, g->hp);
    say(l);
}

COLD static void set_draw(struct game *g, struct line *l, int three) {
    g->draw3 = three;
    new_game(g, l);
}

COLD static void press(struct game *g, struct line *l, int x, int y) {
    g->sel = -1;
    g->held = 0;
    if (y < BAR_H) {
        for (int b = 0; b < NBUTTON; b++) {
            if (x < button_x[b] || x >= button_x[b] + button_w[b] || y < BUTTON_Y || y >= BUTTON_Y + BUTTON_H) continue;
            if (b == B_NEW) new_game(g, l);
            else if (b == B_UNDO) undo(g, l);
            else if (b == B_DRAW) set_draw(g, l, !g->draw3);
            else if (!g->won && !auto_play(g, l, 1)) {
                put_s(l, "solitaire: auto: nothing can go to a foundation");
                say(l);
            }
        }
        return;
    }
    int p, i;
    if (g->won || !hit(g, x, y, &p, &i)) return;
    if (p == STOCK) {
        stock(g, l);
        return;
    }
    if (i < 0) return;
    u64 now = millis();
    if (g->last_ms && now - g->last_ms < DOUBLE_MS && g->last_p == p && g->last_i == i && i == g->n[p] - 1) {
        g->last_ms = 0;
        to_foundation(g, l, p, 0);
        return;
    }
    g->last_ms = now;
    g->last_p = p;
    g->last_i = i;
    if (!(g->card[p][i] & UP) || (p < TAB && i != g->n[p] - 1) || (p >= TAB && !is_run(g, p, i))) return;
    int cx, cy;
    place(g, p, i, &cx, &cy);
    g->held = 1;
    g->dragging = 0;
    g->hp = p;
    g->hi = i;
    g->hx = g->px = x;
    g->hy = g->py = y;
    g->gx = x - cx;
    g->gy = y - cy;
}

/* A right click on a top card: to its foundation. */
COLD static void right_click(struct game *g, struct line *l, int x, int y) {
    int p, i;
    g->sel = -1;
    if (g->won || g->held || !hit(g, x, y, &p, &i) || i < 0 || i != g->n[p] - 1) return;
    to_foundation(g, l, p, 0);
}

/* ---- the keys ---- */

/* The picked pile's cards onto tableau pile q: the part of its run that fits there. */
COLD static void put_on(struct game *g, struct line *l, int p, int q) {
    int n = g->n[p];
    if (p == q || !n) return;
    int i = n - 1;
    if (p >= TAB) {
        int first = n - 1;
        while (first > 0 && (g->card[p][first - 1] & UP)) first--;
        for (i = first; i < n && !fits(g, CARD(g->card[p][i]), n - i, q); i++) {}
    }
    if (i < n && fits(g, CARD(g->card[p][i]), n - i, q)) {
        do_move(g, l, p, q, n - i, 0);
        return;
    }
    put_s(l, "solitaire: nothing in ");
    put_pile(l, p);
    put_s(l, " goes on ");
    put_pile(l, q);
    say(l);
}

COLD static void key(struct game *g, struct line *l, u64 k) {
    g->held = g->dragging = 0;                      /* a key while the button is down ends the drag */
    if (k == 'n' || k == 'N') { new_game(g, l); return; }
    if (k == 'd' || k == 'D') { set_draw(g, l, !g->draw3); return; }
    if (g->won) return;
    if (k == 'u' || k == 'U' || k == 26) { g->sel = -1; undo(g, l); return; }
    if (k == 27) { g->sel = -1; return; }
    if (k == ' ') { g->sel = -1; stock(g, l); return; }
    if (k == 'a' || k == 'A') {
        g->sel = -1;
        if (!auto_play(g, l, 1)) {
            put_s(l, "solitaire: auto: nothing can go to a foundation");
            say(l);
        }
        return;
    }
    int p = k >= '1' && k <= '7' ? TAB + (int)(k - '1') : k == 'w' || k == 'W' ? WASTE : -1;
    int home = k == 'f' || k == 'F' || k == '\r' || k == '\n';
    if (g->sel < 0) {
        if (p >= 0 && g->n[p]) g->sel = p;
        return;
    }
    int from = g->sel;
    g->sel = -1;
    if (home || p == from) to_foundation(g, l, from, 0);
    else if (p >= TAB) put_on(g, l, from, p);
    else if (p >= 0 && g->n[p]) g->sel = p;         /* W after a pile: pick the waste instead */
}

/* ---- the files ---- */

COLD static unsigned number(const char *s) {
    unsigned v = 0;
    while (*s >= '0' && *s <= '9') v = v * 10 + (unsigned)(*s++ - '0');
    return v;
}

COLD static void read_files(struct game *g, struct line *l) {
    char b[256];
    long n = fs_read_all(&g->fs, SEED_FILE, b, sizeof b - 1);
    g->fixed_seed = 0;
    if (n > 0) {
        b[n] = 0;
        g->fixed_seed = number(b);
        if (g->fixed_seed) {
            put_s(l, "solitaire: seed ");
            put_dec(l, g->fixed_seed);
            put_s(l, " from " SEED_FILE ", for every deal");
            say(l);
        }
    }
    g->played = g->wins = g->best = 0;
    n = fs_read_all(&g->fs, STATS_FILE, b, sizeof b - 1);
    b[n > 0 ? n : 0] = 0;
    /* a line each: a name, a space, a number */
    static const char *const names[3] = {"played", "won", "best"};
    unsigned *field[3] = {&g->played, &g->wins, &g->best};
    for (const char *p = b; *p;) {
        for (int k = 0; k < 3; k++) {
            int j = 0;
            while (names[k][j] && p[j] == names[k][j]) j++;
            if (!names[k][j] && p[j] == ' ') *field[k] = number(p + j + 1);
        }
        while (*p && *p != '\n') p++;
        if (*p) p++;
    }
    put_s(l, "solitaire: stats: played ");
    put_dec(l, g->played);
    put_s(l, ", won ");
    put_dec(l, g->wins);
    put_s(l, ", best ");
    if (g->best) {
        put_dec(l, g->best);
        put_s(l, " s");
    } else put_s(l, "none");
    say(l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct game *g = (struct game *)DATA;
    struct line l = {.n = 0};
    ui_load(&g->ui, app_assets());
    g->win = app_surface(WW, WH);
    fs_init(&g->fs, SPARE_PAGE);
    for (int s = 0; s < 4; s++) {
        make_suit(g->small[s], s, SMALL);
        make_suit(g->big[s], s, BIG);
    }
    g->draw3 = 0;
    read_files(g, &l);
    new_game(g, &l);
    draw(g);
    u64 opened = app_open_drag(APP_WIN_OFFSET, WW, WH, "Klondike");
    put_s(&l, "solitaire: opened a window");
    put_s(&l, outcome(opened));
    say(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        /* while the clock runs, ask without waiting, to move it on each second */
        int timing = g->start && !g->won;
        struct event e = timing ? app_poll(dirty) : app_wait(dirty);
        int x = (int)e.a, y = (int)e.b;
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "solitaire: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (e.kind == EV_DOWN) press(g, &l, x, y);
        else if (e.kind == EV_RDOWN) right_click(g, &l, x, y);
        else if (e.kind == EV_KEY) key(g, &l, e.a);
        else if (e.kind == EV_MOVE) {
            if (!g->held) continue;
            g->px = x;
            g->py = y;
            if (!g->dragging && (iabs(x - g->hx) > DRAG_PX || iabs(y - g->hy) > DRAG_PX)) g->dragging = 1;
            if (!g->dragging) continue;
        } else if (e.kind == EV_UP) {
            if (!g->held) continue;
            g->px = x;
            g->py = y;
            if (g->dragging) drop(g, &l);
            g->held = g->dragging = 0;
        } else if (e.kind == EV_NONE) {
            if (timing && seconds(g) != g->secs) {
                g->secs = seconds(g);
                draw_bar(g);
                dirty = 1;
                continue;
            }
            sleep_ms(50);
            continue;
        } else continue;
        if (!g->held) after(g, &l);
        if (g->start && !g->won) g->secs = seconds(g);
        draw(g);
        dirty = 1;
    }
}
