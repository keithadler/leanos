/* mines: Minesweeper. Open every cell that hides no mine; a number says how many of the
   eight cells around it hide one. Three levels: Beginner (9 x 9, 10 mines), Intermediate
   (16 x 16, 40) and Expert (30 x 16, 99), chosen along the bottom of the window, where each
   shows its best time, or with the keys 1, 2 and 3.

   A click opens a cell. The first click of a game is never a mine: the mines are placed
   after it, never on it or around it, so it always opens an area. A cell with no mine
   around it opens its neighbors, and theirs, as far as that goes (a loop over a list of
   cells, not a recursion: a program's stack is 16 KiB). A click on an open number whose
   flags are all placed (as many as it says) opens the rest of its neighbors: a chord.

   Flags: the display server tells a program where a click was and nothing more (not which
   button, nor whether Shift or Control was held: user/display.c, EV_DOWN), and the USB
   driver passes on only a mouse's left button; so a click flags when the Flag button at
   the top is lit (a click on it lights it, and another puts it out), which works the same
   with any mouse or a touchscreen. At the top too: how many mines are left to flag (the
   mines less the flags), the face (a click starts a new game), and the time since the
   first click, in seconds (lib.h's millis: the CPU's counter).

   The keys: the arrows move a cursor over the cells, Space or Return opens the cell under
   it (or chords its number), F flags it or takes the flag back, N starts a new game, and 1,
   2 and 3 choose the level.

   A game is lost on a mine: every mine is shown, the one that went off on red, and a flag
   where there was no mine is crossed out. A game is won when every other cell is open:
   every mine gets its flag. A win faster than the level's best is the new best: the best
   times are kept in apps/mines/best.txt, in the program's own folder, a line a level
   ("beginner 42", seconds), the whole file written in one request.

   Where the mines go: a small generator (xorshift, 32 bits), seeded at the first click
   from the CPU's counter. For tests, a number in apps/mines/seed.txt seeds every game
   instead, so the board is known from the first click (test/mines.sh places them with a
   copy of this generator). Without that file, which nothing makes, play is as above.

   The window: the Expert board, 30 x 16 cells of 16 pixels (the classic size), is the
   largest, and the window is sized for it; with the file server's buffer after it in the
   spare run, that is 160 of the pixel pages a window may use (APP_WIN_PAGES). The smaller
   boards are drawn larger, as large as fits, up to 28 pixels a cell. */
#include "../ui.h"
#include "../fs.h"

#define MW 498
#define MH 328
#define HEAD 38              /* the bar at the top: mines left, Flag, the face, the time */
#define GRID_X 9
#define GRID_Y 40
#define GRID_W 480
#define GRID_H 256
#define FOOT_Y 300           /* the levels, each with its best time */
#define FOOT_H 24
#define CELL_MAX 28
#define COLS_MAX 30
#define ROWS_MAX 16
#define CELLS (COLS_MAX * ROWS_MAX)
_Static_assert((MW * MH * 4 + 4095) / 4096 <= FS_BUF_OFFSET - APP_WIN_OFFSET,
               "the window's pixels would run into the file server's buffer");
_Static_assert(FS_BUF_OFFSET - APP_WIN_OFFSET <= APP_WIN_PAGES, "more pages than a window may use");

/* the top bar's parts */
#define LED_W 58
#define LED_H 26
#define LED_Y 6
#define FLAG_X 75
#define FLAG_W 74
#define FACE 30
#define FACE_X (MW / 2 - FACE / 2)
#define FACE_Y 4
#define TIME_X (MW - GRID_X - LED_W)

#define BEST_FILE "apps/mines/best.txt"
#define SEED_FILE "apps/mines/seed.txt"

/* each cell: these bits */
enum { MINE = 1, OPEN = 2, FLAG = 4, BOOM = 8 };
enum { READY, PLAYING, WON, LOST };

#define BG rgb(214, 218, 226)
#define RAISED rgb(184, 192, 207)
#define LIGHT rgb(238, 241, 247)
#define SHADE rgb(126, 134, 152)
#define FLAT rgb(232, 234, 239)
#define GRIDC rgb(196, 200, 210)
#define BOOMC rgb(232, 64, 52)
#define MINEC rgb(24, 24, 30)
#define FLAGC rgb(226, 40, 36)
#define INK rgb(40, 44, 56)
#define CURSOR rgb(40, 100, 230)

static const struct level { int cols, rows, mines; const char *name, *lower; } levels[3] = {
    {9, 9, 10, "Beginner", "beginner"},
    {16, 16, 40, "Intermediate", "intermediate"},
    {30, 16, 99, "Expert", "expert"},
};

/* The numbers' classic colors: 1 blue, 2 green, 3 red, 4 navy, 5 maroon, 6 teal, 7 black,
   8 gray. */
static const unsigned number_color[9] = {0, 0x0000ff, 0x008000, 0xff0000, 0x000080,
                                         0x800000, 0x008080, 0x000000, 0x808080};

struct mines {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    int level, cols, rows, mines, cs, bx, by;   /* the board, and where it is drawn */
    unsigned char cell[CELLS], near[CELLS];     /* bits, and mines around each */
    short todo[CELLS];                          /* cells whose neighbors are still to open */
    int state, flags, opened;
    int cx, cy, cursor;                         /* the keys' cursor, and whether it is shown */
    int flag_mode;
    u64 start, secs;                            /* the first click (ms), the seconds shown */
    unsigned rng, seed;                         /* seed: from seed.txt, for tests (0: none) */
    unsigned best[3];                           /* seconds, 0: none yet */
};

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static void at(struct line *l, int x, int y) {
    put_dec(l, (u64)x);
    put_s(l, ",");
    put_dec(l, (u64)y);
}

/* ---- the game ---- */

static unsigned next_rand(struct mines *m) {
    unsigned x = m->rng;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    return m->rng = x;
}

static void new_game(struct mines *m, struct line *l) {
    for (int i = 0; i < CELLS; i++) m->cell[i] = m->near[i] = 0;
    m->state = READY;
    m->flags = m->opened = 0;
    m->secs = 0;
    if (m->cx >= m->cols) m->cx = m->cols - 1;
    if (m->cy >= m->rows) m->cy = m->rows - 1;
    const struct level *v = &levels[m->level];
    put_s(l, "mines: new game, ");
    put_s(l, v->lower);
    put_s(l, " (");
    put_dec(l, (u64)v->cols);
    put_s(l, "x");
    put_dec(l, (u64)v->rows);
    put_s(l, ", ");
    put_dec(l, (u64)v->mines);
    put_s(l, " mines)");
    say(l);
}

static void set_level(struct mines *m, struct line *l, int k) {
    const struct level *v = &levels[k];
    m->level = k;
    m->cols = v->cols;
    m->rows = v->rows;
    m->mines = v->mines;
    int a = GRID_W / m->cols, b = GRID_H / m->rows;
    m->cs = a < b ? a : b;
    if (m->cs > CELL_MAX) m->cs = CELL_MAX;
    m->bx = (MW - m->cols * m->cs) / 2;
    m->by = GRID_Y + (GRID_H - m->rows * m->cs) / 2;
    new_game(m, l);
}

/* The mines, placed after the first click, at (fx, fy): never there nor next to it. */
static void place(struct mines *m, struct line *l, int fx, int fy) {
    unsigned seed = m->seed;
    if (!seed) {
        u64 t = ticks();
        seed = (unsigned)(t ^ t >> 32);
        if (!seed) seed = 1;
    }
    m->rng = seed;
    int n = m->cols * m->rows;
    for (int placed = 0; placed < m->mines;) {
        int i = (int)(next_rand(m) % (unsigned)n), x = i % m->cols, y = i / m->cols;
        if (m->cell[i] & MINE) continue;
        if (x >= fx - 1 && x <= fx + 1 && y >= fy - 1 && y <= fy + 1) continue;
        m->cell[i] |= MINE;
        placed++;
    }
    for (int y = 0; y < m->rows; y++)
        for (int x = 0; x < m->cols; x++) {
            int k = 0;
            for (int dy = -1; dy <= 1; dy++)
                for (int dx = -1; dx <= 1; dx++) {
                    int ax = x + dx, ay = y + dy;
                    if (ax >= 0 && ay >= 0 && ax < m->cols && ay < m->rows) k += m->cell[ay * m->cols + ax] & MINE;
                }
            m->near[y * m->cols + x] = (unsigned char)k;
        }
    m->state = PLAYING;
    m->start = millis();
    m->secs = 1;
    put_s(l, "mines: mines placed after the first click at ");
    at(l, fx, fy);
    put_s(l, " (seed ");
    put_dec(l, seed);
    put_s(l, m->seed ? ", from seed.txt)" : ")");
    say(l);
}

/* Open cell i, and, from each cell with no mine around it, its neighbors: a list of cells
   still to spread from, each on it at most once (it is opened as it goes on). Returns how
   many opened. */
static int flood(struct mines *m, int i) {
    int n = 1, top = 0;
    m->cell[i] |= OPEN;
    m->todo[top++] = (short)i;
    while (top) {
        int j = m->todo[--top];
        if (m->near[j]) continue;
        int x = j % m->cols, y = j / m->cols;
        for (int dy = -1; dy <= 1; dy++)
            for (int dx = -1; dx <= 1; dx++) {
                int ax = x + dx, ay = y + dy;
                if (ax < 0 || ay < 0 || ax >= m->cols || ay >= m->rows) continue;
                int k = ay * m->cols + ax;
                if (m->cell[k] & (OPEN | FLAG | MINE)) continue;
                m->cell[k] |= OPEN;
                n++;
                m->todo[top++] = (short)k;
            }
    }
    m->opened += n;
    return n;
}

static u64 seconds(struct mines *m) {
    u64 s = (millis() - m->start) / 1000 + 1;       /* 1 from the first click, as the classic */
    return s > 999 ? 999 : s;
}

static void save_best(struct mines *m, struct line *l) {
    struct line f = {.n = 0};
    for (int k = 0; k < 3; k++) {
        if (!m->best[k]) continue;
        put_s(&f, levels[k].lower);
        put_s(&f, " ");
        put_dec(&f, m->best[k]);
        put_s(&f, "\n");
    }
    u64 st = fs_write(&m->fs, BEST_FILE, f.b, f.n);
    put_s(l, "mines: saved " BEST_FILE);
    put_s(l, st == FS_OK ? " -> ok" : " -> refused");
    say(l);
}

static void lose(struct mines *m, struct line *l, int x, int y) {
    m->state = LOST;
    m->secs = seconds(m);
    put_s(l, "mines: lost at ");
    at(l, x, y);
    put_s(l, " after ");
    put_dec(l, m->secs);
    put_s(l, " s");
    say(l);
}

/* Every other cell open: won. Every mine gets its flag, and a best time is kept. */
static void check_won(struct mines *m, struct line *l) {
    if (m->state != PLAYING || m->opened != m->cols * m->rows - m->mines) return;
    u64 ms = millis() - m->start;
    m->state = WON;
    m->secs = seconds(m);
    for (int i = 0; i < m->cols * m->rows; i++) if (m->cell[i] & MINE) m->cell[i] |= FLAG;
    m->flags = m->mines;
    int best = !m->best[m->level] || m->secs < m->best[m->level];
    put_s(l, "mines: won ");
    put_s(l, levels[m->level].lower);
    put_s(l, " in ");
    put_dec(l, m->secs);
    put_s(l, " s (");
    put_dec(l, ms);
    put_s(l, best ? " ms), a new best" : " ms)");
    say(l);
    if (best) {
        m->best[m->level] = (unsigned)m->secs;
        save_best(m, l);
    }
}

/* Open cell (x, y): the first click places the mines; a mine loses. */
static void reveal(struct mines *m, struct line *l, int x, int y) {
    int i = y * m->cols + x;
    if (m->cell[i] & (OPEN | FLAG)) return;
    if (m->state == READY) place(m, l, x, y);
    if (m->cell[i] & MINE) {
        m->cell[i] |= OPEN | BOOM;
        lose(m, l, x, y);
        return;
    }
    int n = flood(m, i);
    put_s(l, "mines: opened ");
    put_dec(l, (u64)n);
    put_s(l, n == 1 ? " cell at " : " cells at ");
    at(l, x, y);
    say(l);
    check_won(m, l);
}

/* A click on an open number with as many flags around it: the rest of its neighbors open. */
static void chord(struct mines *m, struct line *l, int x, int y) {
    int i = y * m->cols + x, flags = 0, n = 0, boom = 0;
    if (!m->near[i]) return;
    for (int pass = 0; pass < 2; pass++)
        for (int dy = -1; dy <= 1; dy++)
            for (int dx = -1; dx <= 1; dx++) {
                int ax = x + dx, ay = y + dy;
                if (ax < 0 || ay < 0 || ax >= m->cols || ay >= m->rows) continue;
                int k = ay * m->cols + ax;
                if (pass == 0) { flags += (m->cell[k] & FLAG) != 0; continue; }
                if (flags != m->near[i] || (m->cell[k] & (OPEN | FLAG))) continue;
                if (m->cell[k] & MINE) { m->cell[k] |= OPEN | BOOM; boom = 1; }
                else n += flood(m, k);
            }
    if (flags != m->near[i]) return;
    put_s(l, "mines: chord at ");
    at(l, x, y);
    put_s(l, " opened ");
    put_dec(l, (u64)n);
    put_s(l, n == 1 ? " cell" : " cells");
    say(l);
    if (boom) lose(m, l, x, y);
    else check_won(m, l);
}

static void toggle_flag(struct mines *m, struct line *l, int x, int y) {
    int i = y * m->cols + x;
    if (m->cell[i] & OPEN) return;
    m->cell[i] ^= FLAG;
    m->flags += m->cell[i] & FLAG ? 1 : -1;
    put_s(l, m->cell[i] & FLAG ? "mines: flagged " : "mines: unflagged ");
    at(l, x, y);
    put_s(l, " (");
    put_dec(l, (u64)(m->mines > m->flags ? m->mines - m->flags : 0));
    put_s(l, " left)");
    say(l);
}

/* What a click, or Space, does at (x, y): open it, chord it, or (flag) flag it. */
static void act(struct mines *m, struct line *l, int x, int y, int flag) {
    m->cx = x;
    m->cy = y;
    if (m->state == WON || m->state == LOST) return;
    if (m->cell[y * m->cols + x] & OPEN) chord(m, l, x, y);
    else if (flag) toggle_flag(m, l, x, y);
    else reveal(m, l, x, y);
}

static void flag_mode(struct mines *m, struct line *l) {
    m->flag_mode = !m->flag_mode;
    put_s(l, m->flag_mode ? "mines: flag mode on" : "mines: flag mode off");
    say(l);
}

/* ---- drawing ---- */

static void mine_at(struct surface *s, int x, int y, int cs) {
    int cx = x + cs / 2, cy = y + cs / 2, r = cs * 3 / 10, sp = r + cs / 8;
    thick_line(s, (cx - sp) * 16 + 8, cy * 16 + 8, (cx + sp) * 16 + 8, cy * 16 + 8, 2, MINEC);
    thick_line(s, cx * 16 + 8, (cy - sp) * 16 + 8, cx * 16 + 8, (cy + sp) * 16 + 8, 2, MINEC);
    int d = sp * 11 / 16;
    thick_line(s, (cx - d) * 16 + 8, (cy - d) * 16 + 8, (cx + d) * 16 + 8, (cy + d) * 16 + 8, 1, MINEC);
    thick_line(s, (cx - d) * 16 + 8, (cy + d) * 16 + 8, (cx + d) * 16 + 8, (cy - d) * 16 + 8, 1, MINEC);
    round_rect(s, cx - r, cy - r, 2 * r + 1, 2 * r + 1, r, MINEC, 255);
    int h = cs >= 24 ? 3 : 2;
    fill(s, cx - r / 2 - 1, cy - r / 2 - 1, h, h, rgb(250, 250, 250));
}

static void flag_at(struct surface *s, int x, int y, int cs) {
    int pole = x + cs * 9 / 16, top = y + cs / 5, th = cs * 2 / 5, len = cs * 5 / 16, half = th / 2;
    for (int j = 0; j < th; j++) {
        int w = len * (half - (j < half ? half - j : j - half)) / (half ? half : 1);
        fill(s, pole - w, top + j, w, 1, FLAGC);
    }
    int pw = cs >= 24 ? 2 : 1;
    fill(s, pole, top, pw, cs * 3 / 4 - cs / 5, INK);
    fill(s, x + cs / 4, y + cs * 3 / 4 - 1, cs / 2, cs >= 24 ? 3 : 2, INK);
}

static void draw_cell(struct mines *m, int cx, int cy) {
    struct surface *s = &m->win;
    int cs = m->cs, x = m->bx + cx * cs, y = m->by + cy * cs, i = cy * m->cols + cx;
    unsigned c = m->cell[i];
    int over = m->state == LOST;
    int shown = (c & OPEN) || (over && (((c & MINE) && !(c & FLAG)) || ((c & FLAG) && !(c & MINE))));
    if (!shown) {
        int b = cs / 8;
        fill(s, x, y, cs, cs, RAISED);
        fill(s, x, y, cs, b, LIGHT);
        fill(s, x, y, b, cs, LIGHT);
        fill(s, x, y + cs - b, cs, b, SHADE);
        fill(s, x + cs - b, y, b, cs, SHADE);
        if (c & FLAG) flag_at(s, x, y, cs);
    } else {
        fill(s, x, y, cs, cs, c & BOOM ? BOOMC : FLAT);
        fill(s, x, y, cs, 1, GRIDC);
        fill(s, x, y, 1, cs, GRIDC);
        if (c & MINE) mine_at(s, x, y, cs);
        else if (c & FLAG) {                       /* a flag where there was no mine */
            mine_at(s, x, y, cs);
            int a = cs / 5, e = cs - cs / 5;
            thick_line(s, (x + a) * 16, (y + a) * 16, (x + e) * 16, (y + e) * 16, 2, FLAGC);
            thick_line(s, (x + a) * 16, (y + e) * 16, (x + e) * 16, (y + a) * 16, 2, FLAGC);
        } else if (m->near[i]) {
            const struct font *f = cs >= 24 ? &m->ui.title : &m->ui.bold;
            char t[2] = {(char)('0' + m->near[i]), 0};
            int cap = (int)f->px * 727 / 1000;
            font_text(s, f, x + (cs - font_width(f, t) + 1) / 2, y + (cs + cap) / 2 + 1, t, number_color[m->near[i]]);
        }
    }
    if (m->cursor && cx == m->cx && cy == m->cy) {
        fill(s, x, y, cs, 2, CURSOR);
        fill(s, x, y + cs - 2, cs, 2, CURSOR);
        fill(s, x, y, 2, cs, CURSOR);
        fill(s, x + cs - 2, y, 2, cs, CURSOR);
    }
}

/* Three digits, as on the classic's red counters ("-05" below zero). */
static void led(struct mines *m, int x, long v) {
    struct surface *s = &m->win;
    if (v > 999) v = 999;
    if (v < -99) v = -99;
    char t[4];
    long a = v < 0 ? -v : v;
    t[0] = v < 0 ? '-' : (char)('0' + a / 100);
    t[1] = (char)('0' + a / 10 % 10);
    t[2] = (char)('0' + a % 10);
    t[3] = 0;
    round_rect(s, x, LED_Y, LED_W, LED_H, 5, rgb(30, 20, 22), 255);
    const struct font *f = &m->ui.title;
    font_text(s, f, x + (LED_W - font_width(f, t)) / 2, LED_Y + (LED_H + (int)f->px * 727 / 1000) / 2, t,
              rgb(255, 64, 48));
}

static void face(struct mines *m) {
    struct surface *s = &m->win;
    int x = FACE_X, y = FACE_Y, cx = x + FACE / 2, cy = y + FACE / 2, r = 11;
    round_rect(s, x, y, FACE, FACE, 7, RAISED, 255);
    fill(s, x + 4, y + 1, FACE - 8, 2, LIGHT);
    fill(s, x + 4, y + FACE - 3, FACE - 8, 2, SHADE);
    round_rect(s, cx - r, cy - r, 2 * r + 1, 2 * r + 1, r, rgb(255, 204, 48), 255);
    ring(s, cx, cy, r, 1, rgb(150, 110, 20));
    unsigned ink = rgb(40, 32, 20);
    if (m->state == LOST) {                         /* crossed-out eyes, a frown */
        for (int e = -1; e <= 1; e += 2) {
            int ex = cx + e * 4;
            thick_line(s, (ex - 2) * 16 + 8, (cy - 6) * 16 + 8, (ex + 2) * 16 + 8, (cy - 2) * 16 + 8, 1, ink);
            thick_line(s, (ex - 2) * 16 + 8, (cy - 2) * 16 + 8, (ex + 2) * 16 + 8, (cy - 6) * 16 + 8, 1, ink);
        }
        clip_to(s, cx - 7, cy + 3, 15, 4);
        ring(s, cx, cy + 9, 5, 1, ink);
    } else {
        if (m->state == WON) {                      /* sunglasses */
            fill(s, cx - 9, cy - 5, 19, 2, ink);
            round_rect(s, cx - 8, cy - 5, 7, 5, 2, ink, 255);
            round_rect(s, cx + 2, cy - 5, 7, 5, 2, ink, 255);
        } else {
            fill(s, cx - 5, cy - 5, 3, 3, ink);
            fill(s, cx + 3, cy - 5, 3, 3, ink);
        }
        clip_to(s, cx - 7, cy + 1, 15, 7);
        ring(s, cx, cy, 6, 1, ink);
    }
    clip_all(s);
}

static void draw_head(struct mines *m) {
    struct surface *s = &m->win;
    fill(s, 0, 0, MW, HEAD, BG);
    led(m, GRID_X, (long)m->mines - m->flags);
    led(m, TIME_X, (long)m->secs);
    /* Flag: lit while a click flags */
    int on = m->flag_mode;
    round_rect(s, FLAG_X, LED_Y, FLAG_W, LED_H, 8, on ? rgb(255, 176, 64) : RAISED, 255);
    flag_at(s, FLAG_X + 6, LED_Y + 2, 22);
    font_text(s, &m->ui.small_bold, FLAG_X + 32, LED_Y + 17, "Flag", on ? rgb(60, 30, 0) : INK);
    face(m);
}

static void draw_foot(struct mines *m) {
    struct surface *s = &m->win;
    int w = GRID_W / 3;
    round_rect(s, GRID_X, FOOT_Y, GRID_W, FOOT_H, FOOT_H / 2, rgb(196, 201, 212), 255);
    for (int k = 0; k < 3; k++) {
        int x = GRID_X + k * w, lit = k == m->level;
        if (lit) round_rect(s, x + 2, FOOT_Y + 2, w - 4, FOOT_H - 4, FOOT_H / 2 - 2, rgb(252, 252, 254), 255);
        struct line t = {.n = 0};
        if (m->best[k]) {
            put_s(&t, "  best ");
            put_dec(&t, m->best[k]);
            put_s(&t, " s");
        }
        t.b[t.n] = 0;
        int nw = font_width(&m->ui.small_bold, levels[k].name), tw = nw + font_width(&m->ui.small, t.b);
        int tx = x + (w - tw) / 2;
        font_text(s, &m->ui.small_bold, tx, FOOT_Y + 16, levels[k].name, lit ? INK : rgb(90, 96, 112));
        font_text(s, &m->ui.small, tx + nw, FOOT_Y + 16, t.b, rgb(96, 102, 118));
    }
}

static void draw(struct mines *m) {
    fill(&m->win, 0, HEAD, MW, MH - HEAD, BG);
    draw_head(m);
    for (int y = 0; y < m->rows; y++)
        for (int x = 0; x < m->cols; x++) draw_cell(m, x, y);
    draw_foot(m);
}

/* ---- input ---- */

static void key(struct mines *m, struct line *l, u64 k) {
    if (k >= KEY_UP && k <= KEY_LEFT) {
        m->cursor = 1;
        if (k == KEY_UP && m->cy > 0) m->cy--;
        else if (k == KEY_DOWN && m->cy < m->rows - 1) m->cy++;
        else if (k == KEY_LEFT && m->cx > 0) m->cx--;
        else if (k == KEY_RIGHT && m->cx < m->cols - 1) m->cx++;
    } else if (k == ' ' || k == '\r' || k == '\n') {
        m->cursor = 1;
        act(m, l, m->cx, m->cy, 0);
    } else if (k == 'f' || k == 'F') {
        m->cursor = 1;
        if (m->state == READY || m->state == PLAYING) toggle_flag(m, l, m->cx, m->cy);
    } else if (k == 'n' || k == 'N') new_game(m, l);
    else if (k >= '1' && k <= '3') set_level(m, l, (int)(k - '1'));
}

static void click(struct mines *m, struct line *l, int x, int y) {
    if (x >= FACE_X && x < FACE_X + FACE && y >= FACE_Y && y < FACE_Y + FACE) new_game(m, l);
    else if (x >= FLAG_X && x < FLAG_X + FLAG_W && y >= LED_Y && y < LED_Y + LED_H) flag_mode(m, l);
    else if (y >= FOOT_Y && y < FOOT_Y + FOOT_H && x >= GRID_X && x < GRID_X + GRID_W) set_level(m, l, (x - GRID_X) / (GRID_W / 3));
    else if (x >= m->bx && y >= m->by && x < m->bx + m->cols * m->cs && y < m->by + m->rows * m->cs) {
        m->cursor = 0;
        act(m, l, (x - m->bx) / m->cs, (y - m->by) / m->cs, m->flag_mode);
    }
}

/* ---- the files ---- */

/* A number at the start of `s` (0 if none). */
static unsigned number(const char *s) {
    unsigned v = 0;
    while (*s >= '0' && *s <= '9') v = v * 10 + (unsigned)(*s++ - '0');
    return v;
}

static void read_files(struct mines *m, struct line *l) {
    char b[256];
    long n = fs_read_all(&m->fs, SEED_FILE, b, sizeof b - 1);
    m->seed = 0;
    if (n > 0) {
        b[n] = 0;
        m->seed = number(b);
        if (m->seed) {
            put_s(l, "mines: seed ");
            put_dec(l, m->seed);
            put_s(l, " from " SEED_FILE ", for every game");
            say(l);
        }
    }
    n = fs_read_all(&m->fs, BEST_FILE, b, sizeof b - 1);
    b[n > 0 ? n : 0] = 0;
    /* a line a level: its name, a space, the seconds */
    for (const char *p = b; *p;) {
        for (int k = 0; k < 3; k++) {
            const char *name = levels[k].lower;
            int j = 0;
            while (name[j] && p[j] == name[j]) j++;
            if (!name[j] && p[j] == ' ') m->best[k] = number(p + j + 1);
        }
        while (*p && *p != '\n') p++;
        if (*p) p++;
    }
    put_s(l, "mines: best times:");
    for (int k = 0; k < 3; k++) {
        put_s(l, k ? ", " : " ");
        put_s(l, levels[k].lower);
        put_s(l, " ");
        if (m->best[k]) {
            put_dec(l, m->best[k]);
            put_s(l, " s");
        } else put_s(l, "none");
    }
    say(l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct mines *m = (struct mines *)DATA;
    struct line l = {.n = 0};
    ui_load(&m->ui, app_assets());
    m->win = app_surface(MW, MH);
    fs_init(&m->fs, SPARE_PAGE);
    m->cx = m->cy = 4;
    m->cursor = m->flag_mode = 0;
    for (int k = 0; k < 3; k++) m->best[k] = 0;
    read_files(m, &l);
    set_level(m, &l, 0);
    draw(m);
    u64 opened = app_open(MW, MH, "Mines");
    put_s(&l, "mines: opened a window");
    put_s(&l, outcome(opened));
    say(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        /* while the time runs, ask without waiting, to move it on each second */
        struct event e = m->state == PLAYING ? app_poll(dirty) : app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "mines: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (e.kind == EV_KEY || e.kind == EV_DOWN) {
            if (e.kind == EV_KEY) key(m, &l, e.a);
            else click(m, &l, (int)e.a, (int)e.b);
            draw(m);
            dirty = 1;
            continue;
        }
        if (m->state == PLAYING) {
            u64 s = seconds(m);
            if (s != m->secs) {
                m->secs = s;
                draw_head(m);
                dirty = 1;
                continue;
            }
            sleep_ms(50);
        }
    }
}
