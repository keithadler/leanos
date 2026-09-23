/* tiles: 2048. The arrow keys slide every tile; two equal tiles that meet merge into
   their sum. Reach 2048. Space starts a new game. */
#include "../app.h"

#define N 4
#define TILE 64
#define GAP 8
#define TW (N * TILE + (N + 1) * GAP)
#define TH (TW + 32)

struct tiles {
    struct surface win;
    unsigned g[N][N];
    u64 score;
    unsigned rng;
    int over, moves;
};

static void add_tile(struct tiles *t) {
    int free = 0;
    for (int y = 0; y < N; y++) for (int x = 0; x < N; x++) free += t->g[y][x] == 0;
    if (!free) return;
    t->rng = t->rng * 1103515245u + 12345u;
    int pick = (int)((t->rng >> 16) % (unsigned)free);
    for (int y = 0; y < N; y++)
        for (int x = 0; x < N; x++)
            if (t->g[y][x] == 0 && pick-- == 0) t->g[y][x] = (t->rng >> 8) % 10 == 0 ? 4 : 2;
}

static void start(struct tiles *t) {
    for (int y = 0; y < N; y++) for (int x = 0; x < N; x++) t->g[y][x] = 0;
    t->score = 0;
    t->over = 0;
    t->moves = 0;
    add_tile(t);
    add_tile(t);
}

/* Slide one line of four toward index 0; returns whether anything moved. */
static int slide(unsigned *line[N], u64 *score) {
    unsigned v[N], out[N] = {0, 0, 0, 0};
    int n = 0, moved = 0;
    for (int i = 0; i < N; i++) if (*line[i]) v[n++] = *line[i];
    int k = 0;
    for (int i = 0; i < n; i++) {
        if (i + 1 < n && v[i] == v[i + 1]) { out[k++] = v[i] * 2; *score += v[i] * 2; i++; }
        else out[k++] = v[i];
    }
    for (int i = 0; i < N; i++) {
        if (*line[i] != out[i]) moved = 1;
        *line[i] = out[i];
    }
    return moved;
}

static int move(struct tiles *t, u64 key) {
    int moved = 0;
    for (int a = 0; a < N; a++) {
        unsigned *line[N];
        for (int b = 0; b < N; b++) {
            if (key == KEY_LEFT) line[b] = &t->g[a][b];
            else if (key == KEY_RIGHT) line[b] = &t->g[a][N - 1 - b];
            else if (key == KEY_UP) line[b] = &t->g[b][a];
            else line[b] = &t->g[N - 1 - b][a];
        }
        moved |= slide(line, &t->score);
    }
    return moved;
}

static int stuck(struct tiles *t) {
    for (int y = 0; y < N; y++)
        for (int x = 0; x < N; x++) {
            if (!t->g[y][x]) return 0;
            if (x + 1 < N && t->g[y][x] == t->g[y][x + 1]) return 0;
            if (y + 1 < N && t->g[y][x] == t->g[y + 1][x]) return 0;
        }
    return 1;
}

static unsigned tile_color(unsigned v) {
    static const unsigned c[12] = {0xcdc1b4, 0xeee4da, 0xede0c8, 0xf2b179, 0xf59563, 0xf67c5f,
                                   0xf65e3b, 0xedcf72, 0xedcc61, 0xedc850, 0xedc53f, 0xedc22e};
    int k = 0;
    while (v > 1 && k < 11) { v >>= 1; k++; }
    return c[k];
}

static void draw(struct tiles *t) {
    struct surface *w = &t->win;
    fill(w, 0, 0, TW, TH, rgb(250, 248, 239));
    struct line l = {.n = 0};
    put_s(&l, "score ");
    put_dec(&l, t->score);
    l.b[l.n] = 0;
    text(w, GAP, 10, l.b, rgb(119, 110, 101), 2);
    round_rect(w, 0, 32, TW, TW, 8, rgb(187, 173, 160), 255);
    for (int y = 0; y < N; y++)
        for (int x = 0; x < N; x++) {
            int px = GAP + x * (TILE + GAP), py = 32 + GAP + y * (TILE + GAP);
            unsigned v = t->g[y][x];
            round_rect(w, px, py, TILE, TILE, 6, tile_color(v), 255);
            if (!v) continue;
            struct line n = {.n = 0};
            put_dec(&n, v);
            n.b[n.n] = 0;
            int scale = v < 100 ? 3 : v < 1000 ? 2 : 2;
            text(w, px + TILE / 2 - text_width(n.b, scale) / 2, py + TILE / 2 - 7 * scale / 2, n.b,
                 v <= 4 ? rgb(119, 110, 101) : rgb(249, 246, 242), scale);
        }
    if (t->over) {
        fill_alpha(w, 0, 32, TW, TW, rgb(250, 248, 239), 160);
        text(w, TW / 2 - text_width("no moves left", 2) / 2, 32 + TW / 2 - 14, "no moves left", rgb(119, 110, 101), 2);
        text(w, TW / 2 - text_width("space: again", 2) / 2, 32 + TW / 2 + 6, "space: again", rgb(119, 110, 101), 2);
    }
}

__attribute__((section(".text.start"))) void _start(void) {
    struct tiles *t = (struct tiles *)DATA;
    struct line l = {.n = 0};
    app_assets();
    t->win = app_surface(TW, TH);
    t->rng = (unsigned)micros();
    start(t);
    draw(t);
    u64 opened = app_open(TW, TH, "Tiles");
    put_s(&l, "tiles: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind != EV_KEY) continue;
        if (e.a == ' ') start(t);
        else if (e.a >= KEY_UP && e.a <= KEY_LEFT && !t->over) {
            if (!move(t, e.a)) continue;
            add_tile(t);
            t->over = stuck(t);
            if (++t->moves == 3) {
                put_s(&l, "tiles: 3 moves, score ");
                put_dec(&l, t->score);
                put_s(&l, "\n");
                flush(&l);
            }
        } else continue;
        draw(t);
        dirty = 1;
    }
}
