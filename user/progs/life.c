/* life: Conway's Game of Life on a 64 x 40 torus, a generation every tenth of a second.
   It starts from a glider gun. Space pauses, a click toggles a cell, r reseeds at random. */
#include "../app.h"

#define CELL 6
#define GW 64
#define GH 40
#define LW (GW * CELL)
#define LH (GH * CELL + 20)

struct life {
    struct surface win;
    unsigned char a[GH][GW], b[GH][GW];
    u64 gen;
    int paused;
    unsigned rng;
};

static void gun(struct life *L) {
    static const char *const art[9] = {
        "........................O...........",
        "......................O.O...........",
        "............OO......OO............OO",
        "...........O...O....OO............OO",
        "OO........O.....O...OO..............",
        "OO........O...O.OO....O.O...........",
        "..........O.....O.......O...........",
        "...........O...O....................",
        "............OO......................",
    };
    for (int y = 0; y < GH; y++) for (int x = 0; x < GW; x++) L->a[y][x] = 0;
    for (int y = 0; y < 9; y++)
        for (int x = 0; art[y][x]; x++) L->a[y + 2][x + 2] = art[y][x] == 'O';
    L->gen = 0;
}

static void generation(struct life *L) {
    for (int y = 0; y < GH; y++)
        for (int x = 0; x < GW; x++) {
            int n = 0;
            for (int dy = -1; dy <= 1; dy++)
                for (int dx = -1; dx <= 1; dx++)
                    if (dx || dy) n += L->a[(y + dy + GH) % GH][(x + dx + GW) % GW];
            L->b[y][x] = (unsigned char)(n == 3 || (n == 2 && L->a[y][x]));
        }
    for (int y = 0; y < GH; y++) for (int x = 0; x < GW; x++) L->a[y][x] = L->b[y][x];
    L->gen++;
}

static void draw(struct life *L) {
    struct surface *w = &L->win;
    fill(w, 0, 0, LW, LH, rgb(14, 16, 26));
    int alive = 0;
    for (int y = 0; y < GH; y++)
        for (int x = 0; x < GW; x++)
            if (L->a[y][x]) {
                fill(w, x * CELL + 1, 20 + y * CELL + 1, CELL - 1, CELL - 1, rgb(126, 214, 255));
                alive++;
            }
    struct line l = {.n = 0};
    put_s(&l, "generation ");
    put_dec(&l, L->gen);
    put_s(&l, "   alive ");
    put_dec(&l, (u64)alive);
    put_s(&l, L->paused ? "   paused" : "");
    l.b[l.n] = 0;
    text(w, 6, 6, l.b, rgb(170, 176, 200), 1);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct life *L = (struct life *)DATA;
    struct line l = {.n = 0};
    app_assets();
    L->win = app_surface(LW, LH);
    L->paused = 0;
    L->rng = (unsigned)micros();
    gun(L);
    draw(L);
    u64 opened = app_open(LW, LH, "Life");
    put_s(&l, "life: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_poll(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind == EV_KEY && e.a == ' ') L->paused = !L->paused;
        else if (e.kind == EV_KEY && e.a == 'r') {
            for (int y = 0; y < GH; y++)
                for (int x = 0; x < GW; x++) {
                    L->rng = L->rng * 1103515245u + 12345u;
                    L->a[y][x] = (L->rng >> 16) % 4 == 0;
                }
            L->gen = 0;
        } else if (e.kind == EV_DOWN && e.b >= 20) {
            int x = (int)e.a / CELL, y = ((int)e.b - 20) / CELL;
            if (x < GW && y < GH) L->a[y][x] ^= 1;
        } else if (e.kind == EV_NONE && !L->paused) {
            generation(L);
            if (L->gen == 30) {
                put_s(&l, "life: 30 generations\n");
                flush(&l);
            }
        } else if (e.kind != EV_NONE) continue;
        draw(L);
        dirty = 1;
        if (e.kind == EV_NONE) sleep_ms(100);
    }
}
