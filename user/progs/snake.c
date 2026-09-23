/* snake: the arrow keys steer; eat the orange squares to grow. It keeps its own time with
   the kernel's sleep call and asks for keys without blocking. Space starts a new game. */
#include "../app.h"

#define CELL 12
#define GW 30
#define GH 20
#define SW (GW * CELL)
#define SH (GH * CELL + 24)
#define MAXLEN (GW * GH)

struct snake {
    struct surface win;
    unsigned char x[MAXLEN], y[MAXLEN];   /* head first */
    int len, dx, dy, alive, score, best;
    int fx, fy;
    unsigned rng;
};

static unsigned next_rand(struct snake *s) {
    s->rng = s->rng * 1103515245u + 12345u;
    return s->rng >> 16;
}

static int on_snake(struct snake *s, int x, int y) {
    for (int i = 0; i < s->len; i++) if (s->x[i] == x && s->y[i] == y) return 1;
    return 0;
}

static void place_food(struct snake *s) {
    do {
        s->fx = (int)(next_rand(s) % GW);
        s->fy = (int)(next_rand(s) % GH);
    } while (on_snake(s, s->fx, s->fy));
}

static void start(struct snake *s) {
    s->len = 4;
    for (int i = 0; i < s->len; i++) { s->x[i] = (unsigned char)(10 - i); s->y[i] = 10; }
    s->dx = 1;
    s->dy = 0;
    s->alive = 1;
    s->score = 0;
    place_food(s);
}

static void step(struct snake *s, struct line *l) {
    int nx = s->x[0] + s->dx, ny = s->y[0] + s->dy;
    if (nx < 0 || ny < 0 || nx >= GW || ny >= GH || on_snake(s, nx, ny)) {
        s->alive = 0;
        if (s->score > s->best) s->best = s->score;
        put_s(l, "snake: game over, score ");
        put_dec(l, (u64)s->score);
        put_s(l, "\n");
        flush(l);
        return;
    }
    int grow = nx == s->fx && ny == s->fy;
    if (grow && s->len < MAXLEN) s->len++;
    for (int i = s->len - 1; i > 0; i--) { s->x[i] = s->x[i - 1]; s->y[i] = s->y[i - 1]; }
    s->x[0] = (unsigned char)nx;
    s->y[0] = (unsigned char)ny;
    if (grow) {
        s->score += 10;
        place_food(s);
        if (s->score == 10) {
            put_s(l, "snake: ate the first square\n");
            flush(l);
        }
    }
}

static void draw(struct snake *s) {
    struct surface *w = &s->win;
    fill(w, 0, 0, SW, SH, rgb(18, 22, 30));
    for (int y = 0; y < GH; y++)
        for (int x = (y & 1); x < GW; x += 2) fill(w, x * CELL, 24 + y * CELL, CELL, CELL, rgb(22, 27, 36));
    round_rect(w, s->fx * CELL + 2, 24 + s->fy * CELL + 2, CELL - 4, CELL - 4, 3, rgb(255, 160, 60), 255);
    for (int i = s->len - 1; i >= 0; i--)
        round_rect(w, s->x[i] * CELL + 1, 24 + s->y[i] * CELL + 1, CELL - 2, CELL - 2, 3,
                   i == 0 ? rgb(140, 240, 160) : rgb(70, 190, 110), 255);
    struct line l = {.n = 0};
    put_s(&l, "score ");
    put_dec(&l, (u64)s->score);
    put_s(&l, "   best ");
    put_dec(&l, (u64)s->best);
    l.b[l.n] = 0;
    text(w, 8, 8, l.b, rgb(200, 206, 222), 1);
    if (!s->alive) text(w, SW / 2 - text_width("space: play again", 2) / 2, SH / 2, "space: play again",
                        rgb(255, 255, 255), 2);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct snake *s = (struct snake *)DATA;
    struct line l = {.n = 0};
    app_assets();
    s->win = app_surface(SW, SH);
    s->rng = (unsigned)micros();
    s->best = 0;
    start(s);
    draw(s);
    u64 opened = app_open(SW, SH, "Snake");
    put_s(&l, "snake: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_poll(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind == EV_KEY) {
            /* no turning straight back into yourself */
            if (e.a == KEY_UP && s->dy != 1) { s->dx = 0; s->dy = -1; }
            else if (e.a == KEY_DOWN && s->dy != -1) { s->dx = 0; s->dy = 1; }
            else if (e.a == KEY_LEFT && s->dx != 1) { s->dx = -1; s->dy = 0; }
            else if (e.a == KEY_RIGHT && s->dx != -1) { s->dx = 1; s->dy = 0; }
            else if (e.a == ' ' && !s->alive) start(s);
            continue;              /* take every waiting key before the next step */
        }
        if (s->alive) step(s, &l);
        draw(s);
        dirty = 1;
        int speed = 150 - s->len * 2;
        sleep_ms((u64)(speed < 60 ? 60 : speed));
    }
}
