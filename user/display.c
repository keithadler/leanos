/* The display server. It owns the framebuffer (capability 5) and nothing else can reach it.

   Clients call it. OPEN: w0 = 1, w1 = width << 16 | height, w2 = up to 8 bytes of title,
   with a read-only capability to the window's pixels; the reply is 0 on success. WAIT:
   w0 = 2, w1 = 1 if the client redrew its pixels; the reply comes when there is an event
   for the client (w0 = kind, w1, w2). The server never blocks on a client: it holds each
   caller's reply slot until it has something to say.

   The input driver sends it keys and mouse reports (badge 3). Keys go to the focused window;
   a click focuses and raises a window, and dragging its title bar moves it. The sender's
   badge, which the kernel sets, names every window, so no client can pass for another. */
#include "lib.h"
#include "gfx.h"

#define FRAMEBUFFER 5
#define FB_PAGE 1024
#define WIN_PAGE 2048   /* window k's pixels are mapped at WIN_PAGE + 64 k */
#define MAX_WIN 4
#define TITLE_H 26
#define BAR_H 28
#define W 1024
#define H 600

enum { OP_OPEN = 1, OP_WAIT = 2 };
enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4 };
enum { BADGE_ALICE = 1, BADGE_MALLORY = 2, BADGE_INPUT = 3 };

struct win {
    int used;
    u64 badge;
    int x, y, w, h;             /* outer frame */
    struct surface content;
    char title[9];
    u64 slot;                   /* reply slot + 1 while the client waits, else 0 */
    u64 queue[16][3];
    int qhead, qlen;
};

/* Everything the server remembers lives in its data pages: user programs have no writable
   globals. */
struct state {
    struct surface screen;
    unsigned bg[H];
    struct win win[MAX_WIN];
    int z[MAX_WIN];             /* window indices, bottom to top */
    int nz;
    int px, py;                 /* pointer */
    int drag, grab_x, grab_y, drag_x0, drag_y0;
};

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static const char *name_of(u64 badge) {
    return badge == BADGE_ALICE ? "alice" : badge == BADGE_MALLORY ? "mallory" : "unknown";
}

/* The leanos mark: a rounded tile, indigo to teal, with a white lambda. */
static void logo(struct surface *s, int x, int y, int size) {
    round_gradient(s, x, y, size, size, size / 5, rgb(76, 78, 204), rgb(30, 168, 160));
    int u = size * 16 / 100; /* one percent of the tile, in 1/16 pixels */
    int stroke = size / 9 > 1 ? size / 9 : 1;
    thick_line(s, x * 16 + 30 * u, y * 16 + 20 * u, x * 16 + 72 * u, y * 16 + 80 * u, stroke, rgb(255, 255, 255));
    thick_line(s, x * 16 + 51 * u, y * 16 + 49 * u, x * 16 + 29 * u, y * 16 + 80 * u, stroke, rgb(255, 255, 255));
}

#define SPLASH_MS 1600
#define PBAR_W 320
#define PBAR_H 6
#define PBAR_Y 420

/* Ease in and out: 0..1000 to 0..1000, slow at both ends. */
static int ease(int t) {
    if (t <= 0) return 0;
    if (t >= 1000) return 1000;
    return t * t / 1000 * (3000 - 2 * t) / 1000;
}

static void splash_bar(struct state *st, int done /* 0..1000 */) {
    struct surface *s = &st->screen;
    int x = W / 2 - PBAR_W / 2;
    clip_to(s, x - 12, PBAR_Y - 12, PBAR_W + 24, PBAR_H + 24);
    for (int j = s->cy0; j < s->cy1; j++)
        fill(s, s->cx0, j, s->cx1 - s->cx0, 1, mix(rgb(14, 18, 34), rgb(24, 38, 64), (unsigned)(j * 255 / (H - 1))));
    round_rect(s, x, PBAR_Y, PBAR_W, PBAR_H, PBAR_H / 2, rgb(44, 54, 84), 255);
    int filled = PBAR_W * done / 1000;
    if (filled >= PBAR_H) {
        for (int i = 0; i < filled; i++) {
            unsigned c = mix(rgb(70, 110, 230), rgb(80, 220, 200), (unsigned)(i * 255 / PBAR_W));
            int cover = i < PBAR_H / 2 || i >= filled - PBAR_H / 2 ? 1 : 0;
            if (cover) round_rect(s, x + i, PBAR_Y, 1, PBAR_H, 0, c, 200);
            else fill(s, x + i, PBAR_Y, 1, PBAR_H, c);
        }
        round_rect(s, x, PBAR_Y, filled, PBAR_H, PBAR_H / 2, rgb(80, 220, 200), 60);
        /* a soft glint riding the leading edge */
        for (int k = 5; k >= 1; k--)
            round_rect(s, x + filled - 3 - k, PBAR_Y - k + 3, 2 * k + 3, 2 * k, k, rgb(200, 255, 245), 22);
    }
    clip_all(s);
}

static void splash(struct state *st) {
    struct surface *s = &st->screen;
    clip_all(s);
    gradient(s, 0, 0, W, H, rgb(14, 18, 34), rgb(24, 38, 64));
    logo(s, W / 2 - 70, 150, 140);
    const char *name = "leanos";
    text(s, W / 2 - text_width(name, 6) / 2, 318, name, rgb(240, 242, 248), 6);
    const char *tag = "access control proved in Lean";
    text(s, W / 2 - text_width(tag, 2) / 2, 376, tag, rgb(140, 150, 175), 2);
    /* the copyright line at the foot of the screen */
    const char *who = " 2026 Keith Adler";
    int wide = 7 * 2 + 4 + text_width(who, 2);
    int cx = copyright_sign(s, W / 2 - wide / 2, H - 40, rgb(110, 120, 150), 2);
    text(s, cx, H - 40, who, rgb(110, 120, 150), 2);
    /* The bar fills over SPLASH_MS, eased, drawn as often as the time allows. Later it will
       follow real work: checking each program against the signed boot image. */
    u64 start = millis();
    for (;;) {
        u64 t = millis() - start;
        splash_bar(st, ease((int)(t * 1000 / SPLASH_MS)));
        if (t >= SPLASH_MS) break;
    }
}



static int outer_w(const struct win *w) { return w->content.w + 8; }
static int outer_h(const struct win *w) { return w->content.h + TITLE_H + 4; }

static int focused(struct state *st) { return st->nz ? st->z[st->nz - 1] : -1; }

static void draw_window(struct state *st, int k) {
    struct surface *s = &st->screen;
    struct win *w = &st->win[k];
    int ow = outer_w(w), oh = outer_h(w), x = w->x, y = w->y;
    int focus = focused(st) == k;
    shadow(s, x, y, ow, oh, 10);
    round_rect(s, x, y, ow, oh, 10, rgb(246, 244, 238), 255);
    if (focus) round_gradient(s, x, y, ow, TITLE_H + 10, 10, rgb(78, 120, 196), rgb(52, 88, 158));
    else round_gradient(s, x, y, ow, TITLE_H + 10, 10, rgb(206, 206, 212), rgb(184, 184, 192));
    fill(s, x, y + TITLE_H, ow, 10, rgb(246, 244, 238));
    round_rect(s, x + ow - 22, y + 8, 11, 11, 5, focus ? rgb(238, 96, 88) : rgb(160, 160, 168), 255);
    text(s, x + 12, y + 6, w->title, focus ? rgb(255, 255, 255) : rgb(80, 80, 88), 2);
    blit(s, x + 4, y + TITLE_H, &w->content);
}

static void top_bar(struct state *st) {
    struct surface *s = &st->screen;
    fill_alpha(s, 0, 0, W, BAR_H, rgb(250, 250, 252), 215);
    fill_alpha(s, 0, BAR_H, W, 1, rgb(0, 0, 0), 60);
    logo(s, 8, 4, 20);
    text(s, 36, 7, "leanos", rgb(30, 30, 36), 2);
    const char *right = "access control proved in Lean";
    text(s, W - 10 - text_width(right, 2), 7, right, rgb(96, 96, 104), 2);
}

/* Redraw one rectangle of the screen: desktop, bar, windows bottom to top, pointer. */
static void composite(struct state *st, int x, int y, int w, int h) {
    struct surface *s = &st->screen;
    clip_to(s, x, y, w, h);
    for (int j = s->cy0; j < s->cy1; j++) fill(s, s->cx0, j, s->cx1 - s->cx0, 1, st->bg[j]);
    if (s->cy0 < BAR_H + 1) top_bar(st);
    for (int i = 0; i < st->nz; i++) {
        struct win *wn = &st->win[st->z[i]];
        if (wn->x - 8 < s->cx1 && wn->x + outer_w(wn) + 8 > s->cx0 &&
            wn->y - 8 < s->cy1 && wn->y + outer_h(wn) + 12 > s->cy0)
            draw_window(st, st->z[i]);
    }
    pointer(s, st->px, st->py);
    clip_all(s);
}

static void composite_window(struct state *st, int k) {
    struct win *w = &st->win[k];
    composite(st, w->x - 8, w->y - 8, outer_w(w) + 16, outer_h(w) + 20);
}

static void raise(struct state *st, int k) {
    int at = -1;
    for (int i = 0; i < st->nz; i++) if (st->z[i] == k) at = i;
    if (at < 0) return;
    for (int i = at; i < st->nz - 1; i++) st->z[i] = st->z[i + 1];
    st->z[st->nz - 1] = k;
}

static int window_at(struct state *st, int x, int y) {
    for (int i = st->nz - 1; i >= 0; i--) {
        struct win *w = &st->win[st->z[i]];
        if (x >= w->x && x < w->x + outer_w(w) && y >= w->y && y < w->y + outer_h(w)) return st->z[i];
    }
    return -1;
}

/* Give window k's client an event: now, if it is waiting, or when it next asks. */
static void deliver_event(struct win *w, u64 kind, u64 a, u64 b) {
    if (w->slot) {
        sys(SYS_REPLY, w->slot - 1, kind, a, b, 0);
        w->slot = 0;
    } else if (w->qlen < 16) {
        int at = (w->qhead + w->qlen++) % 16;
        w->queue[at][0] = kind;
        w->queue[at][1] = a;
        w->queue[at][2] = b;
    }
}

static void on_input(struct state *st, struct line *l, u64 kind, u64 a, u64 b) {
    if (kind == EV_KEY) {
        int k = focused(st);
        if (k < 0) return;
        deliver_event(&st->win[k], EV_KEY, a, 0);
        put_s(l, "display: key '");
        char ch[2] = {a >= 32 && a < 127 ? (char)a : '?', 0};
        put_s(l, ch);
        put_s(l, "' to ");
        put_s(l, name_of(st->win[k].badge));
        say(l);
        return;
    }
    int ox = st->px, oy = st->py;
    st->px = a < W ? (int)a : W - 1;
    st->py = b < H ? (int)b : H - 1;
    if (kind == EV_DOWN) {
        int k = window_at(st, st->px, st->py);
        if (k >= 0) {
            raise(st, k);
            struct win *w = &st->win[k];
            if (st->py < w->y + TITLE_H) {
                st->drag = k + 1;
                st->grab_x = st->px - w->x;
                st->grab_y = st->py - w->y;
                st->drag_x0 = w->x;
                st->drag_y0 = w->y;
            }
            for (int i = 0; i < st->nz; i++) composite_window(st, st->z[i]);
        }
    } else if (kind == EV_MOVE && st->drag) {
        struct win *w = &st->win[st->drag - 1];
        int nx = st->px - st->grab_x, ny = st->py - st->grab_y;
        if (ny < BAR_H + 2) ny = BAR_H + 2;
        int oxw = w->x, oyw = w->y;
        w->x = nx;
        w->y = ny;
        int x0 = (oxw < nx ? oxw : nx) - 8, y0 = (oyw < ny ? oyw : ny) - 8;
        int x1 = (oxw > nx ? oxw : nx) + outer_w(w) + 8, y1 = (oyw > ny ? oyw : ny) + outer_h(w) + 12;
        composite(st, x0, y0, x1 - x0, y1 - y0);
    } else if (kind == EV_UP && st->drag) {
        struct win *w = &st->win[st->drag - 1];
        if (w->x != st->drag_x0 || w->y != st->drag_y0) {
            put_s(l, "display: moved ");
            put_s(l, name_of(w->badge));
            put_s(l, "'s window to (");
            put_dec(l, w->x);
            put_s(l, ", ");
            put_dec(l, w->y);
            put_s(l, ")");
            say(l);
        }
        st->drag = 0;
    }
    composite(st, ox, oy, 12, 19);
    composite(st, st->px, st->py, 12, 19);
}

static void on_open(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], size = r->x[3], title = r->x[4], cap = r->x[5], slot = r->x[6];
    u64 w = size >> 16, h = size & 0xffff;
    int k = -1;
    for (int i = 0; i < MAX_WIN; i++) if (!st->win[i].used) { k = i; break; }
    struct res info = sys1(SYS_CAPINFO, cap - 1);
    u64 need = (w * h * 4 + 4095) / 4096;
    if (k < 0 || w == 0 || h == 0 || w > 560 || h > 380 || info.x[2] != 0 || info.x[3] < need ||
        need > 64 || sys2(SYS_MAP, cap - 1, WIN_PAGE + 64 * k).status != OK) {
        put_s(l, "display: ");
        put_s(l, name_of(badge));
        put_s(l, " sent a window that does not fit its pixels; refused");
        say(l);
        sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        return;
    }
    struct win *wn = &st->win[k];
    wn->used = 1;
    wn->badge = badge;
    wn->content = surface_of((unsigned *)PAGE(WIN_PAGE + 64 * k), (int)w, (int)h);
    for (int i = 0; i < 8; i++) wn->title[i] = (char)(title >> (8 * i));
    wn->title[8] = 0;
    wn->x = 70 + 40 * k;
    wn->y = 76 + 36 * k;
    wn->slot = 0;
    wn->qhead = wn->qlen = 0;
    st->z[st->nz++] = k;
    composite(st, 0, 0, W, H);
    put_s(l, "display: ");
    put_s(l, name_of(badge));
    put_s(l, " opened a ");
    put_dec(l, w);
    put_s(l, "x");
    put_dec(l, h);
    put_s(l, " window from a read-only capability to ");
    put_dec(l, info.x[3]);
    put_s(l, " pages");
    say(l);
    sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
}

static void on_wait(struct state *st, struct res *r) {
    u64 badge = r->x[1], dirty = r->x[3], slot = r->x[6];
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (!w->used || w->badge != badge) continue;
        if (dirty) composite_window(st, k);
        if (w->qlen) {
            u64 *e = w->queue[w->qhead];
            sys(SYS_REPLY, slot - 1, e[0], e[1], e[2], 0);
            w->qhead = (w->qhead + 1) % 16;
            w->qlen--;
        } else {
            w->slot = slot;
        }
        return;
    }
    sys(SYS_REPLY, slot - 1, 0, 0, 0, 0); /* no window: nothing to wait for */
}

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    struct state *st = (struct state *)DATA;
    if (sys2(SYS_MAP, FRAMEBUFFER, FB_PAGE).status != OK) {
        put_s(&l, "display: no framebuffer to draw on");
        say(&l);
        exit_task();
    }
    st->screen = surface_of((unsigned *)PAGE(FB_PAGE), W, H);
    st->px = W / 2;
    st->py = H / 2;
    splash(st);
    put_s(&l, "display: boot logo drawn");
    say(&l);
    for (u64 t = millis(); millis() - t < 400;) {} /* hold the full bar a moment */

    for (int j = 0; j < H; j++) st->bg[j] = mix(rgb(24, 42, 78), rgb(36, 118, 126), (unsigned)(j * 255 / (H - 1)));
    composite(st, 0, 0, W, H);
    put_s(&l, "display: desktop drawn on the 1024x600 framebuffer");
    say(&l);

    for (;;) {
        struct res r = sys1(SYS_RECV, ENDPOINT);
        u64 badge = r.x[1], op = r.x[2], slot = r.x[6];
        if (badge == BADGE_INPUT && !slot) {
            on_input(st, &l, op, r.x[3], r.x[4]);
        } else if (slot && op == OP_OPEN && r.x[5]) {
            on_open(st, &l, &r);
        } else if (slot && op == OP_WAIT) {
            on_wait(st, &r);
        } else {
            put_s(&l, "display: ");
            put_s(&l, name_of(badge));
            put_s(&l, " asked for a window but sent no pixels; ignored");
            say(&l);
            if (slot) sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        }
    }
}
