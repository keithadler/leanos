/* The display server. It owns the framebuffer (capability 5) and nothing else can reach it.

   Clients call it. OPEN: w0 = 1, w1 = width << 16 | height, w2 = up to 8 bytes of title,
   with a read-only capability to the window's pixels; the reply is 0 on success. WAIT:
   w0 = 2, w1 = 1 if the client redrew its pixels; the reply comes when there is an event
   for the client (w0 = kind, w1, w2). The server never blocks on a client: it holds each
   caller's reply slot until it has something to say.

   The input driver sends it keys and mouse reports (badge 3). Keys go to the focused window;
   a click focuses and raises a window, and dragging its title bar moves it. The sender's
   badge, which the kernel sets, names every window, so no client can pass for another.
   A click inside a window goes to its client (EV_DOWN, window coordinates); a click on the
   red button asks the client to close (EV_CLOSE), and the window goes at once.

   It holds a launch capability for each app (capabilities 6 to 10: Notes, Terminal,
   Settings, Security, Files). Clicking an app in the dock starts it if it is not running; the
   kernel first takes back everything the app's last run shared, including its window, so
   the server drops that window before it asks. SET (w0 = 3) changes the desktop, and only
   Settings (badge 6) may ask.

   It keeps a copy of its own capability list's layout (which app granted each capability,
   and for which window), so it can drop a window's capability when the window goes, drop
   at once any grant it did not ask for, and know which capabilities the kernel takes back
   when it starts an app again. Its capability list never grows without bound.

   Its fonts and icons were loaded at boot into the start of its spare run (capability 3),
   which it maps read-only. The desktop's background is a pattern it computes itself. */
#include "lib.h"
#include "gfx.h"
#include "assets.h"

#define FRAMEBUFFER 5
#define FB_PAGE 1024
#define WIN_PAGE 2048   /* window k's pixels are mapped at WIN_PAGE + WIN_MAX_PAGES k */
#define WIN_MAX_PAGES 160
#define ASSET_PAGE 4096
#define MAX_WIN 6
#define QUEUE 128        /* a pasted line, or fast typing into a busy app, must not be lost */
#define TITLE_H 30
#define BAR_H 30
#define W 1024
#define H 600
#define RADIUS 12

enum { OP_OPEN = 1, OP_WAIT = 2, OP_SET = 3 };
enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4, EV_CLOSE = 5 };
enum { BADGE_ALICE = 1, BADGE_MALLORY = 2, BADGE_INPUT = 3, BADGE_TERMINAL = 5, BADGE_SETTINGS = 6,
       BADGE_SECURITY = 7, BADGE_FILES = 9 };
enum { SET_BACKGROUND = 1 };
#define LAUNCH_FIRST 6  /* launch capabilities: Notes, Terminal, Settings, Security */
enum { F_UI = 1, F_UI_BOLD = 2, F_SMALL = 3, F_HUGE = 4, F_MEDIUM = 5 };

/* The dock. */
#define DOCK_N 5
#define ICON 52
#define ICON_GAP 16
#define DOCK_PAD 14
#define DOCK_W (DOCK_N * ICON + (DOCK_N - 1) * ICON_GAP + 2 * DOCK_PAD)
#define DOCK_H (ICON + 2 * DOCK_PAD - 4)
#define DOCK_X ((W - DOCK_W) / 2)
#define DOCK_Y (H - DOCK_H - 10)
static const char *const dock_names[DOCK_N] = {"Notes", "Files", "Terminal", "Settings", "Security"};
static const int dock_slot[DOCK_N] = {0, 9, 5, 6, 7};
static const int dock_launch[DOCK_N] = {LAUNCH_FIRST, LAUNCH_FIRST + 4, LAUNCH_FIRST + 1, LAUNCH_FIRST + 2,
                                        LAUNCH_FIRST + 3};

/* The backgrounds Settings offers: top and bottom of the gradient, and the glow's color. */
#define NTHEME 3
static const unsigned theme_top[NTHEME] = {0x1e204e, 0x24262c, 0x3a2a5a};
static const unsigned theme_bottom[NTHEME] = {0x0e4656, 0x0c0d10, 0xd98a5c};
static const unsigned theme_glow[NTHEME] = {0x606ee6, 0x5a6482, 0xe07aa0};

struct win {
    int used;
    u64 badge;
    int x, y;                   /* outer frame */
    struct surface content;
    char title[9];
    int closing;                /* closed on screen; the client hears EV_CLOSE when it next waits */
    u64 slot;                   /* reply slot + 1 while the client waits, else 0 */
    unsigned queue[QUEUE][3];    /* events waiting for the client (kind, a, b), oldest at qhead */
    int qhead, qlen;
};

/* Everything the server remembers lives in its data pages: user programs have no writable
   globals. */
struct state {
    struct surface screen;
    struct font ui, ui_bold, small, huge, medium;
    struct picture icons[DOCK_N];
    /* the background pattern: a color per row, a glow per column, and a 32 x 32 tile */
    unsigned bg_row[H];
    /* the glow, per column, ready to blend: the weight left for the row's color, and the
       glow color's red+blue and green already multiplied by the glow's weight */
    unsigned short glow_keep[W];
    unsigned glow_rb[W], glow_g[W];
    unsigned char bg_tile[32 * 32];
    unsigned char bg_dot_row[32];   /* does this row of the tile have any dot */
    struct win win[MAX_WIN];
    int z[MAX_WIN];             /* window indices, bottom to top */
    int nz;
    int px, py;                 /* pointer */
    int drag, grab_x, grab_y, drag_x0, drag_y0;
    int hover;                  /* dock icon under the pointer + 1, or 0 */
    int verified;               /* how many programs the boot checks passed */
    int theme;
    /* the capability list, as the kernel holds it: who granted each one (0: the server's
       own) and which window it shows (window + 1, or 0) */
    int ncaps;
    u64 cap_badge[64];
    int cap_win[64];
    /* how long drawing takes, for the log: the first full redraw (when the first window
       opens), the first click on a window, and the frames of each drag */
    int full_reported, click_reported;
    u64 drag_frames, drag_us;
};
_Static_assert(sizeof(struct state) <= 8 * 4096, "the server's state must fit in its 8 data pages");

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static const char *name_of(u64 badge) {
    return badge == BADGE_ALICE ? "alice" : badge == BADGE_MALLORY ? "mallory"
         : badge == BADGE_TERMINAL ? "Terminal" : badge == BADGE_SETTINGS ? "Settings"
         : badge == BADGE_SECURITY ? "Security" : badge == BADGE_FILES ? "Files" : "unknown";
}

/* The program slot a badge belongs to: the manifest gives each app its slot's number as its
   badge, except Notes (slot 0, badge 1). */
static int slot_of(u64 badge) {
    return badge == BADGE_ALICE ? 0
         : (badge >= BADGE_TERMINAL && badge <= BADGE_SECURITY) || badge == BADGE_FILES ? (int)badge : -1;
}

/* 0 not started, 1 running, 2 stopped, as the kernel sees slot k now. */
static u64 run_state(int k) { return k < 0 ? 0 : sys1(SYS_BOOTINFO, (u64)k).x[4]; }

/* The leanos mark: a rounded tile, indigo to teal, with a white lambda. */
static void logo(struct surface *s, int x, int y, int size) {
    round_gradient(s, x, y, size, size, size / 5, rgb(76, 78, 204), rgb(30, 168, 160));
    int u = size * 16 / 100; /* one percent of the tile, in 1/16 pixels */
    int stroke = size / 9 > 1 ? size / 9 : 1;
    thick_line(s, x * 16 + 30 * u, y * 16 + 20 * u, x * 16 + 72 * u, y * 16 + 80 * u, stroke, rgb(255, 255, 255));
    thick_line(s, x * 16 + 51 * u, y * 16 + 49 * u, x * 16 + 29 * u, y * 16 + 80 * u, stroke, rgb(255, 255, 255));
}

/* ---- the boot screen ---- */

#define SPLASH_MS 1600
#define PBAR_W 320
#define PBAR_H 6
#define PBAR_Y 432

/* Ease in and out: 0..1000 to 0..1000, slow at both ends. */
static int ease(int t) {
    if (t <= 0) return 0;
    if (t >= 1000) return 1000;
    return t * t / 1000 * (3000 - 2 * t) / 1000;
}

static unsigned splash_bg(int y) { return mix(rgb(12, 16, 30), rgb(22, 34, 60), (unsigned)(y * 255 / (H - 1))); }

static void splash_bar(struct state *st, int done /* 0..1000 */) {
    struct surface *s = &st->screen;
    int x = W / 2 - PBAR_W / 2;
    clip_to(s, x - 12, PBAR_Y - 12, PBAR_W + 24, PBAR_H + 24);
    for (int j = s->cy0; j < s->cy1; j++) fill(s, s->cx0, j, s->cx1 - s->cx0, 1, splash_bg(j));
    round_rect(s, x, PBAR_Y, PBAR_W, PBAR_H, PBAR_H / 2, rgb(42, 52, 82), 255);
    int filled = PBAR_W * done / 1000;
    if (filled >= PBAR_H) {
        for (int i = 0; i < filled; i++) {
            unsigned c = mix(rgb(88, 110, 240), rgb(80, 224, 204), (unsigned)(i * 255 / PBAR_W));
            if (i < PBAR_H / 2 || i >= filled - PBAR_H / 2) round_rect(s, x + i, PBAR_Y, 1, PBAR_H, 0, c, 210);
            else fill(s, x + i, PBAR_Y, 1, PBAR_H, c);
        }
        /* a soft glint riding the leading edge */
        for (int k = 5; k >= 1; k--)
            round_rect(s, x + filled - 3 - k, PBAR_Y - k + 3, 2 * k + 3, 2 * k, k, rgb(200, 255, 245), 24);
    }
    clip_all(s);
}

/* The boot checks: what the kernel decided about each task's code, from bootinfo. */
/* The programs checked at boot, and their slots; the apps are checked when they start. */
#define NPROG 6
static const char *const prog_names[NPROG] = {"Notes", "Display server", "Test: mallory", "Test: carol",
                                               "Input driver", "File server"};
static const int prog_slot[NPROG] = {0, 1, 2, 3, 4, 8};

static void hex8(char *out, u64 v) {
    for (int i = 0; i < 8; i++) out[i] = "0123456789abcdef"[(v >> (28 - 4 * i)) & 15];
    out[8] = 0;
}

static void check_mark(struct surface *s, int x, int y, int ok) {
    round_rect(s, x, y, 14, 14, 7, ok ? rgb(46, 180, 110) : rgb(220, 70, 70), 255);
    if (ok) {
        thick_line(s, (x + 3) * 16 + 8, (y + 7) * 16, (x + 6) * 16, (y + 10) * 16, 2, rgb(255, 255, 255));
        thick_line(s, (x + 6) * 16, (y + 10) * 16, (x + 11) * 16, (y + 4) * 16, 2, rgb(255, 255, 255));
    } else {
        thick_line(s, (x + 4) * 16, (y + 4) * 16, (x + 10) * 16, (y + 10) * 16, 2, rgb(255, 255, 255));
        thick_line(s, (x + 10) * 16, (y + 4) * 16, (x + 4) * 16, (y + 10) * 16, 2, rgb(255, 255, 255));
    }
}

#define CHECK_Y 462
#define CHECK_LINE 16

static void boot_check_line(struct state *st, int k, u64 verdict_code, u64 word) {
    struct surface *s = &st->screen;
    int x = W / 2 - 130, y = CHECK_Y + k * CHECK_LINE;
    check_mark(s, x, y, verdict_code == 1);
    font_text(s, &st->small, x + 22, y + 11, prog_names[k], rgb(200, 206, 222));
    char h[9];
    hex8(h, word);
    const char *verdict = verdict_code == 1 ? h : "refused";
    font_text(s, &st->small, x + 260 - font_width(&st->small, verdict), y + 11, verdict,
              verdict_code == 1 ? rgb(120, 132, 160) : rgb(236, 110, 110));
}

static void splash(struct state *st) {
    struct surface *s = &st->screen;
    clip_all(s);
    for (int y = 0; y < H; y++) fill(s, 0, y, W, 1, splash_bg(y));
    logo(s, W / 2 - 66, 150, 132);
    const char *name = "leanos";
    font_text(s, &st->huge, W / 2 - font_width(&st->huge, name) / 2, 356, name, rgb(244, 246, 252));
    const char *tag = "access control proved in Lean";
    font_text(s, &st->ui, W / 2 - font_width(&st->ui, tag) / 2, 396, tag, rgb(140, 152, 182));
    const char *who = "\xc2\xa9 2026 Keith Adler";
    font_text(s, &st->small, W / 2 - font_width(&st->small, who) / 2, H - 20, who, rgb(104, 114, 142));
    /* The kernel has already measured every program against the boot manifest; the bar
       walks through its verdicts, one program per step, eased. */
    u64 code[NPROG], word[NPROG];
    for (int k = 0; k < NPROG; k++) {
        struct res r = sys1(SYS_BOOTINFO, (u64)prog_slot[k]);
        code[k] = r.x[0] == OK ? r.x[1] : 0;
        word[k] = r.x[2];
    }
    u64 start = millis();
    int shown = 0;
    for (;;) {
        u64 t = millis() - start;
        int done = ease((int)(t * 1000 / SPLASH_MS));
        splash_bar(st, done);
        while (shown < NPROG && done >= (shown + 1) * 1000 / NPROG - 60) {
            boot_check_line(st, shown, code[shown], word[shown]);
            shown++;
        }
        if (t >= SPLASH_MS && shown == NPROG) break;
    }
    int ok = 0;
    for (int k = 0; k < NPROG; k++) ok += code[k] == 1;
    st->verified = ok;
}

/* ---- the desktop ---- */

static int outer_w(const struct win *w) { return w->content.w; }
static int outer_h(const struct win *w) { return w->content.h + TITLE_H; }
static int focused(struct state *st) { return st->nz ? st->z[st->nz - 1] : -1; }

static void traffic_lights(struct surface *s, int x, int y, int focus) {
    unsigned c[3] = {rgb(255, 95, 87), rgb(254, 188, 46), rgb(40, 200, 64)};
    for (int i = 0; i < 3; i++) {
        unsigned col = focus ? c[i] : rgb(206, 206, 210);
        round_rect(s, x + i * 20, y, 12, 12, 6, col, 255);
    }
}

static void draw_window(struct state *st, int k) {
    struct surface *s = &st->screen;
    struct win *w = &st->win[k];
    int ow = outer_w(w), oh = outer_h(w), x = w->x, y = w->y;
    int focus = focused(st) == k;
    shadow(s, x, y, ow, oh, RADIUS, 0);
    if (focus) shadow(s, x, y, ow, oh, RADIUS, 2);
    round_gradient(s, x, y, ow, TITLE_H + RADIUS, RADIUS, rgb(248, 248, 250), rgb(234, 234, 238));
    fill(s, x, y + TITLE_H - 1, ow, 1, rgb(214, 214, 220));
    traffic_lights(s, x + 12, y + 9, focus);
    int tw = font_width(&st->ui_bold, w->title);
    font_text(s, &st->ui_bold, x + ow / 2 - tw / 2, y + 20, w->title, focus ? rgb(40, 40, 46) : rgb(150, 150, 158));
    blit_rounded(s, x, y + TITLE_H, &w->content, x, y, ow, oh, RADIUS);
}

static void top_bar(struct state *st) {
    struct surface *s = &st->screen;
    fill_alpha(s, 0, 0, W, BAR_H, rgb(10, 12, 20), 120);
    fill_alpha(s, 0, BAR_H, W, 1, rgb(255, 255, 255), 28);
    logo(s, 10, 6, 18);
    font_text(s, &st->ui_bold, 36, 20, "leanos", rgb(245, 246, 250));
    int k = focused(st);
    if (k >= 0) font_text(s, &st->ui, 104, 20, st->win[k].title, rgb(200, 204, 214));
    const char *right = "access control proved in Lean";
    font_text(s, &st->small, W - 12 - font_width(&st->small, right), 19, right, rgb(190, 196, 210));
}

static int dock_icon_x(int i) { return DOCK_X + DOCK_PAD + i * (ICON + ICON_GAP); }

static int running(struct state *st, int i) {
    (void)st;
    return run_state(dock_slot[i]) == 1;
}

static void dock(struct state *st) {
    struct surface *s = &st->screen;
    round_rect(s, DOCK_X, DOCK_Y, DOCK_W, DOCK_H, 18, rgb(20, 22, 32), 110);
    for (int i = 0; i < DOCK_N; i++) {
        int lift = st->hover == i + 1 ? 4 : 0;
        icon(s, dock_icon_x(i), DOCK_Y + (DOCK_H - ICON) / 2 - 4 - lift, &st->icons[i]);
        if (running(st, i)) round_rect(s, dock_icon_x(i) + ICON / 2 - 2, DOCK_Y + DOCK_H - 7, 4, 4, 2, rgb(230, 232, 240), 255);
    }
    if (st->hover) {
        const char *label = dock_names[st->hover - 1];
        int lw = font_width(&st->ui, label) + 20;
        int lx = dock_icon_x(st->hover - 1) + ICON / 2 - lw / 2, ly = DOCK_Y - 34;
        round_rect(s, lx, ly, lw, 24, 8, rgb(24, 26, 36), 220);
        font_text(s, &st->ui, lx + 10, ly + 17, label, rgb(240, 242, 248));
    }
}

/* The background: indigo at the top to deep teal at the bottom, a soft glow toward the left,
   and a fine grid of dots over it. Built once; drawing a pixel is two multiply-adds (the
   same arithmetic as mix(), split so the glow's half is done once per column), and only
   the rows of the grid that have dots look at the dots. */
static void make_background(struct state *st) {
    int t = st->theme;
    for (int y = 0; y < H; y++) st->bg_row[y] = mix(theme_top[t], theme_bottom[t], (unsigned)(y * 255 / (H - 1)));
    for (int x = 0; x < W; x++) {
        int d = x < 300 ? 0 : x - 300;              /* glow: strongest on the left third */
        int a = 70 - d * 70 / (W - 300);
        unsigned u = (unsigned)(a < 0 ? 0 : a);     /* under 128, so mix() uses it as is */
        unsigned g = theme_glow[t];
        st->glow_keep[x] = (unsigned short)(256 - u);
        st->glow_rb[x] = (g & 0xFF00FFu) * u;
        st->glow_g[x] = (g & 0x00FF00u) * u;
    }
    for (int j = 0; j < 32; j++)
        for (int i = 0; i < 32; i++) {
            /* a dot at the tile's center, 1.6 px across, anti-aliased */
            int dx = (i - 16) * 16, dy = (j - 16) * 16;
            int d = (int)isqrt((unsigned)(dx * dx + dy * dy));
            int cover = 26 - d;                     /* radius 1.6 px in 1/16 px, with a soft edge */
            st->bg_tile[j * 32 + i] = (unsigned char)(cover <= 0 ? 0 : cover >= 16 ? 38 : cover * 38 / 16);
        }
    for (int j = 0; j < 32; j++) {
        st->bg_dot_row[j] = 0;
        for (int i = 0; i < 32; i++) st->bg_dot_row[j] |= st->bg_tile[j * 32 + i] != 0;
    }
}

static void background(struct state *st) {
    struct surface *s = &st->screen;
    for (int y = s->cy0; y < s->cy1; y++) {
        unsigned *row = s->px + y * s->stride;
        unsigned brb = st->bg_row[y] & 0xFF00FFu, bg = st->bg_row[y] & 0x00FF00u;
        for (int x = s->cx0; x < s->cx1; x++) {
            unsigned k = st->glow_keep[x];
            row[x] = (((brb * k + st->glow_rb[x]) >> 8) & 0xFF00FFu) | (((bg * k + st->glow_g[x]) >> 8) & 0x00FF00u);
        }
        if (!st->bg_dot_row[y & 31]) continue;
        const unsigned char *tile = st->bg_tile + (y & 31) * 32;
        for (int x = s->cx0; x < s->cx1; x++) {
            unsigned dot = tile[x & 31];
            if (dot) row[x] = mix(row[x], rgb(200, 220, 255), dot);
        }
    }
}

/* Redraw one rectangle of the screen: background, bar, windows bottom to top, dock, pointer. */
static void composite(struct state *st, int x, int y, int w, int h) {
    struct surface *s = &st->screen;
    clip_to(s, x, y, w, h);
    background(st);
    if (s->cy0 < BAR_H + 1) top_bar(st);
    for (int i = 0; i < st->nz; i++) {
        struct win *wn = &st->win[st->z[i]];
        if (wn->x - 10 < s->cx1 && wn->x + outer_w(wn) + 10 > s->cx0 &&
            wn->y - 10 < s->cy1 && wn->y + outer_h(wn) + 14 > s->cy0)
            draw_window(st, st->z[i]);
    }
    if (s->cy1 > DOCK_Y - 40) dock(st);
    pointer(s, st->px, st->py);
    clip_all(s);
}

static void composite_window(struct state *st, int k) {
    struct win *w = &st->win[k];
    composite(st, w->x - 10, w->y - 10, outer_w(w) + 20, outer_h(w) + 24);
}

static void raise(struct state *st, int k) {
    int at = -1;
    for (int i = 0; i < st->nz; i++) if (st->z[i] == k) at = i;
    if (at < 0) return;
    for (int i = at; i < st->nz - 1; i++) st->z[i] = st->z[i + 1];
    st->z[st->nz - 1] = k;
}

/* Bring window k to the front and redraw only what changed: its area, and the area of the
   window that had the focus (its title bar dims). */
static void bring_to_front(struct state *st, int k) {
    int old = focused(st);
    raise(st, k);
    if (old >= 0 && old != k) composite_window(st, old);
    composite_window(st, k);
    /* the menu bar names the focused window */
    composite(st, 0, 0, W, BAR_H + 1);
}

static int window_at(struct state *st, int x, int y) {
    for (int i = st->nz - 1; i >= 0; i--) {
        struct win *w = &st->win[st->z[i]];
        if (x >= w->x && x < w->x + outer_w(w) && y >= w->y && y < w->y + outer_h(w)) return st->z[i];
    }
    return -1;
}

static int dock_at(int x, int y) {
    if (y < DOCK_Y || y >= DOCK_Y + DOCK_H) return 0;
    for (int i = 0; i < DOCK_N; i++)
        if (x >= dock_icon_x(i) && x < dock_icon_x(i) + ICON) return i + 1;
    return 0;
}

/* Give window k's client an event: now, if it is waiting, or when it next asks. */
static void deliver_event(struct win *w, u64 kind, u64 a, u64 b) {
    if (w->slot) {
        sys(SYS_REPLY, w->slot - 1, kind, a, b, 0);
        w->slot = 0;
    } else if (w->qlen < QUEUE) {
        int at = (w->qhead + w->qlen++) % QUEUE;
        w->queue[at][0] = (unsigned)kind;   /* keys and screen positions fit in 32 bits */
        w->queue[at][1] = (unsigned)a;
        w->queue[at][2] = (unsigned)b;
    }
}

static void redraw_all(struct state *st) { composite(st, 0, 0, W, H); }

/* The kernel removed capability i: everything after it moves down one place. */
static void cap_forget(struct state *st, int i) {
    for (int j = i; j < st->ncaps - 1; j++) {
        st->cap_badge[j] = st->cap_badge[j + 1];
        st->cap_win[j] = st->cap_win[j + 1];
    }
    st->ncaps--;
}

static void cap_drop(struct state *st, int i) {
    sys1(SYS_DROP, (u64)i);
    cap_forget(st, i);
}

/* Take window k off the screen and stop mapping its pixels. */
static void hide(struct state *st, int k) {
    int at = -1;
    for (int i = 0; i < st->nz; i++) if (st->z[i] == k) at = i;
    if (at >= 0) {
        for (int i = at; i < st->nz - 1; i++) st->z[i] = st->z[i + 1];
        st->nz--;
    }
    if (st->drag == k + 1) st->drag = 0;
    sys2(SYS_UNMAP, WIN_PAGE + WIN_MAX_PAGES * (u64)k, WIN_MAX_PAGES);
}

/* Forget window k. A reply slot still held for it is answered, which frees it. */
static void release(struct state *st, int k) {
    struct win *w = &st->win[k];
    hide(st, k);
    for (int i = st->ncaps - 1; i >= 0; i--)
        if (st->cap_win[i] == k + 1) cap_drop(st, i);
    if (w->slot) sys(SYS_REPLY, w->slot - 1, EV_CLOSE, 0, 0, 0);
    w->slot = 0;
    w->used = 0;
    w->closing = 0;
}

/* The close button: the window goes now, and its client hears EV_CLOSE. */
static void close_window(struct state *st, struct line *l, int k) {
    struct win *w = &st->win[k];
    put_s(l, "display: closed ");
    put_s(l, name_of(w->badge));
    put_s(l, "'s window");
    say(l);
    if (w->slot) release(st, k);
    else {
        hide(st, k);
        w->closing = 1;
    }
    redraw_all(st);
}

/* Windows whose client has stopped (it exited, or faulted) are closed. */
static void forget_stopped(struct state *st, struct line *l) {
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (!w->used || run_state(slot_of(w->badge)) != 2) continue;
        if (!w->closing) {
            put_s(l, "display: ");
            put_s(l, name_of(w->badge));
            put_s(l, " stopped; its window is gone");
            say(l);
        }
        release(st, k);
        redraw_all(st);
    }
}

/* Dock item i: show the app's window, or start the app. */
static void launch(struct state *st, struct line *l, int i) {
    int slot = dock_slot[i];
    if (slot < 0) {
        put_s(l, "display: ");
        put_s(l, dock_names[i]);
        put_s(l, " is not installed yet");
        say(l);
        return;
    }
    for (int k = 0; k < MAX_WIN; k++)
        if (st->win[k].used && !st->win[k].closing && slot_of(st->win[k].badge) == slot) {
            bring_to_front(st, k);
            return;
        }
    if (run_state(slot) == 1) return; /* started, not showing a window yet */
    /* Starting takes back what the last run shared, its window's pixels too: drop it first. */
    for (int k = 0; k < MAX_WIN; k++)
        if (st->win[k].used && slot_of(st->win[k].badge) == slot) release(st, k);
    struct res r = sys1(SYS_START, (u64)dock_launch[i]);
    /* The kernel took back every capability to the app's frames: those it granted. */
    if (r.status == OK)
        for (int j = st->ncaps - 1; j >= 0; j--)
            if (st->cap_badge[j] && slot_of(st->cap_badge[j]) == slot) cap_forget(st, j);
    put_s(l, "display: start ");
    put_s(l, dock_names[i]);
    put_s(l, outcome(r.status));
    say(l);
    if (r.status == OK && sys1(SYS_BOOTINFO, (u64)slot).x[1] != 1) {
        put_s(l, "display: ");
        put_s(l, dock_names[i]);
        put_s(l, " was refused: it does not match the boot manifest");
        say(l);
    }
    composite(st, DOCK_X - 60, DOCK_Y - 44, DOCK_W + 120, DOCK_H + 44);
}

/* x.y ms, from microseconds */
static void put_ms(struct line *l, u64 us) {
    put_dec(l, us / 1000);
    put_s(l, ".");
    put_dec(l, us / 100 % 10);
    put_s(l, " ms");
}

static void on_input(struct state *st, struct line *l, u64 kind, u64 a, u64 b) {
    if (kind == EV_KEY) {
        int k = focused(st);
        if (k < 0) return;
        deliver_event(&st->win[k], EV_KEY, a, 0);
        if (a == '\r' || a == '\n') put_s(l, "display: key return to ");
        else {
            put_s(l, "display: key '");
            char ch[2] = {a >= 32 && a < 127 ? (char)a : '?', 0};
            put_s(l, ch);
            put_s(l, "' to ");
        }
        put_s(l, name_of(st->win[k].badge));
        say(l);
        return;
    }
    int ox = st->px, oy = st->py;
    st->px = a < W ? (int)a : W - 1;
    st->py = b < H ? (int)b : H - 1;
    if (kind == EV_DOWN) {
        int d = dock_at(st->px, st->py);
        if (d) launch(st, l, d - 1);
        int k = d ? -1 : window_at(st, st->px, st->py);
        if (k >= 0) {
            struct win *w = &st->win[k];
            if (st->px >= w->x + 12 && st->px < w->x + 24 && st->py >= w->y + 9 && st->py < w->y + 21) {
                close_window(st, l, k);
                return;
            }
            u64 t0 = micros();
            bring_to_front(st, k);
            if (!st->click_reported) {
                st->click_reported = 1;
                put_s(l, "display: a click on a window redrew in ");
                put_ms(l, micros() - t0);
                say(l);
            }
            if (st->py >= w->y + TITLE_H)
                deliver_event(w, EV_DOWN, (u64)(st->px - w->x), (u64)(st->py - w->y - TITLE_H));
            if (st->py < w->y + TITLE_H) {
                st->drag = k + 1;
                st->grab_x = st->px - w->x;
                st->grab_y = st->py - w->y;
                st->drag_x0 = w->x;
                st->drag_y0 = w->y;
            }
        }
    } else if (kind == EV_MOVE && st->drag) {
        struct win *w = &st->win[st->drag - 1];
        int nx = st->px - st->grab_x, ny = st->py - st->grab_y;
        if (ny < BAR_H + 2) ny = BAR_H + 2;
        int oxw = w->x, oyw = w->y;
        w->x = nx;
        w->y = ny;
        int x0 = (oxw < nx ? oxw : nx) - 10, y0 = (oyw < ny ? oyw : ny) - 10;
        int x1 = (oxw > nx ? oxw : nx) + outer_w(w) + 10, y1 = (oyw > ny ? oyw : ny) + outer_h(w) + 14;
        u64 t0 = micros();
        composite(st, x0, y0, x1 - x0, y1 - y0);
        st->drag_us += micros() - t0;
        st->drag_frames++;
    } else if (kind == EV_MOVE) {
        int hv = dock_at(st->px, st->py);
        if (hv != st->hover) {
            st->hover = hv;
            composite(st, DOCK_X - 60, DOCK_Y - 44, DOCK_W + 120, DOCK_H + 44);
        }
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
            put_s(l, "display: the drag drew ");
            put_dec(l, st->drag_frames);
            put_s(l, " frames, ");
            put_ms(l, st->drag_frames ? st->drag_us / st->drag_frames : 0);
            put_s(l, " each");
            say(l);
        }
        st->drag = 0;
        st->drag_frames = st->drag_us = 0;
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
    if (k < 0 || slot_of(badge) < 0 || w == 0 || h == 0 || w > 900 || h > 480 || info.x[2] != 0 ||
        info.x[3] < need || need > WIN_MAX_PAGES ||
        sys2(SYS_MAP, cap - 1, WIN_PAGE + WIN_MAX_PAGES * (u64)k).status != OK) {
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
    wn->content = surface_of((unsigned *)PAGE(WIN_PAGE + WIN_MAX_PAGES * (u64)k), (int)w, (int)h);
    for (int i = 0; i < 8; i++) wn->title[i] = (char)(title >> (8 * i));
    wn->title[8] = 0;
    wn->x = 96 + 40 * k;
    wn->y = 76 + 36 * k;
    if (wn->x + (int)w > W - 8) wn->x = W - 8 - (int)w;
    if (wn->y + (int)h + TITLE_H > DOCK_Y - 8) wn->y = DOCK_Y - 8 - (int)h - TITLE_H;
    wn->slot = 0;
    wn->closing = 0;
    st->cap_win[cap - 1] = k + 1;
    wn->qhead = wn->qlen = 0;
    st->z[st->nz++] = k;
    u64 t0 = micros();
    redraw_all(st);
    if (!st->full_reported) {
        st->full_reported = 1;
        put_s(l, "display: a full redraw took ");
        put_ms(l, micros() - t0);
        say(l);
    }
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
        if (w->closing) {
            sys(SYS_REPLY, slot - 1, EV_CLOSE, 0, 0, 0);
            w->used = 0;
            w->closing = 0;
            return;
        }
        if (dirty) composite_window(st, k);
        if (w->qlen) {
            unsigned *e = w->queue[w->qhead];
            sys(SYS_REPLY, slot - 1, e[0], e[1], e[2], 0);
            w->qhead = (w->qhead + 1) % QUEUE;
            w->qlen--;
        } else {
            w->slot = slot;
        }
        return;
    }
    sys(SYS_REPLY, slot - 1, 0, 0, 0, 0); /* no window: nothing to wait for */
}

/* SET: only Settings may change the desktop. */
static void on_set(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], what = r->x[3], value = r->x[4], slot = r->x[6];
    if (badge != BADGE_SETTINGS || what != SET_BACKGROUND || value >= NTHEME) {
        put_s(l, "display: ");
        put_s(l, name_of(badge));
        put_s(l, " may not change the desktop; refused");
        say(l);
        sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        return;
    }
    st->theme = (int)value;
    make_background(st);
    redraw_all(st);
    put_s(l, "display: background ");
    put_dec(l, value);
    put_s(l, ", as Settings asked");
    say(l);
    sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    struct state *st = (struct state *)DATA;
    if (sys2(SYS_MAP, FRAMEBUFFER, FB_PAGE).status != OK) {
        put_s(&l, "display: no framebuffer to draw on");
        say(&l);
        exit_task();
    }
    /* The assets: a read-only view of the start of the spare run. */
    struct res ro = sys(SYS_DERIVE, 3, R, 0, 200, 0);
    sys2(SYS_MAP, ro.x[1], ASSET_PAGE);
    st->ncaps = (int)ro.x[1] + 1;
    for (int i = 0; i < st->ncaps; i++) { st->cap_badge[i] = 0; st->cap_win[i] = 0; }
    const unsigned char *assets = (const unsigned char *)PAGE(ASSET_PAGE);
    st->ui = font_of(assets, F_UI);
    st->ui_bold = font_of(assets, F_UI_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->huge = font_of(assets, F_HUGE);
    st->medium = font_of(assets, F_MEDIUM);
    for (int i = 0; i < DOCK_N; i++) st->icons[i] = picture_of(assets, ASSET_ICON, 10 + i);

    st->screen = surface_of((unsigned *)PAGE(FB_PAGE), W, H);
    st->theme = 0;
    st->full_reported = st->click_reported = 0;
    st->drag_frames = st->drag_us = 0;
    make_background(st);
    st->px = W / 2;
    st->py = H / 2;
    splash(st);
    put_s(&l, "display: boot checks shown: ");
    put_dec(&l, (u64)st->verified);
    put_s(&l, " verified, ");
    put_dec(&l, (u64)(NPROG - st->verified));
    put_s(&l, " refused");
    say(&l);
    put_s(&l, "display: boot logo drawn");
    say(&l);
    for (u64 t = millis(); millis() - t < 400;) {} /* hold the full bar a moment */

    redraw_all(st);
    put_s(&l, "display: desktop drawn on the 1024x600 framebuffer");
    say(&l);

    for (;;) {
        struct res r = sys1(SYS_RECV, ENDPOINT);
        u64 badge = r.x[1], op = r.x[2], slot = r.x[6], grant = r.x[5];
        if (grant) {
            /* a granted capability lands at the end of the list */
            st->ncaps = (int)grant;
            st->cap_badge[grant - 1] = badge;
            st->cap_win[grant - 1] = 0;
        }
        if (badge == BADGE_INPUT && !slot) {
            on_input(st, &l, op, r.x[3], r.x[4]);
        } else if (slot && op == OP_OPEN && r.x[5]) {
            on_open(st, &l, &r);
        } else if (slot && op == OP_WAIT) {
            on_wait(st, &r);
        } else if (slot && op == OP_SET) {
            on_set(st, &l, &r);
        } else {
            put_s(&l, "display: ");
            put_s(&l, name_of(badge));
            put_s(&l, " asked for a window but sent no pixels; ignored");
            say(&l);
            if (slot) sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        }
        /* A grant that did not become a window is not kept. */
        if (grant && st->cap_win[grant - 1] == 0) cap_drop(st, (int)grant - 1);
        forget_stopped(st, &l);
    }
}
