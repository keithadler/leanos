/* The display server. It owns the framebuffer (capability 5) and nothing else can reach it.

   Clients call it. RAISE (7): w1 w2 = a card file's name, bring its windows forward.
   PENDING (8): Apps asks which pinned program the dock wants started. OPEN: w0 = 1, w1 = width << 16 | height, w2 = up to 8 bytes of title,
   with a read-only capability to the window's pixels; the reply is 0 on success, and the
   window's number as its program knows it: 0 for its first, then the lowest it is not
   using. WAIT: w0 = 2, w1 = the windows the client redrew, a bit per number (1: its first);
   the reply comes when there is an event for any of the client's windows (w0 = kind | the
   window's number << 8, w1, w2), the oldest first. The server never blocks on a client: it
   holds each program's one waiting call until it has something to say. CLOSE (12): w1 = one
   of the caller's window numbers; the window goes at once, and the reply is 0 (1: the
   caller has no window of that number).

   The kernel gives it 8 reply slots (maxCallers) and it may show 12 windows, so it holds at
   most HOLD_MAX (7) waiting programs' calls, and one slot is always free for the next call.
   When a WAIT would take an 8th, the program that has waited longest hears no event
   (EV_NONE) and is parked: it asks again a moment later (app_wait), and while the slots are
   still taken it is answered at once, with its events if it has any, else with none again.
   A parked program that gets an event is held again when it next waits, in place of the one
   that has waited longest. If a receive ever finds the slots full all the same, the one
   that has waited longest is let go the same way: before, the display retried that receive
   for ever, and no key or click reached anyone again.

   A slot started again (Terminal's or Apps' exec, or its own start of an app) frees the
   reply slots held for its last run and takes back the pixels that run lent. So before it
   answers any call the display forgets the windows of stopped programs, and the launchers
   call it just before they start a slot; if a start gets past that all the same, what the
   kernel hands it next shows it, and it forgets that run's windows unanswered and undrawn
   (see "runs the kernel replaced").

   The input driver sends it keys and mouse reports (badge 3). Keys go to the focused window;
   a click focuses and raises a window, and dragging its title bar moves it. The sender's
   badge, which the kernel sets, names every window, so no client can pass for another, and
   a window's number means something only with its program's badge: no program can name
   another's window. A click inside a window goes to its client (EV_DOWN, window
   coordinates); a click on the red button asks the client to close (EV_CLOSE, with that
   window's number), and the window goes from the screen at once, and from the table when
   its client hears it.

   It holds a launch capability for each app (capabilities 6 to 10: Notes, Terminal,
   Settings, Security, Files). Clicking an app in the dock starts it if it is not running; the
   kernel first takes back everything the app's last run shared, including its window, so
   the server drops that window before it asks. SET (w0 = 3) changes the desktop, and only
   Settings (badge 6) may ask: the background, or the time zone (user/zone.h).

   The time zone is the display's to keep. ZONE (9): anyone may ask it, and hears the minutes
   east of UTC (biased); Clock asks every second. The display cannot write the card, so when
   Settings changes the zone it asks Apps, which can, to save it (as it asks Apps to start a
   pinned program); at boot Apps reads it back and gives it here, once.

   The clipboard is the display's too, and text moves between programs only by the user's
   hand (user/app.h). Ctrl+C (byte 3), or Edit, Copy in the menu bar, asks the window in
   front for its text (EV_COPY), and the display takes a copy (COPY, w0 = 10, 16 bytes in w1
   w2 to a call) only from that window's badge, only until the copy ends, and only within
   COPY_MS of asking; a copy at any other time, from anyone, is refused. Ctrl+V (byte 22), or
   Edit, Paste, hands what was copied to the window in front, and only to it, as a run of
   EV_PASTE events in its queue. No request reads the clipboard. Neither key reaches an app.

   It keeps a copy of its own capability list's layout (which app granted each capability,
   and for which window), so it can drop a window's capability when the window goes, drop
   at once any grant it did not ask for, and know which capabilities the kernel takes back
   when it starts an app again. Its capability list never grows without bound.

   Its fonts and icons were loaded at boot into the start of its spare run (capability 3),
   which it maps read-only. The desktop's background is a pattern it computes itself. */
#include "lib.h"
#include "gfx.h"
#include "assets.h"
#include "zone.h"

/* Its code must fit the 16-page code run (user/user.ld), and at -O2 the compiler inlines and
   unrolls freely. So the code that runs once per message or less (setup, the requests, the
   menus, the log) is compiled for size: COLD. The drawing, which runs per pixel, is not; and
   drag_frame, called from the main loop, is kept out of it so it is never compiled for size
   with it. `make` prints each program's size and what is left of its run. */
#define COLD __attribute__((cold, minsize))

/* Text widths and rounded rectangles are asked for in many places, the drawing's too: one
   copy of each, not one inlined in every caller (what costs is the pixels, not the call). */
__attribute__((noinline)) static int text_w(const struct font *f, const char *str) { return font_width(f, str); }
__attribute__((noinline)) static void rounded(struct surface *s, int x, int y, int w, int h, int r, unsigned c,
                                              unsigned alpha) {
    round_rect(s, x, y, w, h, r, c, alpha);
}

#define FRAMEBUFFER 5
#define FB_PAGE 1024
#define WIN_PAGE 2048   /* window k's pixels are mapped at WIN_PAGE + WIN_MAX_PAGES k */
#define WIN_MAX_PAGES 184
#define ASSET_PAGE 4800   /* after the windows: WIN_PAGE + WIN_MAX_PAGES * MAX_WIN = 4256 */
#define MAX_WIN 12
#define WIN_TABLE_PAGE 5100   /* the window table: the spare run's last 28 pages, read-write */
#define ICON_PAGE 4300        /* window k's icon, lent by its program: pages 4300 + 4 k */
#define MINI 40               /* a running program's icon in the dock */
#define MINI_GAP 8
#define DOCK_AREA_X 0         /* the part of the screen the dock and its labels can cover */
#define QUEUE 128        /* a pasted line, or fast typing into a busy app, must not be lost */
#define HOLD_MAX 7       /* waiting programs' calls held at once: one fewer than the kernel's 8 reply slots */
#define NSLOT 17         /* program slots: a badge's slot_of */
#define EV_WIN 8         /* an event's kind word: the kind, and the window's number from this bit up */
#define TITLE_H 30
#define BAR_H 30
#define W 1024
#define H 600
#define RADIUS 12

enum { OP_OPEN = 1, OP_WAIT = 2, OP_SET = 3, OP_POLL = 4, OP_ICON = 5, OP_START = 6, OP_RAISE = 7, OP_PENDING = 8,
       OP_ZONE = 9, OP_COPY = 10, OP_CLOSE = 12 };
/* 11 is no request: programs ask it to show that no request reads the clipboard (mallory, tour) */
enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4, EV_CLOSE = 5, EV_LAUNCH = 6, EV_COPY = 7, EV_PASTE = 8 };
enum { KEY_COPY = 3, KEY_PASTE = 22 };   /* Ctrl+C, Ctrl+V */
#define CLIP_MAX 4096     /* as user/app.h */
#define COPY_MS 2000
enum { BADGE_USB = 17, BADGE_ALICE = 1, BADGE_MALLORY = 2, BADGE_INPUT = 3, BADGE_TERMINAL = 5, BADGE_SETTINGS = 6,
       BADGE_SECURITY = 7, BADGE_FILES = 9 };
enum { SET_BACKGROUND = 1, SET_ZONE = 2 };
#define LAUNCH_FIRST 6  /* launch capabilities: Notes, Terminal, Settings, Security */
#define POWER 11        /* the power capability: switch off, restart */
#define APPS_LAUNCH 12  /* the launch capability for Apps (slot 16) */
enum { POWER_OFF = 0, POWER_RESTART = 1 };
enum { F_UI = 1, F_UI_BOLD = 2, F_SMALL = 3, F_HUGE = 4, F_MEDIUM = 5 };

/* The dock. */
#define DOCK_N 6        /* the built-in apps */
#define NPIN 4          /* programs from the card kept in the dock */
#define DOCK_ALL (DOCK_N + NPIN)
#define ICON 52
#define ICON_GAP 14
#define DOCK_PAD 14
#define DOCK_W (DOCK_ALL * ICON + (DOCK_ALL - 1) * ICON_GAP + 2 * DOCK_PAD)
#define DOCK_H (ICON + 2 * DOCK_PAD - 4)
#define DOCK_X ((W - DOCK_W) / 2)
#define DOCK_Y (H - DOCK_H - 10)
static const char *const dock_names[DOCK_ALL] = {"Notes", "Files", "Terminal", "Settings", "Security", "Apps",
                                                  "Clock", "Calculator", "Tour", "Web"};
/* The pinned programs' files on the card. The display cannot read the card or start a
   program from it: a click asks Apps, which can, to start it (OP_PENDING, EV_LAUNCH). */
static const char *const pin_files[NPIN] = {"clock", "calc", "tour", "web"};
#define APPS_DOCK 5
static const int dock_slot[DOCK_N] = {0, 9, 5, 6, 7, 16};
static const int dock_launch[DOCK_N] = {LAUNCH_FIRST, LAUNCH_FIRST + 4, LAUNCH_FIRST + 1, LAUNCH_FIRST + 2,
                                        LAUNCH_FIRST + 3, APPS_LAUNCH};

/* The backgrounds Settings offers: top and bottom of the gradient, and the glow's color. */
#define NTHEME 3
static const unsigned theme_top[NTHEME] = {0x1e204e, 0x24262c, 0x3a2a5a};
static const unsigned theme_bottom[NTHEME] = {0x0e4656, 0x0c0d10, 0xd98a5c};
static const unsigned theme_glow[NTHEME] = {0x606ee6, 0x5a6482, 0xe07aa0};

struct win {
    int used;
    u64 badge;
    int id;                     /* its number as its program knows it (OPEN's answer, in its events) */
    int x, y;                   /* outer frame */
    struct surface content;
    char title[9];
    int closing;                /* closed on screen; the client hears EV_CLOSE when it next waits */
    unsigned close_seq;         /* when the close button was clicked (the event count) */
    struct picture icon;        /* the icon a program from the card lent (OP_ICON), or none */
    char prog[16];              /* and the card file it came from, or "" */
    int pages;                  /* how many pages its pixels were lent in (for the log) */
    int unsaid;                 /* its opening is not logged yet: a card program's name comes after */
    u64 hash;                   /* the first word of its slot's measured hash when it opened */
    unsigned queue[QUEUE][4];    /* events waiting for the client (kind, a, b, when), oldest at qhead */
    int qhead, qlen;
    /* a paste on its way: what was copied when the user pasted here, handed out 16 bytes to
       an event when an EV_PASTE in the queue comes up */
    int paste_len, paste_at;
    char paste[CLIP_MAX];
};

/* Everything the server remembers lives in its data pages: user programs have no writable
   globals. */
struct state {
    unsigned char ignored[32];   /* requests not understood, per badge, so a flood logs once */
    unsigned char said[32];      /* refused windows, raises and closes logged, per badge: a few, not a flood */
    struct surface screen;
    struct font ui, ui_bold, small, huge, medium;
    struct picture icons[DOCK_ALL];
    char pending[16];           /* a pinned program to start when Apps next asks */
    char bar_time[24];          /* the menu bar's clock ("Wed Sep 23  14:05"), empty until known */
    u64 bar_minute;             /* the minute it shows */
    long zone;                  /* the time zone, minutes east of UTC (user/zone.h) */
    int zone_unsaved;           /* Settings changed it, and Apps has not been asked to save it */
    int zone_restore;           /* Apps, started at boot, may give the zone saved on the card */
    /* the background pattern: a color per row, a glow per column, and a 32 x 32 tile */
    unsigned bg_row[H];
    /* the glow, per column, ready to blend: the weight left for the row's color, and the
       glow color's red+blue and green already multiplied by the glow's weight */
    unsigned short glow_keep[W];
    unsigned glow_rb[W], glow_g[W];
    unsigned char bg_tile[32 * 32];
    unsigned char bg_dot_row[32];   /* does this row of the tile have any dot */
    struct win *win;            /* MAX_WIN of them, in the spare run (WIN_TABLE_PAGE) */
    int z[MAX_WIN];             /* window indices, bottom to top */
    int nz;
    int px, py;                 /* pointer */
    int drag, grab_x, grab_y, drag_x0, drag_y0;
    int hover;                  /* dock icon under the pointer + 1, or 0 */
    int verified;               /* how many programs the boot checks passed */
    int theme;
    /* the capability list, as the kernel holds it: who granted each one (0: the server's
       own) and which window it shows (window + 1, or 0) */
    int ncaps, own_caps;        /* how many, and how many are its own (the first) */
    int grant_at;               /* where the message being handled put its grant, or -1 */
    u64 cap_badge[64];
    int cap_win[64];
    /* how long drawing takes, for the log: the first full redraw (when the first window
       opens), the first click on a window, and the frames of each drag */
    int full_reported, click_reported;
    int menu;                   /* the menu that is open: 0 none, 1 leanos, 2 Edit */
    int menu_x;                 /* where the Edit menu opened */
    /* the clipboard, and the copy the display asked for: which window (+ 1, or 0), its
       badge, when, and the text so far */
    int clip_len, copy_win, copy_len;
    u64 copy_badge, copy_at;
    unsigned char copy_refused[32];   /* refused copies, per badge, so a flood logs a few */
    char clip[CLIP_MAX], copy_buf[CLIP_MAX];
    u64 drag_frames, drag_us;
    int drag_pending, pend_x, pend_y;   /* a drag move not drawn yet, and where the window was */
    u64 waits;                  /* waits held so far: each program's held_at */
    int parked_said;            /* the log has said once that programs are parked */
    /* per program slot (slot_of its badge): its one waiting call (reply slot + 1, or 0),
       when it was held (a count, to find the one held longest), and whether it was let go
       with no event while HOLD_MAX were held (it asks again soon) */
    u64 hold[NSLOT], held_at[NSLOT];
    unsigned char parked[NSLOT];
    unsigned events;            /* events queued so far: which of a program's is oldest */
};
_Static_assert(sizeof(struct state) <= 8 * 4096, "the server's state must fit in its 8 data pages");

COLD static void say(struct line *l) { put_s(l, "\n"); flush(l); }

COLD static const char *name_of(u64 badge) {
    return badge == BADGE_ALICE ? "alice" : badge == BADGE_MALLORY ? "mallory"
         : badge == BADGE_TERMINAL ? "Terminal" : badge == BADGE_SETTINGS ? "Settings"
         : badge == BADGE_SECURITY ? "Security" : badge == BADGE_FILES ? "Files"
         : badge >= 10 && badge <= 15 ? "a program from the SD card" : badge == 16 ? "Apps" : "unknown";
}

/* A window's name in the log: the card file its program came from, once it is known, or
   its program's (name_of). */
COLD static const char *win_name(const struct win *w) { return w->prog[0] ? w->prog : name_of(w->badge); }

/* The program slot a badge belongs to: the manifest gives each app its slot's number as its
   badge, except Notes (slot 0, badge 1). */
static int slot_of(u64 badge) {
    return badge == BADGE_ALICE ? 0
         : (badge >= BADGE_TERMINAL && badge <= BADGE_SECURITY) || badge == BADGE_FILES ||
           (badge >= 10 && badge <= 16) ? (int)badge : -1;
}

/* 0 not started, 1 running, 2 stopped, as the kernel sees slot k now. */
COLD static u64 run_state(int k) { return k < 0 ? 0 : sys1(SYS_BOOTINFO, (u64)k).x[4]; }

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
COLD static int ease(int t) {
    if (t <= 0) return 0;
    if (t >= 1000) return 1000;
    return t * t / 1000 * (3000 - 2 * t) / 1000;
}

COLD static unsigned splash_bg(int y) { return mix(rgb(12, 16, 30), rgb(22, 34, 60), (unsigned)(y * 255 / (H - 1))); }

COLD static void splash_bar(struct state *st, int done /* 0..1000 */) {
    struct surface *s = &st->screen;
    int x = W / 2 - PBAR_W / 2;
    clip_to(s, x - 12, PBAR_Y - 12, PBAR_W + 24, PBAR_H + 24);
    for (int j = s->cy0; j < s->cy1; j++) fill(s, s->cx0, j, s->cx1 - s->cx0, 1, splash_bg(j));
    rounded(s, x, PBAR_Y, PBAR_W, PBAR_H, PBAR_H / 2, rgb(42, 52, 82), 255);
    int filled = PBAR_W * done / 1000;
    if (filled >= PBAR_H) {
        for (int i = 0; i < filled; i++) {
            unsigned c = mix(rgb(88, 110, 240), rgb(80, 224, 204), (unsigned)(i * 255 / PBAR_W));
            if (i < PBAR_H / 2 || i >= filled - PBAR_H / 2) rounded(s, x + i, PBAR_Y, 1, PBAR_H, 0, c, 210);
            else fill(s, x + i, PBAR_Y, 1, PBAR_H, c);
        }
        /* a soft glint riding the leading edge */
        for (int k = 5; k >= 1; k--)
            rounded(s, x + filled - 3 - k, PBAR_Y - k + 3, 2 * k + 3, 2 * k, k, rgb(200, 255, 245), 24);
    }
    clip_all(s);
}

/* The boot checks: what the kernel decided about each task's code, from bootinfo. */
/* The programs checked at boot, and their slots; the apps are checked when they start. */
#define NPROG 6
static const char *const prog_names[NPROG] = {"Notes", "Display server", "Test: mallory", "Test: carol",
                                               "Input driver", "File server"};
static const int prog_slot[NPROG] = {0, 1, 2, 3, 4, 8};

COLD static void hex8(char *out, u64 v) {
    for (int i = 0; i < 8; i++) out[i] = "0123456789abcdef"[(v >> (28 - 4 * i)) & 15];
    out[8] = 0;
}

COLD static void check_mark(struct surface *s, int x, int y, int ok) {
    rounded(s, x, y, 14, 14, 7, ok ? rgb(46, 180, 110) : rgb(220, 70, 70), 255);
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

COLD static void boot_check_line(struct state *st, int k, u64 verdict_code, u64 word) {
    struct surface *s = &st->screen;
    int x = W / 2 - 130, y = CHECK_Y + k * CHECK_LINE;
    check_mark(s, x, y, verdict_code == 1);
    font_text(s, &st->small, x + 22, y + 11, prog_names[k], rgb(200, 206, 222));
    char h[9];
    hex8(h, word);
    const char *verdict = verdict_code == 1 ? h : "refused";
    font_text(s, &st->small, x + 260 - text_w(&st->small, verdict), y + 11, verdict,
              verdict_code == 1 ? rgb(120, 132, 160) : rgb(236, 110, 110));
}

COLD static void splash(struct state *st) {
    struct surface *s = &st->screen;
    clip_all(s);
    for (int y = 0; y < H; y++) fill(s, 0, y, W, 1, splash_bg(y));
    logo(s, W / 2 - 66, 150, 132);
    const char *name = "leanos";
    font_text(s, &st->huge, W / 2 - text_w(&st->huge, name) / 2, 356, name, rgb(244, 246, 252));
    const char *tag = "access control proved in Lean";
    font_text(s, &st->ui, W / 2 - text_w(&st->ui, tag) / 2, 396, tag, rgb(140, 152, 182));
    const char *who = "\xc2\xa9 2026 Keith Adler";
    font_text(s, &st->small, W / 2 - text_w(&st->small, who) / 2, H - 20, who, rgb(104, 114, 142));
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
        rounded(s, x + i * 20, y, 12, 12, 6, col, 255);
    }
}

/* The icon for window k: the one its program lent, or the dock's for a built-in app. */
static const struct picture *win_icon(struct state *st, int k) {
    struct win *w = &st->win[k];
    if (w->icon.px) return &w->icon;
    for (int i = 0; i < DOCK_N; i++)
        if (dock_slot[i] >= 0 && slot_of(w->badge) == dock_slot[i]) return &st->icons[i];
    return 0;
}

static void draw_window(struct state *st, int k) {
    struct surface *s = &st->screen;
    struct win *w = &st->win[k];
    int ow = outer_w(w), oh = outer_h(w), x = w->x, y = w->y;
    int focus = focused(st) == k;
    shadow(s, x, y, ow, oh, RADIUS, 0);
    if (focus) shadow(s, x, y, ow, oh, RADIUS, 2);
    /* The rest only inside the window's frame: its buttons and its title (the program's
       words) must not reach past a narrow window onto what is beside it, where clicks go to
       another window. */
    int cx0 = s->cx0, cy0 = s->cy0, cx1 = s->cx1, cy1 = s->cy1;
    if (s->cx0 < x) s->cx0 = x;
    if (s->cy0 < y) s->cy0 = y;
    if (s->cx1 > x + ow) s->cx1 = x + ow;
    if (s->cy1 > y + oh) s->cy1 = y + oh;
    if (s->cx0 < s->cx1 && s->cy0 < s->cy1) {
        round_gradient(s, x, y, ow, TITLE_H + RADIUS, RADIUS, rgb(248, 248, 250), rgb(234, 234, 238));
        fill(s, x, y + TITLE_H - 1, ow, 1, rgb(214, 214, 220));
        traffic_lights(s, x + 12, y + 9, focus);
        int tw = text_w(&st->ui_bold, w->title);
        const struct picture *ic = win_icon(st, k);
        int tx = x + ow / 2 - tw / 2 + (ic ? 11 : 0);
        if (ic) icon_scaled(s, tx - 24, y + 5, 20, ic);
        font_text(s, &st->ui_bold, tx, y + 20, w->title, focus ? rgb(40, 40, 46) : rgb(150, 150, 158));
        blit_rounded(s, x, y + TITLE_H, &w->content, x, y, ow, oh, RADIUS);
    }
    s->cx0 = cx0;
    s->cy0 = cy0;
    s->cx1 = cx1;
    s->cy1 = cy1;
}

/* The Edit menu's name in the menu bar, after the name of the window in front (-1: no window). */
static int edit_x(struct state *st) {
    int k = focused(st);
    return k < 0 ? -1 : 104 + text_w(&st->ui, st->win[k].title) + 22;
}

COLD static int on_edit(struct state *st, int x) {
    int e = edit_x(st);
    return e >= 0 && x >= e - 10 && x < e + text_w(&st->ui, "Edit") + 10;
}

static void top_bar(struct state *st) {
    struct surface *s = &st->screen;
    fill_alpha(s, 0, 0, W, BAR_H, rgb(10, 12, 20), 120);
    fill_alpha(s, 0, BAR_H, W, 1, rgb(255, 255, 255), 28);
    logo(s, 10, 6, 18);
    font_text(s, &st->ui_bold, 36, 20, "leanos", rgb(245, 246, 250));
    int k = focused(st);
    if (k >= 0) {
        font_text(s, &st->ui, 104, 20, st->win[k].title, rgb(200, 204, 214));
        int e = edit_x(st), ew = text_w(&st->ui, "Edit");
        if (st->menu == 2) rounded(s, e - 8, 4, ew + 16, BAR_H - 8, 6, rgb(255, 255, 255), 40);
        font_text(s, &st->ui, e, 20, "Edit", rgb(236, 238, 244));
    }
    const char *right = "access control proved in Lean";
    int rx = W - 12;
    if (st->bar_time[0]) {
        rx -= text_w(&st->ui_bold, st->bar_time);
        font_text(s, &st->ui_bold, rx, 20, st->bar_time, rgb(245, 246, 250));
        rx -= 18;
    }
    font_text(s, &st->small, rx - text_w(&st->small, right), 19, right, rgb(190, 196, 210));
}

static void composite(struct state *st, int x, int y, int w, int h);

/* The menu bar's clock: the kernel's time of day in the time zone, to the minute. Every
   zone is a whole number of minutes from UTC, so its minutes turn over with UTC's. */
COLD static void bar_show(struct state *st, u64 wall, int again) {
    u64 minute = wall / 60;
    if (minute != st->bar_minute || again) {
        st->bar_minute = minute;
        struct date d = date_of(local_of(wall, st->zone));
        struct line l = {.n = 0};
        const char *m = month_names[d.month - 1];
        const char *wd = day_names[d.weekday];
        char a[4] = {wd[0], wd[1], wd[2], 0}, b[4] = {m[0], m[1], m[2], 0};
        put_s(&l, a);
        put_s(&l, " ");
        put_s(&l, b);
        put_s(&l, " ");
        put_dec(&l, (u64)d.day);
        put_s(&l, "  ");
        put_two(&l, (u64)d.h);
        put_s(&l, ":");
        put_two(&l, (u64)d.m);
        int n = (int)(l.n < sizeof st->bar_time - 1 ? l.n : sizeof st->bar_time - 1);
        for (int i = 0; i < n; i++) st->bar_time[i] = l.b[i];
        st->bar_time[n] = 0;
        composite(st, 0, 0, W, BAR_H + 1);
    }
}

/* The zone, said: and what the menu bar shows with it, beside UTC, for the log. */
COLD static void say_zone(struct state *st, struct line *l, const char *why) {
    put_s(l, "display: time zone ");
    put_zone(l, st->zone);
    put_s(l, why);
    u64 wall = sys0(SYS_TIME).x[6];
    if (wall) {
        bar_show(st, wall, 1);
        put_s(l, "; the menu bar shows ");
        put_s(l, st->bar_time);
        put_s(l, " at Unix time ");
        put_dec(l, wall);
    } else put_s(l, "; the time of day is not known yet");
    say(l);
}

/* Returns the milliseconds until the next minute (or a few seconds, while the time is not
   known). The first time it is known, the log says what the menu bar shows. */
COLD static u64 bar_clock(struct state *st) {
    u64 wall = sys0(SYS_TIME).x[6];
    if (!wall) return 5000;
    if (!st->bar_time[0]) {
        struct line l = {.n = 0};
        say_zone(st, &l, "");
    } else bar_show(st, wall, 0);
    return (60 - wall % 60) * 1000 + 50;
}

static int dock_icon_x(int i) { return DOCK_X + DOCK_PAD + i * (ICON + ICON_GAP); }

static int same_name(const char *a, const char *b) {
    int i = 0;
    while (i < 15 && a[i] && a[i] == b[i]) i++;
    return i == 15 || a[i] == b[i];
}

/* The open window of the program from card file `name`, or -1. */
COLD static int window_of(struct state *st, const char *name) {
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (w->used && !w->closing && w->prog[0] && same_name(w->prog, name)) return k;
    }
    return -1;
}

static int pinned(const struct win *w) {
    for (int p = 0; p < NPIN; p++) if (w->prog[0] && same_name(w->prog, pin_files[p])) return 1;
    return 0;
}

static int running(struct state *st, int i) {
    if (i >= DOCK_N) return window_of(st, pin_files[i - DOCK_N]) >= 0;
    return run_state(dock_slot[i]) == 1;
}

/* Is window k shown, and the first in the table of its program's shown windows? */
static int first_of(struct state *st, int k) {
    struct win *w = &st->win[k];
    if (!w->used || w->closing) return 0;
    for (int j = 0; j < k; j++)
        if (st->win[j].used && !st->win[j].closing && st->win[j].badge == w->badge) return 0;
    return 1;
}

/* Programs from the card with a window, one icon each (its first window's), in the order
   they appear in the dock (after the built-in apps, so those never move). */
static int dock_extras(struct state *st, int *which) {
    int n = 0;
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (first_of(st, k) && w->badge >= 10 && w->badge <= 15 && !pinned(w)) which[n++] = k;
    }
    return n;
}

/* Running programs sit to the right of the dock; when there are more than fit, they overlap. */
#define EXTRA_X0 (DOCK_X + DOCK_W - DOCK_PAD + 14)
static int extra_step(int n) {
    int room = W - 8 - MINI - EXTRA_X0;
    return n > 1 && room / (n - 1) < MINI + MINI_GAP ? room / (n - 1) : MINI + MINI_GAP;
}
static int extra_x_of(int i, int n) { return EXTRA_X0 + i * extra_step(n); }

static void dock(struct state *st) {
    struct surface *s = &st->screen;
    int which[MAX_WIN], n = dock_extras(st, which);
    int width = DOCK_W + (n ? 14 + (n - 1) * extra_step(n) + MINI + 4 : 0);
    rounded(s, DOCK_X, DOCK_Y, width, DOCK_H, 18, rgb(20, 22, 32), 110);
    if (n) fill_alpha(s, DOCK_X + DOCK_W - DOCK_PAD + 6, DOCK_Y + 14, 1, DOCK_H - 28, rgb(255, 255, 255), 60);
    for (int i = 0; i < n; i++) {
        struct win *w = &st->win[which[i]];
        int x = extra_x_of(i, n), y = DOCK_Y + (DOCK_H - MINI) / 2 - 4 - (st->hover == 101 + which[i] ? 4 : 0);
        const struct picture *ic = win_icon(st, which[i]);
        if (ic) icon_scaled(s, x, y, MINI, ic);
        else {
            rounded(s, x + 2, y + 2, MINI - 4, MINI - 4, 10, rgb(58, 110, 230), 255);
            char ch[2] = {w->title[0], 0};
            font_text(s, &st->ui_bold, x + MINI / 2 - text_w(&st->ui_bold, ch) / 2, y + MINI / 2 + 6, ch,
                      rgb(255, 255, 255));
        }
        rounded(s, x + MINI / 2 - 2, DOCK_Y + DOCK_H - 7, 4, 4, 2, rgb(230, 232, 240), 255);
    }
    for (int i = 0; i < DOCK_ALL; i++) {
        int lift = st->hover == i + 1 ? 4 : 0;
        icon(s, dock_icon_x(i), DOCK_Y + (DOCK_H - ICON) / 2 - 4 - lift, &st->icons[i]);
        if (running(st, i)) rounded(s, dock_icon_x(i) + ICON / 2 - 2, DOCK_Y + DOCK_H - 7, 4, 4, 2, rgb(230, 232, 240), 255);
    }
    if (st->hover) {
        int extra = st->hover > 100;
        const char *label = extra ? st->win[st->hover - 101].title : dock_names[st->hover - 1];
        int cx = 0;
        if (extra) {
            for (int i = 0; i < n; i++) if (which[i] == st->hover - 101) cx = extra_x_of(i, n) + MINI / 2;
        } else cx = dock_icon_x(st->hover - 1) + ICON / 2;
        int lw = text_w(&st->ui, label) + 20;
        int lx = cx - lw / 2, ly = DOCK_Y - 34;
        rounded(s, lx, ly, lw, 24, 8, rgb(24, 26, 36), 220);
        font_text(s, &st->ui, lx + 10, ly + 17, label, rgb(240, 242, 248));
    }
}

/* The background: indigo at the top to deep teal at the bottom, a soft glow toward the left,
   and a fine grid of dots over it. Built once; drawing a pixel is two multiply-adds (the
   same arithmetic as mix(), split so the glow's half is done once per column), and only
   the rows of the grid that have dots look at the dots. */
COLD static void make_background(struct state *st) {
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

/* The menus: the leanos menu, under the logo (Restart, Shut down), and the Edit menu, under
   its name (Copy, Paste: the same as Ctrl+C and Ctrl+V). */
#define MENU_X 6
#define MENU_Y (BAR_H + 4)
#define MENU_W 190
#define MENU_ITEM 28
#define MENU_H (2 * MENU_ITEM + 12)
static const char *const menu_items[2][2] = {{"Restart", "Shut down"}, {"Copy", "Paste"}};
static const char *const edit_keys[2] = {"Ctrl+C", "Ctrl+V"};

static int menu_left(struct state *st, int m) { return m == 2 ? st->menu_x : MENU_X; }

static void menu(struct state *st) {
    struct surface *s = &st->screen;
    int x = menu_left(st, st->menu);
    shadow(s, x, MENU_Y, MENU_W, MENU_H, 10, 0);
    rounded(s, x, MENU_Y, MENU_W, MENU_H, 10, rgb(248, 248, 250), 255);
    for (int i = 0; i < 2; i++) {
        int y = MENU_Y + 6 + i * MENU_ITEM + 19;
        font_text(s, &st->ui, x + 16, y, menu_items[st->menu - 1][i], rgb(30, 30, 36));
        if (st->menu == 2)
            font_text(s, &st->small, x + MENU_W - 16 - text_w(&st->small, edit_keys[i]), y, edit_keys[i],
                      rgb(140, 144, 156));
    }
}

/* Which item (0, 1) of the open menu is at (x, y), or -1. */
COLD static int menu_at(struct state *st, int x, int y) {
    int x0 = menu_left(st, st->menu);
    if (x < x0 || x >= x0 + MENU_W || y < MENU_Y + 6 || y >= MENU_Y + 6 + 2 * MENU_ITEM) return -1;
    return (y - MENU_Y - 6) / MENU_ITEM;
}

/* The part of a window nothing shows through: all of it but the rounded corners, as two
   rectangles (a wide one without the corner rows, a tall one without the corner columns).
   Which of them best overlaps (x0, y0)-(x1, y1) goes in *o, with how much it overlaps. */
static long opaque_part(const struct win *w, int x0, int y0, int x1, int y1, int o[4]) {
    int ow = outer_w(w), oh = outer_h(w);
    int r[2][4] = {{w->x, w->y + RADIUS, w->x + ow, w->y + oh - RADIUS},
                   {w->x + RADIUS, w->y, w->x + ow - RADIUS, w->y + oh}};
    long best = 0;
    for (int k = 0; k < 2; k++) {
        int a0 = r[k][0] > x0 ? r[k][0] : x0, b0 = r[k][1] > y0 ? r[k][1] : y0;
        int a1 = r[k][2] < x1 ? r[k][2] : x1, b1 = r[k][3] < y1 ? r[k][3] : y1;
        long area = a1 > a0 && b1 > b0 ? (long)(a1 - a0) * (b1 - b0) : 0;
        if (area > best) { best = area; o[0] = a0; o[1] = b0; o[2] = a1; o[3] = b1; }
    }
    return best;
}

/* Draw (x0, y0)-(x1, y1) from window z[from] up: background and bar only if from is 0. */
static void composite_from(struct state *st, int x0, int y0, int x1, int y1, int from) {
    struct surface *s = &st->screen;
    clip_to(s, x0, y0, x1 - x0, y1 - y0);
    if (from == 0) {
        background(st);
        if (s->cy0 < BAR_H + 1) top_bar(st);
    }
    for (int i = from; i < st->nz; i++) {
        struct win *wn = &st->win[st->z[i]];
        if (wn->x - 10 < s->cx1 && wn->x + outer_w(wn) + 10 > s->cx0 &&
            wn->y - 10 < s->cy1 && wn->y + outer_h(wn) + 14 > s->cy0)
            draw_window(st, st->z[i]);
    }
    if (s->cy1 > DOCK_Y - 40) dock(st);
    if (st->menu && s->cx0 < menu_left(st, st->menu) + MENU_W + 12 && s->cx1 > menu_left(st, st->menu) - 12 &&
        s->cy0 < MENU_Y + MENU_H + 12)
        menu(st);
    pointer(s, st->px, st->py);
    clip_all(s);
}

/* Redraw one rectangle of the screen: background, bar, windows bottom to top, dock, pointer.
   What an opaque window covers is drawn from that window up, skipping everything under it;
   the rest of the rectangle (at most four pieces) is done the same way with the windows
   below. */
static void composite_depth(struct state *st, int x0, int y0, int x1, int y1, int depth) {
    if (x0 < 0) x0 = 0;
    if (y0 < 0) y0 = 0;
    if (x1 > W) x1 = W;
    if (y1 > H) y1 = H;
    if (x0 >= x1 || y0 >= y1) return;
    int o[4], top = -1;
    long whole = (long)(x1 - x0) * (y1 - y0);
    for (int i = st->nz - 1; i >= 0 && depth < 4; i--) {
        long a = opaque_part(&st->win[st->z[i]], x0, y0, x1, y1, o);
        if (a == whole || a >= 64 * 64) {   /* worth splitting for */
            top = i;
            break;
        }
    }
    if (top < 0) {
        composite_from(st, x0, y0, x1, y1, 0);
        return;
    }
    composite_from(st, o[0], o[1], o[2], o[3], top);
    composite_depth(st, x0, y0, x1, o[1], depth + 1);            /* above */
    composite_depth(st, x0, o[3], x1, y1, depth + 1);            /* below */
    composite_depth(st, x0, o[1], o[0], o[3], depth + 1);        /* left */
    composite_depth(st, o[2], o[1], x1, o[3], depth + 1);        /* right */
}

static void composite(struct state *st, int x, int y, int w, int h) {
    composite_depth(st, x, y, x + w, y + h, 0);
}

static void composite_window(struct state *st, int k) {
    struct win *w = &st->win[k];
    composite(st, w->x - 10, w->y - 10, outer_w(w) + 20, outer_h(w) + 24);
}

COLD static void raise(struct state *st, int k) {
    int at = -1;
    for (int i = 0; i < st->nz; i++) if (st->z[i] == k) at = i;
    if (at < 0) return;
    for (int i = at; i < st->nz - 1; i++) st->z[i] = st->z[i + 1];
    st->z[st->nz - 1] = k;
}

/* Bring window k to the front and redraw only what changed: its area, and the area of the
   window that had the focus (its title bar dims). */
COLD static void bring_to_front(struct state *st, int k) {
    int old = focused(st);
    raise(st, k);
    if (old >= 0 && old != k) composite_window(st, old);
    composite_window(st, k);
    /* the menu bar names the focused window */
    composite(st, 0, 0, W, BAR_H + 1);
}

/* Bring every window of window k's program to the front, in the order they were in, so
   the one of them that was in front last is in front now (the dock, RAISE: a program, not
   a window, was asked for), and redraw what changed. */
COLD static void raise_program(struct state *st, int k) {
    u64 badge = st->win[k].badge;
    int old = focused(st), n = st->nz;
    for (int i = 0, seen = 0; seen < n; seen++) {
        int j = st->z[i];
        if (st->win[j].badge == badge) raise(st, j);   /* to the top: the rest move down */
        else i++;
    }
    if (old >= 0 && st->win[old].badge != badge) composite_window(st, old);
    for (int i = 0; i < st->nz; i++)
        if (st->win[st->z[i]].badge == badge) composite_window(st, st->z[i]);
    composite(st, 0, 0, W, BAR_H + 1);
}

COLD static int window_at(struct state *st, int x, int y) {
    for (int i = st->nz - 1; i >= 0; i--) {
        struct win *w = &st->win[st->z[i]];
        if (x >= w->x && x < w->x + outer_w(w) && y >= w->y && y < w->y + outer_h(w)) return st->z[i];
    }
    return -1;
}

/* What in the dock is at (x, y): a built-in app (1 + its index), a running program's
   window (101 + the window), or nothing (0). */
COLD static int dock_at(struct state *st, int x, int y) {
    if (y < DOCK_Y || y >= DOCK_Y + DOCK_H) return 0;
    for (int i = 0; i < DOCK_ALL; i++)
        if (x >= dock_icon_x(i) && x < dock_icon_x(i) + ICON) return i + 1;
    int which[MAX_WIN], n = dock_extras(st, which);
    for (int i = 0; i < n; i++)
        if (x >= extra_x_of(i, n) && x < extra_x_of(i, n) + MINI) return 101 + which[i];
    return 0;
}

COLD static void forget(struct state *st, int k);

/* The next event for the program with this badge: the oldest waiting for any of its
   windows, taken from that window's queue, with the window's number in its kind word; 0 if
   there is none. An EV_PASTE in a queue stands for the whole paste, and stays at the front
   until the last of it (fewer than 16 bytes) is handed out. A window closed on screen (its
   close button) has EV_CLOSE after the events it already had; handing that out forgets it. */
COLD __attribute__((noinline)) static int next_event(struct state *st, u64 badge, u64 e[3]) {
    int k = -1;
    unsigned at = 0;
    for (int j = 0; j < MAX_WIN; j++) {
        struct win *c = &st->win[j];
        if (!c->used || c->badge != badge || (!c->qlen && !c->closing)) continue;
        unsigned when = c->qlen ? c->queue[c->qhead][3] : c->close_seq;
        if (k < 0 || (int)(when - at) < 0) { k = j; at = when; }
    }
    if (k < 0) return 0;
    struct win *w = &st->win[k];
    u64 id = (u64)w->id << EV_WIN;
    if (!w->qlen) {
        e[0] = EV_CLOSE | id;
        e[1] = e[2] = 0;
        forget(st, k);
        return 1;
    }
    unsigned *q = w->queue[w->qhead];
    e[0] = q[0] | id;
    e[1] = q[1];
    e[2] = q[2];
    if (q[0] == EV_PASTE) {
        int n = 0;
        e[1] = e[2] = 0;
        for (; n < 16 && w->paste_at < w->paste_len; n++)
            e[1 + n / 8] |= (u64)(unsigned char)w->paste[w->paste_at++] << (8 * (n % 8));
        if (n == 16) return 1;
        w->paste_len = w->paste_at = 0;
    }
    w->qhead = (w->qhead + 1) % QUEUE;
    w->qlen--;
    return 1;
}

/* Give window k's client an event: now, if it is waiting, or when it next asks. */
COLD static void deliver_event(struct state *st, int k, u64 kind, u64 a, u64 b) {
    struct win *w = &st->win[k];
    if (w->qlen < QUEUE) {
        int at = (w->qhead + w->qlen++) % QUEUE;
        w->queue[at][0] = (unsigned)kind;   /* keys and screen positions fit in 32 bits */
        w->queue[at][1] = (unsigned)a;
        w->queue[at][2] = (unsigned)b;
        w->queue[at][3] = ++st->events;
    }
    int p = slot_of(w->badge);
    u64 e[3];
    if (st->hold[p] && next_event(st, w->badge, e)) {
        sys(SYS_REPLY, st->hold[p] - 1, e[0], e[1], e[2], 0);
        st->hold[p] = 0;
    }
}

COLD static void redraw_all(struct state *st) { composite(st, 0, 0, W, H); }

/* The kernel removed capability i: everything after it moves down one place, the grant
   the message being handled carries too. */
COLD static void cap_forget(struct state *st, int i) {
    if (i < st->grant_at) st->grant_at--;
    for (int j = i; j < st->ncaps - 1; j++) {
        st->cap_badge[j] = st->cap_badge[j + 1];
        st->cap_win[j] = st->cap_win[j + 1];
    }
    st->ncaps--;
}

COLD static void cap_drop(struct state *st, int i) {
    sys1(SYS_DROP, (u64)i);
    cap_forget(st, i);
}

/* Take window k off the screen and stop mapping its pixels. */
COLD static void hide(struct state *st, int k) {
    int at = -1;
    for (int i = 0; i < st->nz; i++) if (st->z[i] == k) at = i;
    if (at >= 0) {
        for (int i = at; i < st->nz - 1; i++) st->z[i] = st->z[i + 1];
        st->nz--;
    }
    if (st->drag == k + 1) st->drag = 0;
    if (st->hover == 101 + k) st->hover = 0;
    sys2(SYS_UNMAP, WIN_PAGE + WIN_MAX_PAGES * (u64)k, WIN_MAX_PAGES);
}

/* Forget window k: off the screen, its capabilities (pixels, icon) let go, its place in the
   table free. */
COLD static void forget(struct state *st, int k) {
    struct win *w = &st->win[k];
    hide(st, k);
    for (int i = st->ncaps - 1; i >= 0; i--)
        if (st->cap_win[i] == k + 1) cap_drop(st, i);
    w->used = 0;
    w->closing = 0;
    w->paste_len = w->paste_at = 0;
    if (st->copy_win == k + 1) st->copy_win = 0;
}

/* Forget window k. A call its program is still held in is answered (EV_CLOSE, for this
   window), which frees the reply slot. */
COLD static void release(struct state *st, int k) {
    u64 id = (u64)st->win[k].id << EV_WIN;
    int p = slot_of(st->win[k].badge);
    forget(st, k);
    if (st->hold[p]) sys(SYS_REPLY, st->hold[p] - 1, EV_CLOSE | id, 0, 0, 0);
    st->hold[p] = 0;
}

/* The close button: the window goes now, and its client hears EV_CLOSE (after the events
   its window already had). */
COLD static void close_window(struct state *st, struct line *l, int k) {
    struct win *w = &st->win[k];
    put_s(l, "display: closed ");
    put_s(l, name_of(w->badge));
    put_s(l, "'s window");
    say(l);
    if (st->hold[slot_of(w->badge)]) release(st, k);   /* it waits: nothing else is queued */
    else {
        hide(st, k);
        w->closing = 1;
        w->close_seq = ++st->events;
    }
    redraw_all(st);
}

/* Windows whose client has stopped (it exited, or faulted) are closed. */
COLD static void forget_stopped(struct state *st, struct line *l) {
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

static void say3(struct line *l, const char *a, const char *b, const char *c);

/* ---- runs the kernel replaced ----

   Starting a program slot again (Terminal's and Apps' exec, or the display's own start) frees
   every reply slot any task holds for the slot's last run, and takes back every capability
   into its memory, with the mappings (the kernel's `start`). The display learns of a run
   only through bootinfo (not started, running, stopped) and the measured hash, which is the
   same for the same program: there is no run number to ask for. So it keeps its records
   true three ways. Before it answers any call it forgets the windows of stopped programs
   (forget_stopped), and a launcher calls it after it finds a slot stopped and before it
   starts it (app_before_start in user/app.h), so the display has let go of the last run
   before the kernel does. Beyond that, what the kernel hands it shows what it missed: */

/* The badge of the programs in slot p (slot_of's inverse). */
static u64 badge_in(int p) { return p == 0 ? BADGE_ALICE : (u64)p; }

/* A call in reply slot k: the calls the display holds are all in slots of their own, so any
   record it still has of slot k is of a call the kernel has dropped (its caller's slot was
   started again). It is forgotten, not answered: an answer now would reach the new caller. */
COLD static void claim_slot(struct state *st, struct line *l, u64 slot) {
    for (int p = 0; p < NSLOT; p++) {
        if (st->hold[p] != slot) continue;
        st->hold[p] = 0;
        say3(l, "the kernel dropped the call held for ", name_of(badge_in(p)), "'s last run; forgot it");
    }
}

/* How many capabilities the kernel says it holds: as many as it counts, or fewer. */
COLD static int caps_now(struct state *st) {
    int n = st->ncaps;
    while (n > 0 && sys1(SYS_CAPINFO, (u64)n - 1).status != OK) n--;
    return n;
}

/* The kernel holds only `real` of its capabilities: a slot was started again while the
   display thought its last run was still there, and it took back the capabilities that
   run had granted (a window's pixels, its icon) and the mappings with them. The windows of
   that slot are forgotten without being drawn, dropped or answered. The slot is the one
   whose grants number what is missing; if several do, the one whose program changed (its
   hash); if the display still cannot tell, it lets every capability but its own go, and
   every window closes. Returns how many capabilities it let go (the grant being handled,
   after them, moves down as many places). */
COLD static int lost_runs(struct state *st, struct line *l, int real) {
    int miss = st->ncaps - real, pick = -1, fits = 0, changed = -1, nchanged = 0;
    for (int s = 0; s < 17; s++) {
        int n = 0;
        for (int i = 0; i < st->ncaps; i++) n += st->cap_badge[i] && slot_of(st->cap_badge[i]) == s;
        if (n != miss) continue;
        fits++;
        pick = s;
        u64 h = sys1(SYS_BOOTINFO, (u64)s).x[2];
        for (int k = 0; k < MAX_WIN; k++)
            if (st->win[k].used && slot_of(st->win[k].badge) == s && st->win[k].hash != h) {
                changed = s;
                nchanged++;
                break;
            }
    }
    if (fits > 1) pick = nchanged == 1 ? changed : -1;
    int dropped = 0;
    if (pick >= 0) {
        put_s(l, "display: slot ");
        put_dec(l, (u64)pick);
        say3(l, " was started again unseen; forgot its last run's windows", "", "");
        for (int k = 0; k < MAX_WIN; k++) {
            struct win *w = &st->win[k];
            if (!w->used || slot_of(w->badge) != pick) continue;
            hide(st, k);
            w->used = w->closing = w->paste_len = w->paste_at = 0;
            if (st->copy_win == k + 1) st->copy_win = 0;
        }
        for (int i = st->ncaps - 1; i >= 0; i--)
            if (st->cap_badge[i] && slot_of(st->cap_badge[i]) == pick) cap_forget(st, i);
        st->hold[pick] = 0;
    } else {
        say3(l, "a slot was started again unseen, and it cannot tell which: every window closes", "", "");
        for (int i = real - 1; i >= st->own_caps; i--, dropped++) sys1(SYS_DROP, (u64)i);
        st->ncaps = st->own_caps;
        for (int k = 0; k < MAX_WIN; k++) if (st->win[k].used) release(st, k);
    }
    redraw_all(st);
    return dropped;
}

/* Dock item i: show the app's windows, or start the app. */
COLD static void launch(struct state *st, struct line *l, int i) {
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
            raise_program(st, k);
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
    composite(st, DOCK_AREA_X, DOCK_Y - 44, W, DOCK_H + 44);
}

/* A pinned program: bring its windows forward, or have Apps start it. Apps reads the card
   and holds the open slots' launch capabilities; the display holds neither. If Apps is
   showing its window, it gets the name as an event; if not, the display starts Apps, which
   asks for the name first thing (OP_PENDING), starts the program, and leaves quietly. */
COLD static void open_pinned(struct state *st, struct line *l, int p) {
    int k = window_of(st, pin_files[p]);
    if (k >= 0) {
        raise_program(st, k);
        return;
    }
    put_s(l, "display: open ");
    put_s(l, pin_files[p]);
    put_s(l, " from the dock");
    say(l);
    u64 a = 0, b = 0;
    for (int i = 0; i < 8 && pin_files[p][i]; i++) {
        u64 c = (u64)(unsigned char)pin_files[p][i] << (8 * (i % 4));
        if (i < 4) a |= c;
        else b |= c;
    }
    for (int j = 0; j < MAX_WIN; j++) {
        struct win *w = &st->win[j];
        if (w->used && !w->closing && slot_of(w->badge) == 16) {
            deliver_event(st, j, EV_LAUNCH, a, b);
            return;
        }
    }
    int n = 0;
    for (; n < 15 && pin_files[p][n]; n++) st->pending[n] = pin_files[p][n];
    st->pending[n] = 0;
    launch(st, l, APPS_DOCK);
}

/* PENDING: Apps asks, as it starts, whether the dock sent it a program to start. Only Apps
   gets an answer; the name goes in two message words. */
COLD static void on_pending(struct state *st, struct res *r) {
    u64 w[2] = {0, 0};
    if (r->x[1] == 16) {
        st->zone_restore = same_name(st->pending, "@startup");
        if (same_name(st->pending, "@zone")) st->zone_unsaved = 0;
        for (int i = 0; i < 15 && st->pending[i]; i++) w[i / 8] |= (u64)(unsigned char)st->pending[i] << (8 * (i % 8));
        st->pending[0] = 0;
    }
    sys(SYS_REPLY, r->x[6] - 1, 0, w[0], w[1], 0);
}

/* x.y ms, from microseconds */
COLD static void put_ms(struct line *l, u64 us) {
    put_dec(l, us / 1000);
    put_s(l, ".");
    put_dec(l, us / 100 % 10);
    put_s(l, " ms");
}

/* Draw the dragged window where it now is. */
__attribute__((noinline)) static void drag_frame(struct state *st) {
    if (!st->drag_pending || !st->drag) {
        st->drag_pending = 0;
        return;
    }
    st->drag_pending = 0;
    struct win *w = &st->win[st->drag - 1];
    int oxw = st->pend_x, oyw = st->pend_y, nx = w->x, ny = w->y;
    /* The window with its shadow, before and after: redraw what it uncovered (the old
       box less the new, at most four pieces), then the new box. */
    int ow = outer_w(w) + 20, oh = outer_h(w) + 24;
    int ax0 = oxw - 10, ay0 = oyw - 10, ax1 = ax0 + ow, ay1 = ay0 + oh;
    int bx0 = nx - 10, by0 = ny - 10, bx1 = bx0 + ow, by1 = by0 + oh;
    u64 t0 = micros();
    if (bx0 >= ax1 || bx1 <= ax0 || by0 >= ay1 || by1 <= ay0) {
        composite_depth(st, ax0, ay0, ax1, ay1, 0);
    } else {
        int cy0 = ay0 > by0 ? ay0 : by0, cy1 = ay1 < by1 ? ay1 : by1;
        composite_depth(st, ax0, ay0, ax1, cy0, 0);                    /* above the new box */
        composite_depth(st, ax0, cy1, ax1, ay1, 0);                    /* below it */
        composite_depth(st, ax0, cy0, bx0 > ax0 ? bx0 : ax0, cy1, 0);  /* left of it */
        composite_depth(st, bx1 < ax1 ? bx1 : ax1, cy0, ax1, cy1, 0);  /* right of it */
    }
    composite_depth(st, bx0, by0, bx1, by1, 0);
    st->drag_us += micros() - t0;
    st->drag_frames++;
}

/* ---- copy and paste: only by the user's hand ---- */

COLD __attribute__((noinline)) static void copy_bytes(char *to, const char *from, int n) {
    for (int i = 0; i < n; i++) to[i] = from[i];
}

/* "display: " a b c, on a line of its own, or after what the line already has (kept out of
   line: it is said from many places). */
COLD __attribute__((noinline)) static void say3(struct line *l, const char *a, const char *b, const char *c) {
    if (!l->n) put_s(l, "display: ");
    put_s(l, a);
    put_s(l, b);
    put_s(l, c);
    say(l);
}

/* The user asked to copy (Ctrl+C, or Edit, Copy): ask the window in front for its text. From
   now until the copy ends, or COPY_MS pass, that window's badge, and no other, may send it.
   Asked again while its answer may still be arriving, the display waits for that one: a new
   start in the middle would keep only the answer's tail. */
COLD static void copy_ask(struct state *st, struct line *l) {
    int k = focused(st);
    if (k < 0) return;
    struct win *w = &st->win[k];
    if (st->copy_win == k + 1 && millis() - st->copy_at <= COPY_MS) {
        say3(l, "copy: still waiting for ", name_of(w->badge), "");
        return;
    }
    st->copy_win = k + 1;
    st->copy_badge = w->badge;
    st->copy_at = millis();
    st->copy_len = 0;
    deliver_event(st, k, EV_COPY, 0, 0);
    say3(l, "copy: asked ", name_of(w->badge), " for its text");
}

/* The user asked to paste (Ctrl+V, or Edit, Paste): what was copied goes to the window in
   front, and to no other, after the events already waiting for it. */
COLD static void paste_to(struct state *st, struct line *l) {
    int k = focused(st);
    if (k < 0) return;
    struct win *w = &st->win[k];
    if (!st->clip_len) {
        say3(l, "paste: nothing has been copied", "", "");
    } else if (w->paste_len || w->qlen == QUEUE) {
        say3(l, "paste: the last paste is still on its way to ", name_of(w->badge), "");
    } else {
        copy_bytes(w->paste, st->clip, st->clip_len);
        w->paste_len = st->clip_len;
        w->paste_at = 0;
        deliver_event(st, k, EV_PASTE, 0, 0);
        put_s(l, "display: paste: ");
        put_dec(l, (u64)st->clip_len);
        say3(l, " bytes to ", name_of(w->badge), "");
    }
}

/* COPY: the text the display asked for, 16 bytes at a time; fewer than 16 ends it. Taken
   only from the badge of the window that was asked, while the copy it asked for is open.
   The text is kept only when it ends: until then, the clipboard is what it was. */
COLD __attribute__((noinline)) static void on_copy(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], slot = r->x[6];
    int k = st->copy_win - 1;
    int late = k >= 0 && millis() - st->copy_at > COPY_MS;
    if (k < 0 || late || badge != st->copy_badge || !st->win[k].used || st->win[k].closing ||
        st->win[k].badge != badge) {
        if (late) st->copy_win = 0;
        if (slot) sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        if (st->copy_refused[badge & 31] < 3) {
            st->copy_refused[badge & 31]++;
            say3(l, name_of(badge), late && badge == st->copy_badge ? " answered a copy too late; refused"
                                                                     : " sent a copy nobody asked for; refused", "");
        }
        return;
    }
    int n = 0;
    for (; n < 16; n++) {
        unsigned char c = (unsigned char)(r->x[3 + n / 8] >> (8 * (n % 8)));
        if (!c) break;
        if (c == '\r') c = '\n';
        if (c == '\t') c = ' ';
        if ((c == '\n' || (c >= 32 && c < 127)) && st->copy_len < CLIP_MAX) st->copy_buf[st->copy_len++] = (char)c;
    }
    if (slot) sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
    if (n == 16 && st->copy_len < CLIP_MAX) return;     /* more to come */
    st->copy_win = 0;
    if (!st->copy_len) {
        say3(l, "copy: ", name_of(badge), " had nothing to copy");
    } else {
        copy_bytes(st->clip, st->copy_buf, st->copy_len);
        st->clip_len = st->copy_len;
        put_s(l, "display: copied ");
        put_dec(l, (u64)st->clip_len);
        say3(l, " bytes from ", name_of(badge), "");
    }
}

COLD static void on_input(struct state *st, struct line *l, u64 kind, u64 a, u64 b) {
    if (kind == EV_KEY && (a == KEY_COPY || a == KEY_PASTE)) {
        if (a == KEY_COPY) copy_ask(st, l);
        else paste_to(st, l);
        return;
    }
    if (kind == EV_KEY) {
        int k = focused(st);
        if (k < 0) return;
        deliver_event(st, k, EV_KEY, a, 0);
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
    if (kind == EV_DOWN && (st->menu || (st->py < BAR_H && (st->px < 100 || on_edit(st, st->px))))) {
        /* a click with a menu open closes it (choosing what is under it); on the logo or
           on Edit, with none open, opens that one */
        int was = st->menu, item = was ? menu_at(st, st->px, st->py) : -1;
        st->menu = was ? 0 : st->px < 100 ? 1 : 2;
        if (st->menu == 2) st->menu_x = edit_x(st) - 10;
        composite(st, 0, 0, W, MENU_Y + MENU_H + 12);
        if (st->menu == 2) say3(l, "the Edit menu, for ", name_of(st->win[focused(st)].badge), "");
        if (was == 2 && item >= 0) {
            if (item == 0) copy_ask(st, l);
            else paste_to(st, l);
        } else if (was == 1 && item >= 0) {
            int restart = item == 0;          /* the items: Restart, Shut down */
            put_s(l, restart ? "display: restarting, as the user asked"
                             : "display: switching off, as the user asked");
            say(l);
            if (!restart) {
                /* A Pi cannot cut its own power: the kernel halts. Say it is safe. */
                struct surface *sc = &st->screen;
                fill(sc, 0, 0, W, H, rgb(12, 14, 22));
                const char *msg = "leanos has shut down. You can switch off the Pi.";
                font_text(sc, &st->medium, W / 2 - text_w(&st->medium, msg) / 2, H / 2, msg,
                          rgb(210, 214, 228));
            }
            sys(SYS_POWER, POWER, restart ? POWER_RESTART : POWER_OFF, 0, 0, 0);
        }
        composite(st, ox, oy, 12, 19);
        composite(st, st->px, st->py, 12, 19);
        return;
    }
    if (kind == EV_DOWN) {
        int d = dock_at(st, st->px, st->py);
        if (d > 100) raise_program(st, d - 101);
        else if (d > DOCK_N) open_pinned(st, l, d - 1 - DOCK_N);
        else if (d) launch(st, l, d - 1);
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
                deliver_event(st, k, EV_DOWN, (u64)(st->px - w->x), (u64)(st->py - w->y - TITLE_H));
            if (st->py < w->y + TITLE_H) {
                st->drag = k + 1;
                st->grab_x = st->px - w->x;
                st->grab_y = st->py - w->y;
                st->drag_x0 = w->x;
                st->drag_y0 = w->y;
            }
        }
    } else if (kind == EV_MOVE && st->drag) {
        /* Moves that arrive faster than frames are drawn: only the last is drawn (the main
           loop calls drag_frame when no message is waiting). */
        struct win *w = &st->win[st->drag - 1];
        int ny = st->py - st->grab_y;
        if (!st->drag_pending) {
            st->drag_pending = 1;
            st->pend_x = w->x;
            st->pend_y = w->y;
        }
        w->x = st->px - st->grab_x;
        w->y = ny < BAR_H + 2 ? BAR_H + 2 : ny;
    } else if (kind == EV_MOVE) {
        int hv = dock_at(st, st->px, st->py);
        if (hv != st->hover) {
            st->hover = hv;
            composite(st, DOCK_AREA_X, DOCK_Y - 44, W, DOCK_H + 44);
        }
    } else if (kind == EV_UP && st->drag) {
        struct win *w = &st->win[st->drag - 1];
        if (w->x != st->drag_x0 || w->y != st->drag_y0) {
            put_s(l, "display: moved ");
            put_s(l, win_name(w));
            put_s(l, "'s window to (");
            put_dec(l, w->x);
            put_s(l, ", ");
            put_dec(l, w->y);
            put_s(l, ")");
            if (w->id) {
                put_s(l, ", its window ");
                put_dec(l, (u64)w->id);
            }
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

/* ---- where a new window goes ----

   Where it covers least of what can be seen of the windows already open: each window's
   title bar counts four times its area, so a new window leaves the others' title bars
   showing (to click and drag) wherever it can. It stays in the work area, below the menu
   bar and above the dock, with a margin, if it fits there.

   What shows of the open windows is painted into a coarse map, a cell per 8 x 8 pixels (the
   weight at the cell's center: 0 the desktop, 1 a window, 4 a title bar), and summed as a
   table of prefix sums, so what a place covers costs four lookups. The places tried: the
   work area's edges and corners, a 64-pixel grid, and beside or aligned with each window's
   edges. Of the places that cover least, one in a corner of the work area is taken first,
   then one on an edge, then the topmost, then the leftmost: the same windows always go to
   the same places, which the tests rely on. At first boot Notes takes the top left, Apps
   the top right, and the tour the bottom left.

   When every place would cover much (more than half again the window's own area), the
   screen is full: the window cascades from the top left, 32 pixels a step, to the first
   step no window's corner is at, so every title bar in the cascade shows. */
#define PLACE_X0 8
#define PLACE_Y0 (BAR_H + 8)
#define PLACE_X1 (W - 8)
#define PLACE_Y1 (DOCK_Y - 8)
#define PLACE_GAP 8
#define CELL 8
#define GX (W / CELL)
#define GY (H / CELL)
#define NCAND (2 + 16 + 4 * MAX_WIN)
/* the map's prefix sums live in the spare run, after the window table (at most 4 x 128 x
   75 = 38400 in any sum: they fit in 16 bits) */
_Static_assert(sizeof(struct win) * MAX_WIN + (GY + 1) * (GX + 1) * 2 <= 28 * 4096,
               "the window table and the placement map must fit in 28 pages");
_Static_assert(4 * GX * GY < 65536, "a sum of the map must fit in 16 bits");

COLD static int add_cand(int *c, int n, int v, int lo, int hi) {
    if (v < lo) v = lo;          /* (a window wider or taller than the room: at its start) */
    if (v > hi) v = hi > lo ? hi : lo;
    for (int i = 0; i < n; i++) if (c[i] == v) return n;
    c[n] = v;
    return n + 1;
}

COLD static void place(struct state *st, struct win *wn) {
    int ow = outer_w(wn), oh = outer_h(wn);
    int xhi = PLACE_X1 - ow, yhi = PLACE_Y1 - oh;
    unsigned short *sum = (unsigned short *)(st->win + MAX_WIN);   /* (GY + 1) x (GX + 1) */
    for (int i = 0; i < (GY + 1) * (GX + 1); i++) sum[i] = 0;
    /* what shows where: the windows bottom to top, each over the ones below */
    for (int i = 0; i < st->nz; i++) {
        const struct win *o = &st->win[st->z[i]];
        for (int j = 0; j < GY; j++) {
            int cy = j * CELL + CELL / 2;
            if (cy < o->y || cy >= o->y + outer_h(o)) continue;
            for (int c = 0; c < GX; c++) {
                int cx = c * CELL + CELL / 2;
                if (cx >= o->x && cx < o->x + outer_w(o)) sum[(j + 1) * (GX + 1) + c + 1] = cy < o->y + TITLE_H ? 4 : 1;
            }
        }
    }
    for (int j = 1; j <= GY; j++)
        for (int c = 1; c <= GX; c++)
            sum[j * (GX + 1) + c] += sum[(j - 1) * (GX + 1) + c] + sum[j * (GX + 1) + c - 1] -
                                     sum[(j - 1) * (GX + 1) + c - 1];
    int xs[NCAND], ys[NCAND], nx = 0, ny = 0;
    nx = add_cand(xs, nx, PLACE_X0, PLACE_X0, xhi);
    nx = add_cand(xs, nx, xhi, PLACE_X0, xhi);
    ny = add_cand(ys, ny, PLACE_Y0, PLACE_Y0, yhi);
    ny = add_cand(ys, ny, yhi, PLACE_Y0, yhi);
    for (int g = 64; g < W; g += 64) {
        if (PLACE_X0 + g < xhi) nx = add_cand(xs, nx, PLACE_X0 + g, PLACE_X0, xhi);
        if (PLACE_Y0 + g < yhi) ny = add_cand(ys, ny, PLACE_Y0 + g, PLACE_Y0, yhi);
    }
    for (int i = 0; i < st->nz; i++) {
        const struct win *o = &st->win[st->z[i]];
        int x0 = o->x, y0 = o->y, x1 = o->x + outer_w(o), y1 = o->y + outer_h(o);
        int at[8] = {x1 + PLACE_GAP, x0 - PLACE_GAP - ow, x0, x1 - ow, y1 + PLACE_GAP, y0 - PLACE_GAP - oh, y0, y1 - oh};
        for (int a = 0; a < 4; a++) {
            if (at[a] >= PLACE_X0 && at[a] <= xhi) nx = add_cand(xs, nx, at[a], PLACE_X0, xhi);
            if (at[4 + a] >= PLACE_Y0 && at[4 + a] <= yhi) ny = add_cand(ys, ny, at[4 + a], PLACE_Y0, yhi);
        }
    }
    long best = -1;
    int best_edge = 0, bx = PLACE_X0, by = PLACE_Y0;
    for (int b = 0; b < ny; b++)
        for (int a = 0; a < nx; a++) {
            int x = xs[a], y = ys[b];
            /* the cells whose centers the place covers */
            int c0 = (x + CELL / 2 - 1) / CELL, c1 = (x + ow + CELL / 2 - 1) / CELL;
            int j0 = (y + CELL / 2 - 1) / CELL, j1 = (y + oh + CELL / 2 - 1) / CELL;
            if (c1 > GX) c1 = GX;
            if (j1 > GY) j1 = GY;
            long cost = (long)sum[j1 * (GX + 1) + c1] - sum[j0 * (GX + 1) + c1] - sum[j1 * (GX + 1) + c0] +
                        sum[j0 * (GX + 1) + c0];
            int edge = (x != PLACE_X0 && x != xhi) + (y != PLACE_Y0 && y != yhi);
            if (best < 0 || cost < best || (cost == best && (edge < best_edge || (edge == best_edge &&
                (y < by || (y == by && x < bx)))))) {
                best = cost;
                best_edge = edge;
                bx = x;
                by = y;
            }
        }
    if (best * CELL * CELL > 3L * ow * oh / 2) {
        /* full: cascade */
        for (int n = 0; n < MAX_WIN; n++) {
            bx = PLACE_X0 + 32 * n;
            by = PLACE_Y0 + 32 * n;
            int taken = 0;
            for (int i = 0; i < st->nz; i++) {
                const struct win *o = &st->win[st->z[i]];
                int dx = o->x - bx, dy = o->y - by;
                if (dx > -16 && dx < 16 && dy > -16 && dy < 16) taken = 1;
            }
            if (!taken) break;
        }
    }
    wn->x = bx;
    wn->y = by;
    if (wn->x + ow > W - 8) wn->x = W - 8 - ow;
    if (wn->y + oh > PLACE_Y1) wn->y = PLACE_Y1 - oh;
    /* but never over the menu bar, as a drag keeps it: a window taller than the room between
       them reaches over the dock instead, which is drawn over every window */
    if (wn->y < PLACE_Y0) wn->y = PLACE_Y0;
}

/* "display: Terminal opened a 460x272 window at 556,38 from a read-only capability to 123
   pages": what opened, and where, which the tests read to click inside it. */
COLD static void say_open(struct line *l, struct win *w) {
    w->unsaid = 0;
    put_s(l, "display: ");
    put_s(l, win_name(w));
    put_s(l, " opened a ");
    put_dec(l, (u64)w->content.w);
    put_s(l, "x");
    put_dec(l, (u64)w->content.h);
    put_s(l, " window at ");
    put_dec(l, (u64)w->x);
    put_s(l, ",");
    put_dec(l, (u64)w->y);
    put_s(l, " from a read-only capability to ");
    put_dec(l, (u64)w->pages);
    put_s(l, " pages");
    if (w->id) {
        put_s(l, ", its window ");
        put_dec(l, (u64)w->id);
    }
    say(l);
}

/* A request from `badge` other than ICON: any of its windows whose opening is not logged
   yet will get no name, so log it now. */
COLD static void say_unsaid(struct state *st, struct line *l, u64 badge) {
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (w->used && w->unsaid && w->badge == badge) say_open(l, w);
    }
}

COLD static void on_open(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], size = r->x[3], title = r->x[4], cap = r->x[5], slot = r->x[6];
    u64 w = size >> 16, h = size & 0xffff;
    int k = -1;
    for (int i = 0; i < MAX_WIN; i++) if (!st->win[i].used) { k = i; break; }
    struct res info = sys1(SYS_CAPINFO, cap - 1);
    u64 need = (w * h * 4 + 4095) / 4096;
    /* The map takes the whole granted run, so a run longer than a window's slot would reach
       into the next window's slot and show this program's pixels there: refused. */
    if (k < 0 || slot_of(badge) < 0 || w == 0 || h == 0 || w > 900 || h > 480 || info.x[2] != 0 ||
        info.x[3] < need || info.x[3] > WIN_MAX_PAGES ||
        sys2(SYS_MAP, cap - 1, WIN_PAGE + WIN_MAX_PAGES * (u64)k).status != OK) {
        /* Every line holds the kernel while the serial port takes it: a program asking again
           and again must not keep the display (and every core) busy logging. */
        if (st->said[badge & 31] < 3) {
            st->said[badge & 31]++;
            say3(l, name_of(badge), " sent a window that does not fit its pixels; refused", "");
        }
        sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        return;
    }
    struct win *wn = &st->win[k];
    /* its number: the lowest its program is not using (0 for its first) */
    int id = 0, others = 0;
    for (int again = 1; again;) {
        again = 0;
        for (int j = 0; j < MAX_WIN; j++) {
            if (!st->win[j].used || st->win[j].badge != badge) continue;
            others = 1;
            if (st->win[j].id == id) { id++; again = 1; }
        }
    }
    if (!others) st->parked[slot_of(badge)] = 0;   /* its first window: it starts afresh */
    wn->used = 1;
    wn->badge = badge;
    wn->id = id;
    wn->content = surface_of((unsigned *)PAGE(WIN_PAGE + WIN_MAX_PAGES * (u64)k), (int)w, (int)h);
    for (int i = 0; i < 8; i++) wn->title[i] = (char)(title >> (8 * i));
    wn->title[8] = 0;
    place(st, wn);
    wn->hash = sys1(SYS_BOOTINFO, (u64)slot_of(badge)).x[2];
    wn->closing = 0;
    wn->icon.px = 0;
    wn->prog[0] = 0;
    st->cap_win[cap - 1] = k + 1;
    wn->qhead = wn->qlen = 0;
    wn->paste_len = wn->paste_at = 0;
    if (st->copy_win == k + 1) st->copy_win = 0;
    st->z[st->nz++] = k;
    u64 t0 = micros();
    redraw_all(st);
    if (!st->full_reported) {
        st->full_reported = 1;
        put_s(l, "display: a full redraw took ");
        put_ms(l, micros() - t0);
        say(l);
    }
    wn->pages = (int)info.x[3];
    /* A program from the card lends its name (ICON) just after: its opening is logged then,
       with the name (on_icon), or at its next request if it lends none (say_unsaid). */
    wn->unsaid = badge >= 10 && badge <= 15;
    if (!wn->unsaid) say_open(l, wn);
    sys(SYS_REPLY, slot - 1, 0, (u64)id, 0, 0);
}

/* How many waiting programs' calls it holds: each takes one of its 8 reply slots. */
COLD static int held(struct state *st) {
    int n = 0;
    for (int p = 0; p < NSLOT; p++) n += st->hold[p] != 0;
    return n;
}

/* Answer the program that has waited longest with no event, which frees its reply slot. It
   asks again a moment later (app_wait); until then its events wait in its windows' queues. */
COLD static void park_oldest(struct state *st, struct line *l) {
    int o = -1;
    for (int p = 0; p < NSLOT; p++)
        if (st->hold[p] && (o < 0 || st->held_at[p] < st->held_at[o])) o = p;
    if (o < 0) return;
    if (!st->parked_said) {
        st->parked_said = 1;
        say3(l, "more windows wait than the 7 calls it holds: ", name_of(badge_in(o)),
             ", waiting longest, hears no event and asks again");
    }
    sys(SYS_REPLY, st->hold[o] - 1, 0, 0, 0, 0);
    st->hold[o] = 0;
    st->parked[o] = 1;
}

/* WAIT (and POLL, which answers at once, with no event if there is none, for a client
   that keeps time itself and must not block), for any of the caller's windows: a program
   holds one call, however many windows it has. A parked program, asking again while
   HOLD_MAX waits are held, is answered at once too; any other wait is held, in place of the
   one held longest if HOLD_MAX already are. */
COLD static void on_wait(struct state *st, struct line *l, struct res *r, int poll) {
    u64 badge = r->x[1], dirty = r->x[3], slot = r->x[6];
    int any = 0;
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (!w->used || w->badge != badge) continue;
        any = 1;
        if (((dirty >> w->id) & 1) && !w->closing) composite_window(st, k);
    }
    if (!any) {
        sys(SYS_REPLY, slot - 1, 0, 0, 0, 0); /* no window: nothing to wait for */
        return;
    }
    /* Events that came before a close button still go first: keys typed just before a
       click on close are the program's to handle (Notes saves them). */
    int p = slot_of(badge);
    u64 e[3];
    if (next_event(st, badge, e)) {
        st->parked[p] = 0;
        sys(SYS_REPLY, slot - 1, e[0], e[1], e[2], 0);
    } else if (poll || (st->parked[p] && held(st) >= HOLD_MAX)) {
        sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
    } else {
        if (held(st) >= HOLD_MAX) park_oldest(st, l);
        st->hold[p] = slot;
        st->parked[p] = 0;
        st->held_at[p] = ++st->waits;
    }
}

/* CLOSE: the caller closes one of its own windows (w1: its number), which goes at once:
   off the screen, its capabilities let go, its place in the table free. The badge, which
   the kernel sets, and the number together name the window, so a program can close only its
   own. 0 if it did, 1 if the caller has no window of that number (one it closed already,
   or whose EV_CLOSE it has heard). A window whose close button was clicked goes the same
   way, its EV_CLOSE unsaid: the program closed it itself. */
COLD static void on_close(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], id = r->x[3], slot = r->x[6];
    int k = -1;
    for (int j = 0; j < MAX_WIN; j++)
        if (st->win[j].used && st->win[j].badge == badge && (u64)st->win[j].id == id) k = j;
    if (k < 0) {
        if (st->said[badge & 31] < 3) {
            st->said[badge & 31]++;
            say3(l, name_of(badge), " asked to close a window it does not have; refused", "");
        }
        sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        return;
    }
    forget(st, k);
    redraw_all(st);
    sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
    int n = 0;
    for (int j = 0; j < MAX_WIN; j++) n += st->win[j].used;
    put_s(l, "display: ");
    put_s(l, name_of(badge));
    put_s(l, " closed its window ");
    put_dec(l, id);
    put_s(l, "; windows in the table: ");
    put_dec(l, (u64)n);
    say(l);
}

/* ICON: a program from the card lends the icon and name its loader gave it: 4 pages of its
   code run (a marker, the size, the icon asset, and at the end the name of the file it was
   run from). The icon is shown in its title bar and in the dock; the name is what RAISE,
   `run` and the dock's pinned programs look for, so it must be the loader's. A program can
   write any of its runs but its code run, which alone may execute (every run it holds is
   its own, with no more rights than the manifest gave: `confined`, `frame_flow`, and
   `derive_never_amplifies`), and the loader puts the marker at the start of no page of it
   but its icon's (image_marked in elf.h). So the grant must carry the execute right, be
   exactly four pages and start with the marker. It is mapped read-only: a copy without the
   execute right takes the grant's place, so nothing a program lends ever runs here. */
COLD static void on_icon(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], cap = r->x[5], slot = r->x[6];
    u64 ok = 1;
    for (int k = 0; k < MAX_WIN && cap && badge >= 10 && badge <= 15; k++) {
        struct win *w = &st->win[k];
        if (!w->used || w->closing || w->badge != badge || w->icon.px || w->prog[0]) continue;
        struct res info = sys1(SYS_CAPINFO, cap - 1);
        /* exactly its four pages (a longer run would be mapped over the next window's icon),
           of a code run; then the read-only copy, at the grant's place (the grant is last) */
        if (info.status != OK || !(info.x[1] & X) || info.x[2] != 0 || info.x[3] != 4) break;
        struct res ro = sys(SYS_DERIVE, cap - 1, R, 0, 0, 0);
        if (ro.status != OK) break;
        sys1(SYS_DROP, ro.x[1] == cap ? cap - 1 : ro.x[1]);
        if (ro.x[1] != cap) break;
        if (sys2(SYS_MAP, cap - 1, ICON_PAGE + 4 * (u64)k).status != OK) break;
        const unsigned *m = (const unsigned *)PAGE(ICON_PAGE + 4 * (u64)k);
        unsigned wd = m[2], ht = m[3];
        if (m[0] != 0x43494e4cu) break;
        /* the name the loader wrote at the end: printable, or none */
        const unsigned char *name = (const unsigned char *)m + 4 * 4096 - 16;
        int n = 0;
        while (n < 15 && name[n] > 32 && name[n] < 127) n++;
        for (int i = 0; i < 16; i++) w->prog[i] = i < n && !name[n] ? (char)name[i] : 0;
        if (w->unsaid) say_open(l, w);
        if (m[1] && wd > 0 && ht > 0 && wd <= 64 && ht <= 64 && 16 + wd * ht * 4 <= 4 * 4096 - 16) {
            w->icon.w = (int)wd;
            w->icon.h = (int)ht;
            w->icon.px = m + 4;
        }
        if (w->icon.px || w->prog[0]) {
            st->cap_win[cap - 1] = k + 1;          /* dropped with the window */
            ok = 0;
            composite_window(st, k);
            composite(st, DOCK_AREA_X, DOCK_Y - 44, W, DOCK_H + 44);
        }
        break;
    }
    sys(SYS_REPLY, slot - 1, ok, 0, 0, 0);
}

/* START: Apps asks for one of the built-in apps (w1 = its place in the dock), as if its
   dock icon were clicked. Only Apps may ask. */
/* RAISE: bring forward the windows of the program from card file w1 w2 (up to 15 bytes),
   if one is open. Answers 0 if it did, 1 if there is none (always, for no name: a launcher
   about to start a slot asks that, app_before_start). Anyone may ask: it only moves a
   window up. The name is the one its icon brought (ICON): the name of the file the loader
   ran, from the program's code run (on_icon). */
COLD static void on_raise(struct state *st, struct line *l, struct res *r) {
    char want[17];
    for (int i = 0; i < 16; i++) want[i] = (char)(r->x[3 + i / 8] >> (8 * (i % 8)));
    want[15] = want[16] = 0;
    u64 found = 1;
    for (int k = 0; k < MAX_WIN && want[0]; k++) {
        struct win *w = &st->win[k];
        if (!w->used || w->closing || !w->prog[0]) continue;
        int i = 0;
        while (i < 16 && w->prog[i] == want[i] && want[i]) i++;
        if (i < 16 && w->prog[i] == want[i]) {
            raise_program(st, k);
            if (st->said[r->x[1] & 31] < 3) {    /* a program may name its own window and ask again */
                st->said[r->x[1] & 31]++;
                say3(l, want, " is already open; brought it to the front", "");
            }
            found = 0;
            break;
        }
    }
    sys(SYS_REPLY, r->x[6] - 1, found, 0, 0, 0);
}

COLD static void on_start(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], which = r->x[3], slot = r->x[6];
    if (badge != 16 || which >= DOCK_N) {
        sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        return;
    }
    sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
    launch(st, l, (int)which);
}

/* Ask Apps to save the time zone on the card: as an event if its window is open, else by
   starting it with "@zone" waiting (OP_PENDING). If Apps is busy starting, or another request
   is waiting for it, this is tried again once it is done. */
COLD static void save_zone(struct state *st, struct line *l) {
    for (int k = 0; k < MAX_WIN; k++) {
        struct win *w = &st->win[k];
        if (w->used && !w->closing && slot_of(w->badge) == 16) {
            deliver_event(st, k, EV_LAUNCH, 0x6e6f7a40 /* "@zon" */, 'e');
            st->zone_unsaved = 0;
            return;
        }
    }
    if (run_state(16) == 1 || (st->pending[0] && !same_name(st->pending, "@zone"))) return;
    const char *z = "@zone";
    for (int i = 0; i < 6; i++) st->pending[i] = z[i];
    launch(st, l, APPS_DOCK);   /* Apps takes it from pending (on_pending) */
}

/* ZONE: the time zone, for anyone who asks. */
COLD static void on_zone(struct state *st, struct res *r) {
    sys(SYS_REPLY, r->x[6] - 1, 0, (u64)(st->zone + ZONE_BIAS), 0, 0);
}

/* SET: only Settings may change the desktop. Apps, started at boot, may give the time zone
   it read from the card, once, unless Settings has chosen one since. */
COLD static void on_set(struct state *st, struct line *l, struct res *r) {
    u64 badge = r->x[1], what = r->x[3], value = r->x[4], slot = r->x[6];
    if (what == SET_ZONE && value <= (u64)(ZONE_MAX + ZONE_BIAS) && zone_ok((long)value - ZONE_BIAS) &&
        (badge == BADGE_SETTINGS || (badge == 16 && st->zone_restore))) {
        st->zone = (long)value - ZONE_BIAS;
        if (badge == BADGE_SETTINGS) st->zone_unsaved = 1;
        st->zone_restore = 0;
        sys(SYS_REPLY, slot - 1, 0, 0, 0, 0);
        if (badge == BADGE_SETTINGS) say_zone(st, l, ", as Settings asked");
        else if (st->zone) say_zone(st, l, ", saved on the card");
        return;
    }
    if (badge != BADGE_SETTINGS || what != SET_BACKGROUND || value >= NTHEME) {
        if (st->ignored[badge & 31] < 3) {
            st->ignored[badge & 31]++;
            put_s(l, "display: ");
            put_s(l, name_of(badge));
            put_s(l, " may not change the desktop; refused");
            say(l);
        }
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

COLD __attribute__((section(".text.start"))) void _start(void) {
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
    /* The window table is too big for the data pages: it lives in the spare run's tail,
       past the assets, which is this server's own memory. */
    struct res rw = sys(SYS_DERIVE, 3, R | 2 /* write: W is the screen's width here */, 200, 28, 0);
    sys2(SYS_MAP, rw.x[1], WIN_TABLE_PAGE);
    st->win = (struct win *)PAGE(WIN_TABLE_PAGE);
    _Static_assert(sizeof(struct win) * MAX_WIN <= 28 * 4096, "the window table must fit in 28 pages");
    st->ncaps = st->own_caps = (int)rw.x[1] + 1;
    st->grant_at = -1;
    for (int i = 0; i < st->ncaps; i++) { st->cap_badge[i] = 0; st->cap_win[i] = 0; }
    const unsigned char *assets = (const unsigned char *)PAGE(ASSET_PAGE);
    st->ui = font_of(assets, F_UI);
    st->ui_bold = font_of(assets, F_UI_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->huge = font_of(assets, F_HUGE);
    st->medium = font_of(assets, F_MEDIUM);
    for (int i = 0; i < DOCK_ALL; i++) st->icons[i] = picture_of(assets, ASSET_ICON, 10 + i);
    st->pending[0] = 0;

    st->screen = surface_of((unsigned *)PAGE(FB_PAGE), W, H);
    st->theme = 0;
    st->full_reported = st->click_reported = 0;
    st->menu = 0;
    st->clip_len = st->copy_win = st->copy_len = 0;
    for (int i = 0; i < 32; i++) st->copy_refused[i] = 0;
    st->drag_frames = st->drag_us = 0;
    st->bar_time[0] = 0;
    st->bar_minute = 0;
    st->zone = 0;
    st->zone_unsaved = st->zone_restore = 0;
    st->waits = 0;
    st->events = 0;
    for (int p = 0; p < NSLOT; p++) st->hold[p] = st->parked[p] = 0;
    st->parked_said = 0;
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
    /* Startup items: Apps opens what the card's startup.txt lists (nothing, if it has none). */
    const char *at = "@startup";
    for (int i = 0; i < 9; i++) st->pending[i] = at[i];
    launch(st, &l, APPS_DOCK);

    u64 bar_wait = bar_clock(st), bar_at = millis();
    for (;;) {
        struct res r;
        if (millis() - bar_at >= bar_wait) {
            bar_wait = bar_clock(st);
            bar_at = millis();
        }
        if (st->zone_unsaved) save_zone(st, &l);
        if (st->drag_pending) {
            r = sys(SYS_RECVT, ENDPOINT, 0, 0, 0, 0);   /* anything else waiting? */
            if (r.status != OK) {
                drag_frame(st);
                continue;
            }
        } else {
            /* wait for a message, or until the menu bar's clock turns over (or, while the
               time zone waits for Apps to save it, a moment) */
            u64 left = bar_wait - (millis() - bar_at);
            if (st->zone_unsaved && left > 100) left = 100;
            r = sys(SYS_RECVT, ENDPOINT, left ? left : 1, 0, 0, 0);
            if (r.status == FULL) park_oldest(st, &l);    /* a caller waits for a reply slot */
            if (r.status != OK) continue;
        }
        u64 badge = r.x[1], op = r.x[2], slot = r.x[6], grant = r.x[5];
        /* First, what the kernel may have taken back since the last message (see "runs the
           kernel replaced"): a reply slot this call now has, capabilities fewer than it
           counts (a granted one lands at the end of the list, so its place says how many
           there were before it), and the windows of programs that stopped. The grant
           moves down with every capability let go before it. */
        if (slot) claim_slot(st, &l, slot);
        int real = grant ? (int)grant - 1 : caps_now(st);
        if (real < st->ncaps) {
            int dropped = lost_runs(st, &l, real);
            if (grant) grant -= (u64)dropped;
        }
        st->grant_at = (int)grant - 1;
        if (grant) {
            st->ncaps = (int)grant;
            st->cap_badge[grant - 1] = badge;
            st->cap_win[grant - 1] = 0;
        }
        forget_stopped(st, &l);
        grant = r.x[5] = (u64)(st->grant_at + 1);
        /* Anything but another drag move draws the one waiting first. */
        if (st->drag_pending && !((badge == BADGE_INPUT || badge == BADGE_USB) && !slot && op == EV_MOVE))
            drag_frame(st);
        if (slot && !(op == OP_ICON && grant)) say_unsaid(st, &l, badge);
        if ((badge == BADGE_INPUT || badge == BADGE_USB) && !slot) {
            on_input(st, &l, op, r.x[3], r.x[4]);
        } else if (slot && op == OP_OPEN && r.x[5]) {
            on_open(st, &l, &r);
        } else if (slot && (op == OP_WAIT || op == OP_POLL)) {
            on_wait(st, &l, &r, op == OP_POLL);
        } else if (slot && op == OP_SET) {
            on_set(st, &l, &r);
        } else if (slot && op == OP_ICON && grant) {
            on_icon(st, &l, &r);
        } else if (slot && op == OP_START) {
            on_start(st, &l, &r);
        } else if (slot && op == OP_RAISE) {
            on_raise(st, &l, &r);
        } else if (slot && op == OP_PENDING) {
            on_pending(st, &r);
        } else if (slot && op == OP_ZONE) {
            on_zone(st, &r);
        } else if (slot && op == OP_CLOSE) {
            on_close(st, &l, &r);
        } else if (op == OP_COPY && !grant) {
            on_copy(st, &l, &r);
        } else {
            /* A request the display does not understand, from anyone: it answers no, and
               says so the first few times, so a program that floods it cannot flood the log. */
            unsigned char *n = &st->ignored[badge & 31];
            if (*n < 3) {
                put_s(&l, "display: ");
                put_s(&l, name_of(badge));
                put_s(&l, *n == 2 ? " keeps sending requests it cannot make; ignoring them quietly"
                                  : " sent a request it cannot make; ignored");
                say(&l);
                (*n)++;
            }
            if (slot) sys(SYS_REPLY, slot - 1, 1, 0, 0, 0);
        }
        /* A grant that did not become a window is not kept. */
        if (st->grant_at >= 0 && st->cap_win[st->grant_at] == 0) cap_drop(st, st->grant_at);
        st->grant_at = -1;
    }
}
