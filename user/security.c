/* Security. What the boot checks found for every program, straight from the kernel, and
   what is proved about the kernel. Clicking the window checks again. */
#include "app.h"

#define XW 460
#define XH 322
enum { F_UI = 1, F_BOLD = 2, F_SMALL = 3 };

static const char *const proved[] = {
    "Only code that matches the boot manifest runs",
    "No page is ever both writable and executable",
    "An app reaches only its own memory",
    "Only the input driver can touch the keyboard",
    "Starting an app takes back all of its memory",
};
#define NPROVED (sizeof proved / sizeof proved[0])

struct security {
    struct font ui, bold, small;
    struct surface win;
};

static void mark(struct surface *s, int x, int y, int kind) {
    /* kind: 1 verified (green check), 2 refused (red cross), 0 not loaded (gray dot) */
    if (kind == 1) {
        round_rect(s, x, y, 16, 16, 8, rgb(52, 199, 89), 255);
        thick_line(s, x + 4, y + 8, x + 7, y + 11, 2, rgb(255, 255, 255));
        thick_line(s, x + 7, y + 11, x + 12, y + 5, 2, rgb(255, 255, 255));
    } else if (kind == 2) {
        round_rect(s, x, y, 16, 16, 8, rgb(255, 69, 58), 255);
        thick_line(s, x + 5, y + 5, x + 11, y + 11, 2, rgb(255, 255, 255));
        thick_line(s, x + 11, y + 5, x + 5, y + 11, 2, rgb(255, 255, 255));
    } else {
        round_rect(s, x + 4, y + 4, 8, 8, 4, rgb(190, 190, 198), 255);
    }
}

static void hex8(char *out, u64 v) {
    for (int i = 0; i < 8; i++) out[i] = "0123456789abcdef"[(v >> (28 - 4 * i)) & 15];
    out[8] = 0;
}

/* Draw the report; returns how many programs are verified, refused and not loaded. */
static void draw(struct security *st, int n[3]) {
    struct surface *s = &st->win;
    n[0] = n[1] = n[2] = 0;
    fill(s, 0, 0, XW, XH, rgb(246, 246, 248));
    font_text(s, &st->bold, 20, 30, "Verified boot", rgb(30, 30, 36));
    for (u64 k = 0; k < 8; k++) {
        struct res r = sys1(SYS_BOOTINFO, k);
        int kind = r.status == OK ? (int)r.x[1] : 0;
        int y = 44 + (int)k * 20;
        mark(s, 20, y, kind);
        font_text(s, &st->ui, 44, y + 13, slot_name(k), rgb(40, 40, 48));
        char h[9];
        hex8(h, r.x[2]);
        const char *what = kind == 1 ? h : kind == 2 ? "does not match" : "not loaded";
        font_text(s, &st->small, 200, y + 12, what, kind == 2 ? rgb(215, 50, 40) : rgb(120, 120, 130));
        const char *run = r.x[4] == 1 ? "running" : r.x[4] == 2 ? "stopped" : "";
        font_text(s, &st->small, XW - 20 - font_width(&st->small, run), y + 12, run, rgb(120, 120, 130));
        n[kind == 1 ? 0 : kind == 2 ? 1 : 2]++;
    }
    fill(s, 20, 210, XW - 40, 1, rgb(224, 224, 230));
    font_text(s, &st->bold, 20, 234, "Proved in Lean", rgb(30, 30, 36));
    for (u64 i = 0; i < NPROVED; i++) {
        int y = 254 + (int)i * 16;
        font_text(s, &st->small, 22, y, "\xe2\x80\xa2", rgb(58, 110, 230));
        font_text(s, &st->small, 34, y, proved[i], rgb(60, 60, 70));
    }
}

static void report(struct line *l, int n[3]) {
    put_s(l, "security: ");
    put_dec(l, (u64)n[0]);
    put_s(l, " verified, ");
    put_dec(l, (u64)n[1]);
    put_s(l, " refused, ");
    put_dec(l, (u64)n[2]);
    put_s(l, " not loaded\n");
    flush(l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct security *st = (struct security *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->bold = font_of(assets, F_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->win = app_surface(XW, XH);
    int n[3];
    draw(st, n);
    u64 opened = app_open(XW, XH, "Security");
    put_s(&l, "security: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    report(&l, n);

    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "security: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind != EV_DOWN) continue;
        draw(st, n);
        report(&l, n);
        dirty = 1;
    }
}
