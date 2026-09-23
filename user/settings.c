/* Settings. Picks the desktop's background. The display server takes this request only
   from the badge the manifest gives Settings, so no other app can change the desktop. */
#include "app.h"

#define SW 380
#define SH 250
enum { F_UI = 1, F_BOLD = 2, F_SMALL = 3 };

#define NBG 3
static const char *const bg_names[NBG] = {"Indigo", "Graphite", "Dawn"};
static const unsigned bg_top[NBG] = {0x1e204e, 0x24262c, 0x3a2a5a};
static const unsigned bg_bottom[NBG] = {0x0e4656, 0x0c0d10, 0xd98a5c};

#define SWATCH_W 96
#define SWATCH_H 64
#define SWATCH_Y 58
static int swatch_x(int i) { return 24 + i * (SWATCH_W + 18); }

struct settings {
    struct font ui, bold, small;
    struct surface win;
    int chosen;
};

static void draw(struct settings *st) {
    struct surface *s = &st->win;
    fill(s, 0, 0, SW, SH, rgb(246, 246, 248));
    font_text(s, &st->bold, 24, 36, "Background", rgb(30, 30, 36));
    for (int i = 0; i < NBG; i++) {
        int x = swatch_x(i);
        if (i == st->chosen) round_rect(s, x - 4, SWATCH_Y - 4, SWATCH_W + 8, SWATCH_H + 8, 14, rgb(58, 110, 230), 255);
        round_rect(s, x - 1, SWATCH_Y - 1, SWATCH_W + 2, SWATCH_H + 2, 11, rgb(246, 246, 248), 255);
        round_gradient(s, x, SWATCH_Y, SWATCH_W, SWATCH_H, 10, bg_top[i], bg_bottom[i]);
        int lw = font_width(&st->ui, bg_names[i]);
        font_text(s, &st->ui, x + SWATCH_W / 2 - lw / 2, SWATCH_Y + SWATCH_H + 24, bg_names[i],
                  i == st->chosen ? rgb(30, 30, 36) : rgb(110, 110, 120));
    }
    fill(s, 24, 176, SW - 48, 1, rgb(224, 224, 230));
    font_text(s, &st->bold, 24, 204, "About", rgb(30, 30, 36));
    font_text(s, &st->small, 24, 226, "leanos \xc2\xa9 2026 Keith Adler \xe2\x80\xa2 MIT license", rgb(120, 120, 130));
}

__attribute__((section(".text.start"))) void _start(void) {
    struct settings *st = (struct settings *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->bold = font_of(assets, F_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->win = app_surface(SW, SH);
    st->chosen = 0;
    draw(st);
    u64 opened = app_open(SW, SH, "Settings");
    put_s(&l, "settings: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "settings: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind != EV_DOWN) continue;
        int x = (int)e.a, y = (int)e.b;
        for (int i = 0; i < NBG; i++) {
            if (x < swatch_x(i) || x >= swatch_x(i) + SWATCH_W || y < SWATCH_Y || y >= SWATCH_Y + SWATCH_H) continue;
            struct res r = sys(SYS_CALL, ENDPOINT, OP_SET, SET_BACKGROUND, (u64)i, 0);
            u64 ok = r.status == OK && r.x[1] == 0 ? OK : BAD_ARG;
            put_s(&l, "settings: background set to ");
            put_s(&l, bg_names[i]);
            put_s(&l, outcome(ok));
            put_s(&l, "\n");
            flush(&l);
            if (ok == OK) {
                st->chosen = i;
                draw(st);
                dirty = 1;
            }
        }
    }
}
