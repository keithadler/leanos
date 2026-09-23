/* clock: a program from the SD card that keeps time. It sleeps a second at a time (the
   kernel's sleep call) and redraws how long the Pi has been up, asking the display server
   for events without blocking so the close button still works. */
#include "../ui.h"

#define CW 260
#define CH 120

struct clock {
    struct ui ui;
    struct surface win;
    u64 shown;               /* the second on screen */
};

static void two(struct line *l, u64 v) {
    if (v < 10) put_s(l, "0");
    put_dec(l, v);
}

static void draw(struct clock *c, u64 secs) {
    struct surface *s = &c->win;
    fill(s, 0, 0, CW, CH, rgb(20, 22, 32));
    struct line l = {.n = 0};
    two(&l, secs / 3600);
    put_s(&l, ":");
    two(&l, secs / 60 % 60);
    put_s(&l, ":");
    two(&l, secs % 60);
    l.b[l.n] = 0;
    int w = font_width(&c->ui.huge, l.b);
    font_text(s, &c->ui.huge, CW / 2 - w / 2, 70, l.b, rgb(126, 214, 255));
    const char *up = "up since the Pi started";
    font_text(s, &c->ui.small, CW / 2 - font_width(&c->ui.small, up) / 2, 100, up, rgb(130, 136, 160));
}

__attribute__((section(".text.start"))) void _start(void) {
    struct clock *c = (struct clock *)DATA;
    struct line l = {.n = 0};
    ui_load(&c->ui, app_assets());
    c->win = app_surface(CW, CH);
    c->shown = millis() / 1000;
    draw(c, c->shown);
    u64 opened = app_open(CW, CH, "Clock");
    put_s(&l, "clock: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0, ticks = 0;
    for (;;) {
        struct event e = app_poll(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "clock: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        u64 now = millis() / 1000;
        if (now != c->shown) {
            c->shown = now;
            draw(c, now);
            dirty = 1;
            if (++ticks == 3) {           /* for the log: it keeps time on its own */
                put_s(&l, "clock: ticked 3 times\n");
                flush(&l);
            }
        }
        sleep_ms(1000 - millis() % 1000);  /* until the next second */
    }
}
