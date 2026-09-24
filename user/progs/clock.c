/* clock: the Lean kernel's clock, shown. It keeps no time of its own: every second it asks
   the kernel (`time`, system call 22), which counts timer ticks in Lean and hands back the
   hours, minutes and seconds. LeanOS/Proofs.lean proves what that means: the count moves
   only on a timer tick, by exactly one, and never back (`clock_monotone`); the hours,
   minutes and seconds add up to exactly the uptime (`time_reads_clock`); and the sleep it
   waits in never ends early (`sleep_on_time`). It asks the display server for events
   without blocking, so the close button still works. */
#include "../ui.h"
#include "../date.h"

#define CW 300
#define CH 150

struct clock {
    struct ui ui;
    struct surface win;
    u64 shown;               /* the second on screen */
    u64 ticks;               /* the kernel's tick count behind it */
};

/* The kernel's clock: ticks since boot, milliseconds, and hours, minutes, seconds. */
struct time { u64 ticks, ms, h, m, s, wall; };
static struct time kernel_time(void) {
    struct res r = sys0(SYS_TIME);
    return (struct time){r.x[1], r.x[2], r.x[3], r.x[4], r.x[5], r.x[6]};
}

static void two(struct line *l, u64 v) {
    if (v < 10) put_s(l, "0");
    put_dec(l, v);
}

static void draw(struct clock *c, struct time t) {
    struct surface *s = &c->win;
    fill(s, 0, 0, CW, CH, rgb(20, 22, 32));
    /* The time of day, if the network has said what it is; else the time since boot. */
    struct date d = date_of(t.wall);
    struct line l = {.n = 0};
    two(&l, t.wall ? (u64)d.h : t.h);
    put_s(&l, ":");
    two(&l, t.wall ? (u64)d.m : t.m);
    put_s(&l, ":");
    two(&l, t.wall ? (u64)d.s : t.s);
    l.b[l.n] = 0;
    int w = font_width(&c->ui.huge, l.b);
    font_text(s, &c->ui.huge, CW / 2 - w / 2, 70, l.b, rgb(126, 214, 255));
    struct line u = {.n = 0};
    if (t.wall) {
        put_s(&u, day_names[d.weekday]);
        put_s(&u, ", ");
        put_s(&u, month_names[d.month - 1]);
        put_s(&u, " ");
        put_dec(&u, (u64)d.day);
        put_s(&u, ", ");
        put_dec(&u, (u64)d.year);
        put_s(&u, " (UTC)");
    } else put_s(&u, "up since the Pi started");
    u.b[u.n] = 0;
    font_text(s, &c->ui.small, CW / 2 - font_width(&c->ui.small, u.b) / 2, 96, u.b, rgb(130, 136, 160));
    struct line k = {.n = 0};
    if (t.wall) {
        put_s(&k, "up ");
        two(&k, t.h);
        put_s(&k, ":");
        two(&k, t.m);
        put_s(&k, ":");
        two(&k, t.s);
        put_s(&k, ", kept by the Lean kernel");
    } else {
        put_s(&k, "kept by the Lean kernel: tick ");
        put_dec(&k, t.ticks);
    }
    k.b[k.n] = 0;
    font_text(s, &c->ui.small, CW / 2 - font_width(&c->ui.small, k.b) / 2, 120, k.b, rgb(96, 104, 130));
    const char *proved = "proved never to go back";
    font_text(s, &c->ui.small, CW / 2 - font_width(&c->ui.small, proved) / 2, 138, proved, rgb(96, 104, 130));
}

__attribute__((section(".text.start"))) void _start(void) {
    struct clock *c = (struct clock *)DATA;
    struct line l = {.n = 0};
    ui_load(&c->ui, app_assets());
    c->win = app_surface(CW, CH);
    struct time t = kernel_time();
    c->shown = t.ms / 1000;
    c->ticks = t.ticks;
    draw(c, t);
    u64 opened = app_open(CW, CH, "Clock");
    put_s(&l, "clock: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0, ticked = 0;
    for (;;) {
        struct event e = app_poll(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "clock: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        t = kernel_time();
        if (t.ticks < c->ticks) {        /* the proofs say this cannot happen; say so if it does */
            put_s(&l, "clock: the kernel's clock went back\n");
            flush(&l);
        }
        c->ticks = t.ticks;
        if (t.ms / 1000 != c->shown) {
            c->shown = t.ms / 1000;
            draw(c, t);
            dirty = 1;
            if (++ticked == 3) {         /* for the log: it keeps up with the kernel */
                put_s(&l, "clock: ticked 3 times, at tick ");
                put_dec(&l, t.ticks);
                put_s(&l, " (");
                two(&l, t.h);
                put_s(&l, ":");
                two(&l, t.m);
                put_s(&l, ":");
                two(&l, t.s);
                put_s(&l, ")\n");
                flush(&l);
            }
        }
        sleep_ms(1000 - t.ms % 1000);    /* until the next second */
    }
}
