/* clock: the Lean kernel's clock, shown, with a stopwatch and a countdown timer beside it. It
   keeps no time of its own: it asks the kernel (`time`, system call 22), which counts timer
   ticks in Lean and hands back the hours, minutes and seconds. LeanOS/Proofs.lean proves what
   that means: the count moves only on a timer tick, by exactly one, and never back
   (`clock_monotone`); the hours, minutes and seconds add up to exactly the uptime
   (`time_reads_clock`); and the sleep it waits in never ends early (`sleep_on_time`). It asks
   the display server for events without blocking (POLL), so the close button, keys and
   clicks still work while it keeps time.

   Three tabs at the top, Clock, Stopwatch and Timer: a click, or C, S and T (Tab, Left and
   Right go through them). The stopwatch and the timer keep running on any tab.
   Stopwatch   space (or Return) starts and stops it, L takes a lap, R resets it (stopped)
   Timer       digits type the time as a microwave's do (1 3 0 is 1:30), Backspace takes the
               last one back, + and - (or Up and Down) add or take a minute; space (or Return)
               starts and pauses it, R resets it. At zero it flashes, on the Timer tab, until
               a key or a click.
   Each has buttons too. The stopwatch and the timer measure with the CPU's own counter
   (lib.h's millis), which runs at one rate whatever the load: the kernel's clock moves a
   tick at a time, each tick set going when the last one is handled, so a late tick puts it
   behind for good. The log says what they measured by both.

   The time of day is shown in the time zone chosen in Settings. The kernel keeps only UTC;
   the zone is the display server's, and Clock asks it every second (ZONE, over the endpoint
   every window already has), so a new zone shows at once and Clock needs nothing more: no
   file, no new capability. */
#include "../ui.h"
#include "../zone.h"

/* All of it runs a few dozen times a second at most: compiled for size (as Terminal's
   commands are), but for the drawing of text and rounded rectangles, the one part that
   loops over pixels. `make` prints each program's size and what is left of its run. */
#define COLD __attribute__((cold, minsize))

#define CW 300
#define CH 150
#define BG rgb(20, 22, 32)
#define ACCENT rgb(126, 214, 255)
#define GRAY rgb(130, 136, 160)
#define DIM rgb(96, 104, 130)
#define FLASH rgb(196, 64, 56)
#define GO rgb(30, 86, 116)
#define STOP rgb(122, 46, 52)

/* the tabs: one pill across the top, a third each */
#define TX 33
#define TY 6
#define TSW 78
#define TH 22
/* the buttons, along the bottom */
#define BY 116
#define BH 26

enum { CLOCK, WATCH, TIMER };
enum { IDLE, RUNNING, PAUSED, DONE };
#define TIMER_MAX (99 * 60 + 59)

struct clock {
    struct ui ui;
    struct surface win;
    u64 shown;               /* the second on screen */
    u64 ticks;               /* the kernel's tick count behind it */
    long zone;               /* the time zone it shows, minutes east of UTC */
    int said;                /* the time of day was logged in this zone */
    int mode;                /* the tab shown */
    u64 view;                /* what is drawn, to draw again only when it changes */
    u64 kms;                 /* the kernel's clock now, in ms (the counter's: `now`) */
    /* the stopwatch: `acc` ms before it last started, at `from`, by the counter (and `kacc`,
       `kfrom` by the kernel's clock) */
    int w_on;
    u64 w_acc, w_from, w_kacc, w_kfrom, w_mark, laps, lap[2];
    /* the timer: `set` seconds (`entry`: as typed); running, it ends at `end`, and began,
       less any pause, at `began` (`kbegan` by the kernel's clock) */
    int t_state, t_typing;
    u64 t_set, t_entry, t_len, t_end, t_left, t_began, t_kbegan, t_paused, t_kpaused, flash_from;
};

/* The kernel's clock: ticks since boot, milliseconds, and hours, minutes, seconds. */
struct time { u64 ticks, ms, h, m, s, wall; };
COLD static struct time kernel_time(void) {
    struct res r = sys0(SYS_TIME);
    return (struct time){r.x[1], r.x[2], r.x[3], r.x[4], r.x[5], r.x[6]};
}

COLD static void two(struct line *l, u64 v) {
    if (v < 10) put_s(l, "0");
    put_dec(l, v);
}

/* mm:ss.cc, or h:mm:ss from an hour on */
COLD static void put_watch(struct line *l, u64 ms) {
    u64 s = ms / 1000;
    if (s >= 3600) {
        put_dec(l, s / 3600);
        put_s(l, ":");
        two(l, s / 60 % 60);
        put_s(l, ":");
        two(l, s % 60);
        return;
    }
    two(l, s / 60);
    put_s(l, ":");
    two(l, s % 60);
    put_s(l, ".");
    two(l, ms / 10 % 100);
}

/* mm:ss */
COLD static void put_mmss(struct line *l, u64 s) {
    two(l, s / 60);
    put_s(l, ":");
    two(l, s % 60);
}

/* The end of a log line, and a whole one. */
COLD static void end(struct line *l, const char *s) {
    put_s(l, s);
    put_s(l, "\n");
    flush(l);
}
COLD static void say(struct line *l, const char *s) {
    put_s(l, "clock: ");
    end(l, s);
}

static const char *const tab_names[3] = {"Clock", "Stopwatch", "Timer"};
static const char *const mode_says[3] = {"showing the clock", "showing the stopwatch", "showing the timer"};

COLD static u64 watch_ms(struct clock *c, u64 now) { return c->w_acc + (c->w_on ? now - c->w_from : 0); }
/* whole seconds left on the timer, rounded up: 3, 2, 1, then done */
COLD static u64 timer_left(struct clock *c, u64 now) {
    u64 ms = c->t_state == RUNNING ? (c->t_end > now ? c->t_end - now : 0)
           : c->t_state == PAUSED ? c->t_left : c->t_state == DONE ? 0 : c->t_set * 1000;
    return (ms + 999) / 1000;
}
COLD static int flash_on(struct clock *c, u64 now) { return c->t_state == DONE && (now - c->flash_from) / 500 % 2 == 0; }

/* Text centered on x as `shape` would be (the big numbers take a template of the same shape,
   so they stay put as they change), and a rounded rectangle: each drawn in one place, not
   inlined at every call, which keeps Clock's code small. */
__attribute__((noinline)) static void text_at(struct clock *c, const struct font *f, int x, int y, const char *s,
                                              const char *shape, unsigned color) {
    font_text(&c->win, f, x - font_width(f, shape) / 2, y, s, color);
}
__attribute__((noinline)) static void pill(struct clock *c, int x, int y, int w, int h, int r, unsigned color) {
    round_rect(&c->win, x, y, w, h, r, color, 255);
}
COLD static void centered(struct clock *c, const struct font *f, int y, const char *s, unsigned color) {
    text_at(c, f, CW / 2, y, s, s, color);
}
COLD static void big(struct clock *c, const char *s, const char *shape, unsigned color) {
    text_at(c, &c->ui.huge, CW / 2, 70, s, shape, color);
}

/* n buttons along the bottom, the last one the main one (in `main`); `off`, a bit each, are
   dimmed: they do nothing now. */
COLD static void buttons(struct clock *c, int n, const char *const *label, unsigned off, unsigned main) {
    int w = (CW - 30 - 6 * (n - 1)) / n;
    for (int i = 0; i < n; i++) {
        int x = 15 + i * (w + 6), dim = off >> i & 1;
        pill(c, x, BY, w, BH, 8, dim ? rgb(30, 33, 46) : i == n - 1 ? main : rgb(40, 44, 62));
        text_at(c, &c->ui.small_bold, x + w / 2, BY + 17, label[i], label[i], dim ? rgb(70, 76, 98) : rgb(214, 220, 236));
    }
}
COLD static int button_at(int n, int x, int y) {
    int w = (CW - 30 - 6 * (n - 1)) / n;
    if (y < BY || y >= BY + BH || x < 15) return -1;
    int i = (x - 15) / (w + 6);
    return i < n && (x - 15) % (w + 6) < w ? i : -1;
}

COLD static void draw_clock(struct clock *c, struct time t) {
    /* The time of day, if the network has said what it is; else the time since boot. */
    struct date d = date_of(local_of(t.wall, c->zone));
    struct line l = {.n = 0};
    two(&l, t.wall ? (u64)d.h : t.h);
    put_s(&l, ":");
    two(&l, t.wall ? (u64)d.m : t.m);
    put_s(&l, ":");
    two(&l, t.wall ? (u64)d.s : t.s);
    l.b[l.n] = 0;
    big(c, l.b, l.b, ACCENT);
    struct line u = {.n = 0};
    if (t.wall) {
        put_s(&u, day_names[d.weekday]);
        put_s(&u, ", ");
        put_s(&u, month_names[d.month - 1]);
        put_s(&u, " ");
        put_dec(&u, (u64)d.day);
        put_s(&u, ", ");
        put_dec(&u, (u64)d.year);
        put_s(&u, " (");
        put_zone(&u, c->zone);
        put_s(&u, ")");
    } else put_s(&u, "up since the Pi started");
    u.b[u.n] = 0;
    centered(c, &c->ui.small, 96, u.b, GRAY);
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
    centered(c, &c->ui.small, 120, k.b, DIM);
    centered(c, &c->ui.small, 138, "proved never to go back", DIM);
}

COLD static void draw_watch(struct clock *c, u64 now) {
    u64 ms = watch_ms(c, now);
    struct line l = {.n = 0};
    put_watch(&l, ms);
    l.b[l.n] = 0;
    big(c, l.b, ms >= 3600000 ? "0:00:00" : "00:00.00", ACCENT);
    centered(c, &c->ui.small, 90, c->w_on ? "running" : ms ? "stopped" : "space starts and stops, L laps, R resets",
             GRAY);
    if (c->laps) {                   /* the last two laps, the newest first */
        struct line p = {.n = 0};
        for (u64 i = 0; i < 2 && i < c->laps; i++) {
            put_s(&p, i ? "     lap " : "lap ");
            put_dec(&p, c->laps - i);
            put_s(&p, "  ");
            put_watch(&p, c->lap[i]);
        }
        p.b[p.n] = 0;
        centered(c, &c->ui.small, 106, p.b, DIM);
    }
    static const char *const run[3] = {"Reset", "Lap", "Stop"}, *const stop[3] = {"Reset", "Lap", "Start"};
    buttons(c, 3, c->w_on ? run : stop, c->w_on ? 1 : ms ? 2 : 3, c->w_on ? STOP : GO);
}

COLD static void draw_timer(struct clock *c, u64 now) {
    int flash = flash_on(c, now), done = c->t_state == DONE;
    if (flash) fill(&c->win, 0, TY + TH + 4, CW, CH - TY - TH - 4, FLASH);
    struct line l = {.n = 0};
    put_mmss(&l, timer_left(c, now));
    l.b[l.n] = 0;
    big(c, l.b, "00:00", done ? (flash ? rgb(255, 255, 255) : rgb(255, 120, 110)) : ACCENT);
    struct line s = {.n = 0};
    if (done) {
        put_s(&s, "time is up (");
        put_mmss(&s, c->t_len);
        put_s(&s, ")");
    } else put_s(&s, c->t_state == RUNNING ? "counting down" : c->t_state == PAUSED ? "paused"
                     : "type the time (1 3 0 is 1:30), or + and -");
    s.b[s.n] = 0;
    centered(c, &c->ui.small, 90, s.b, flash ? rgb(255, 230, 226) : GRAY);
    if (done) {
        centered(c, &c->ui.small, 106, "a key or a click stops it", flash ? rgb(255, 230, 226) : GRAY);
        return;
    }
    static const char *const idle[4] = {"Reset", "- 1 min", "+ 1 min", "Start"},
                             *const run[4] = {"Reset", "- 1 min", "+ 1 min", "Pause"};
    int going = c->t_state == RUNNING, set = c->t_state == IDLE;
    unsigned off = (set ? 1 : 0) | (!set || c->t_set <= 60 ? 2 : 0) | (!set || c->t_set >= TIMER_MAX ? 4 : 0)
                 | (set && !c->t_set ? 8 : 0);
    buttons(c, 4, going ? run : idle, off, going ? STOP : GO);
}

COLD static void draw(struct clock *c, struct time t, u64 now) {
    struct surface *s = &c->win;
    fill(s, 0, 0, CW, CH, BG);
    pill(c, TX, TY, 3 * TSW, TH, TH / 2, rgb(32, 35, 50));
    pill(c, TX + c->mode * TSW + 2, TY + 2, TSW - 4, TH - 4, TH / 2 - 2, rgb(56, 62, 90));
    for (int i = 0; i < 3; i++)
        text_at(c, &c->ui.small_bold, TX + i * TSW + TSW / 2, TY + 15, tab_names[i], tab_names[i], i == c->mode ? ACCENT : GRAY);
    if (c->mode == CLOCK) draw_clock(c, t);
    else if (c->mode == WATCH) draw_watch(c, now);
    else draw_timer(c, now);
}

COLD static void show(struct clock *c, struct line *l, int mode) {
    if (mode == c->mode) return;
    c->mode = mode;
    say(l, mode_says[mode]);
}

/* The stopwatch: start or stop it, a lap, or back to zero. */
COLD static void watch_go(struct clock *c, struct line *l, u64 now) {
    if (!c->w_on) {
        c->w_on = 1;
        c->w_from = now;
        c->w_kfrom = c->kms;
        say(l, "stopwatch started");
        return;
    }
    c->w_on = 0;
    c->w_acc += now - c->w_from;
    c->w_kacc += c->kms - c->w_kfrom;
    put_s(l, "clock: stopwatch stopped at ");
    put_watch(l, c->w_acc);
    put_s(l, " (");
    put_dec(l, c->w_acc);
    put_s(l, " ms by the counter, ");
    put_dec(l, c->w_kacc);
    end(l, " by the kernel's clock)");
}
COLD static void watch_lap(struct clock *c, struct line *l, u64 now) {
    if (!c->w_on) return;
    u64 ms = watch_ms(c, now);
    c->lap[1] = c->lap[0];
    c->lap[0] = ms - c->w_mark;
    c->w_mark = ms;
    c->laps++;
    put_s(l, "clock: stopwatch lap ");
    put_dec(l, c->laps);
    put_s(l, ", ");
    put_watch(l, c->lap[0]);
    end(l, "");
}
COLD static void watch_reset(struct clock *c, struct line *l) {
    if (c->w_on || !c->w_acc) return;
    c->w_acc = c->w_kacc = c->w_mark = c->laps = 0;
    say(l, "stopwatch reset");
}

/* The timer: set it, start or pause it, back to what it was set to. */
COLD static void timer_set(struct clock *c, struct line *l, u64 s) {
    if (c->t_state != IDLE) return;
    c->t_set = s > TIMER_MAX ? TIMER_MAX : s;
    c->t_entry = c->t_set / 60 * 100 + c->t_set % 60;
    c->t_typing = 0;
    put_s(l, "clock: timer set to ");
    put_mmss(l, c->t_set);
    end(l, "");
}
COLD static void timer_go(struct clock *c, struct line *l, u64 now) {
    if (c->t_state == RUNNING) {
        c->t_state = PAUSED;
        c->t_left = c->t_end > now ? c->t_end - now : 0;
        c->t_paused = now;
        c->t_kpaused = c->kms;
        put_s(l, "clock: timer paused, ");
        put_mmss(l, timer_left(c, now));
        end(l, " left");
    } else if (c->t_state == PAUSED) {
        c->t_state = RUNNING;
        c->t_end = now + c->t_left;
        c->t_began += now - c->t_paused;     /* the pause does not count */
        c->t_kbegan += c->kms - c->t_kpaused;
        say(l, "timer going again");
    } else if (c->t_state == IDLE && c->t_set) {
        c->t_state = RUNNING;
        c->t_len = c->t_set;
        c->t_end = now + c->t_set * 1000;
        c->t_began = now;
        c->t_kbegan = c->kms;
        put_s(l, "clock: timer started, ");
        put_mmss(l, c->t_set);
        end(l, "");
    }
}
COLD static void timer_reset(struct clock *c, struct line *l) {
    if (c->t_state == IDLE) return;
    c->t_state = IDLE;
    put_s(l, "clock: timer reset to ");
    put_mmss(l, c->t_set);
    end(l, "");
}
/* digits as typed, MMSS: 9 0 is 1:30, and 9 0 0 is 9:00. The first digit starts afresh. */
COLD static void timer_digit(struct clock *c, struct line *l, u64 d) {
    u64 e = ((c->t_typing ? c->t_entry * 10 : 0) + d) % 10000;
    timer_set(c, l, e / 100 * 60 + e % 100);
    c->t_entry = e;
    c->t_typing = 1;
}

COLD static void key(struct clock *c, struct line *l, u64 k, u64 now) {
    if (c->t_state == DONE) {               /* any key stops the flash */
        timer_reset(c, l);
        return;
    }
    u64 lower = k >= 'A' && k <= 'Z' ? k + 32 : k, set = c->t_state == IDLE;
    if (lower == 'c') show(c, l, CLOCK);
    else if (lower == 's') show(c, l, WATCH);
    else if (lower == 't') show(c, l, TIMER);
    else if (k == '\t' || k == KEY_RIGHT) show(c, l, (c->mode + 1) % 3);
    else if (k == KEY_LEFT) show(c, l, (c->mode + 2) % 3);
    else if (c->mode == WATCH) {
        if (k == ' ' || k == '\r' || k == '\n') watch_go(c, l, now);
        else if (lower == 'l') watch_lap(c, l, now);
        else if (lower == 'r') watch_reset(c, l);
    } else if (c->mode == TIMER) {
        if (k == ' ' || k == '\r' || k == '\n') timer_go(c, l, now);
        else if (lower == 'r') timer_reset(c, l);
        else if (k >= '0' && k <= '9' && set) timer_digit(c, l, k - '0');
        else if ((k == 8 || k == 127) && set) {
            u64 e = c->t_entry / 10;
            timer_set(c, l, e / 100 * 60 + e % 100);
            c->t_entry = e;
            c->t_typing = 1;
        } else if (k == '+' || k == '=' || k == KEY_UP) timer_set(c, l, c->t_set + 60);
        else if ((k == '-' || k == KEY_DOWN) && c->t_set > 60) timer_set(c, l, c->t_set - 60);
    }
}

COLD static void click(struct clock *c, struct line *l, int x, int y, u64 now) {
    if (c->t_state == DONE) {               /* any click stops the flash */
        timer_reset(c, l);
        return;
    }
    if (y >= TY && y < TY + TH && x >= TX && x < TX + 3 * TSW) show(c, l, (x - TX) / TSW);
    else if (c->mode == WATCH) {
        int b = button_at(3, x, y);
        if (b == 0) watch_reset(c, l);
        else if (b == 1) watch_lap(c, l, now);
        else if (b == 2) watch_go(c, l, now);
    } else if (c->mode == TIMER) {
        int b = button_at(4, x, y);
        if (b == 0) timer_reset(c, l);
        else if (b == 1 && c->t_set > 60) timer_set(c, l, c->t_set - 60);
        else if (b == 2) timer_set(c, l, c->t_set + 60);
        else if (b == 3) timer_go(c, l, now);
    }
}

/* What the tab shown shows now, as one number: drawn again when it changes. */
COLD static u64 view_of(struct clock *c, struct time t, u64 now) {
    u64 v = c->mode == CLOCK ? t.ms / 1000 : c->mode == WATCH ? watch_ms(c, now) / 10 * 2 + (u64)c->w_on
          : timer_left(c, now) * 8 + (u64)c->t_state * 2 + (u64)flash_on(c, now);
    return v * 4 + (u64)c->mode;
}

COLD __attribute__((section(".text.start"))) void _start(void) {
    struct clock *c = (struct clock *)DATA;
    struct line l = {.n = 0};
    ui_load(&c->ui, app_assets());
    c->win = app_surface(CW, CH);
    struct time t = kernel_time();
    c->shown = t.ms / 1000;
    c->ticks = t.ticks;
    c->zone = app_zone();
    c->said = 0;
    c->mode = CLOCK;
    c->w_on = 0;
    c->w_acc = c->w_kacc = c->w_mark = c->laps = c->lap[0] = c->lap[1] = 0;
    c->t_state = IDLE;
    c->t_typing = 0;
    c->t_set = 5 * 60;
    c->t_entry = 500;
    draw(c, t, millis());
    c->view = view_of(c, t, millis());
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
        c->kms = t.ms;
        u64 now = millis();
        int changed = e.kind == EV_KEY || e.kind == EV_DOWN;
        if (e.kind == EV_KEY) key(c, &l, e.a, now);
        else if (e.kind == EV_DOWN) click(c, &l, (int)e.a, (int)e.b, now);
        if (c->t_state == RUNNING && now >= c->t_end) {      /* the timer is done: flash, on its tab */
            c->t_state = DONE;
            c->flash_from = now;
            put_s(&l, "clock: timer done after ");
            put_dec(&l, c->t_len);
            put_s(&l, " s (");
            put_dec(&l, now - c->t_began);
            put_s(&l, " ms by the counter, ");
            put_dec(&l, t.ms - c->t_kbegan);
            end(&l, " by the kernel's clock)");
            show(c, &l, TIMER);
            changed = 1;
        }
        if (t.ms / 1000 != c->shown) {
            c->shown = t.ms / 1000;
            long zone = app_zone();
            if (zone != c->zone) {
                c->zone = zone;
                c->said = 0;
                changed = 1;             /* draw it now */
            }
            if (t.wall && !c->said) {    /* for the log: the time shown, and UTC, from one reading */
                c->said = 1;
                put_s(&l, "clock: in ");
                put_zone(&l, c->zone);
                put_s(&l, " it is ");
                put_local(&l, t.wall, c->zone);
                put_s(&l, " (Unix time ");
                put_dec(&l, t.wall);
                put_s(&l, ")\n");
                flush(&l);
            }
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
        u64 view = view_of(c, t, now);
        if (changed || view != c->view) {
            c->view = view;
            draw(c, t, now);
            dirty = 1;
            continue;                    /* the display shows it at the next POLL: now */
        }
        /* A key or a click waits a tenth of a second at most, a running stopwatch on screen is
           drawn 25 times a second, the clock at each second, and the timer ends on time. */
        u64 wait = 1000 - t.ms % 1000, most = c->mode == WATCH && c->w_on ? 40 : 100;
        if (wait > most) wait = most;
        if (c->t_state == RUNNING && c->t_end - now < wait) wait = c->t_end - now;
        sleep_ms(wait);
    }
}
