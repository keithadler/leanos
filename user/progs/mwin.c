/* mwin: a program from the card with three windows (test/windows.sh).

   A program may open several windows. Each has a number (0 for its first, then the lowest
   it is not using), one wait hears the events of all of them, and each event says which
   window it is for (user/app.h). mwin opens three windows of one color each and says every
   event it hears, with its window's number: clicks, keys, a copy (it answers with the
   window's number) and a paste. When the middle window's close button is clicked, it checks
   the window is gone from the display's table (closing it again is refused), opens another
   (it must get the same number), and closes that one itself (CLOSE), twice (the second
   refused). When the first window's close button is clicked, it closes the last itself,
   then asks for an event with no window left (WAIT and POLL must answer at once, with none)
   and stops. Every line starts "mwin: ". */
#include "../app.h"

#define MW 200
#define MH 120
#define MPAGES ((MW * MH * 4 + 4095) / 4096)
/* the windows' pixels in the spare run, after the assets: one run of pages each */
#define OFF(i) (APP_WIN_OFFSET + (u64)(i) * MPAGES)

static const unsigned colors[4] = {0xd04040, 0x40b040, 0x4060d0, 0xd0c040};   /* red, green, blue, yellow */

static void say(const char *a, long n, const char *b) {
    struct line l = {.n = 0};
    put_s(&l, "mwin: ");
    put_s(&l, a);
    if (n >= 0) put_dec(&l, (u64)n);
    put_s(&l, b);
    put_s(&l, "\n");
    flush(&l);
}

/* A window of one color from pages `at` of the spare run: its number, or -1. */
static long open_one(int at, unsigned color, const char *title) {
    struct surface s = app_surface_at(OFF(at), MW, MH);
    fill(&s, 0, 0, MW, MH, color);
    return app_window_at(OFF(at), MW, MH, title);
}

/* A raw WAIT or POLL: with no window, the display answers at once. */
static u64 ask(u64 op) {
    struct res r = sys(SYS_CALL, ENDPOINT, op, 7, 0, 0);
    return r.status == OK ? r.x[1] : ~0UL;
}

__attribute__((section(".text.start"))) void _start(void) {
    app_assets();
    long a = open_one(0, colors[0], "one"), b = open_one(1, colors[1], "two"), c = open_one(2, colors[2], "three");
    struct line l = {.n = 0};
    put_s(&l, "mwin: opened windows ");
    put_dec(&l, (u64)a);
    put_s(&l, ", ");
    put_dec(&l, (u64)b);
    put_s(&l, ", ");
    put_dec(&l, (u64)c);
    put_s(&l, "\n");
    flush(&l);
    if (a < 0 || b < 0 || c < 0) exit_task();
    char pasted[64];
    int np = 0;
    for (;;) {
        struct event e = app_wait(0);
        long w = (long)e.win;
        if (e.kind == EV_DOWN) {
            put_s(&l, "mwin: window ");
            put_dec(&l, e.win);
            put_s(&l, ": click at (");
            put_dec(&l, e.a);
            put_s(&l, ", ");
            put_dec(&l, e.b);
            put_s(&l, ")\n");
            flush(&l);
        } else if (e.kind == EV_KEY) {
            char k[2] = {e.a >= 32 && e.a < 127 ? (char)e.a : '?', 0};
            put_s(&l, "mwin: window ");
            put_dec(&l, e.win);
            put_s(&l, ": key '");
            put_s(&l, k);
            put_s(&l, "'\n");
            flush(&l);
        } else if (e.kind == EV_COPY) {
            char text[] = "from window ?";
            text[12] = (char)('0' + e.win);
            app_copy(text, 13);
            say("copy asked of window ", w, "");
        } else if (e.kind == EV_PASTE) {
            char t[16];
            int n = paste_text(e, t);
            for (int i = 0; i < n && np < 63; i++) pasted[np++] = t[i];
            if (n < 16) {
                pasted[np] = 0;
                put_s(&l, "mwin: window ");
                put_dec(&l, e.win);
                put_s(&l, ": paste '");
                put_s(&l, pasted);
                put_s(&l, "'\n");
                flush(&l);
                np = 0;
            }
        } else if (e.kind == EV_CLOSE) {
            say("window ", w, ": closed by its button");
            if (w == b) {
                /* gone from the display's table: closing it again is refused */
                say("closing window ", w, app_close((u64)w) == OK ? " again: TAKEN" : " again: refused");
                /* its number is free: the next window takes it */
                long d = open_one(1, colors[3], "four");
                say("opened another window: ", d, d == b ? ", the closed one's number" : ", NOT the closed one's number");
                say("closed window ", d, app_close((u64)d) == OK ? " itself" : " itself: REFUSED");
                say("closing window ", d, app_close((u64)d) == OK ? " twice: TAKEN" : " twice: refused");
                say("ready", -1, "");
            } else if (w == a) {
                say("closed window ", c, app_close((u64)c) == OK ? " itself" : " itself: REFUSED");
                u64 wt = ask(OP_WAIT), pl = ask(OP_POLL);
                say(wt == EV_NONE && pl == EV_NONE ? "no window left: WAIT and POLL answer at once, with no event"
                                                   : "no window left: WAIT or POLL answered WRONG", -1, "");
                exit_task();
            }
        }
    }
}
