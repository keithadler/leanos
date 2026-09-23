/* hello: the first program that is not in the kernel image. It lives on the SD card as an
   ELF file; Terminal's `run hello` loads it into an open slot. The manifest gives that slot
   its own memory and a window from the display server, and nothing else, whatever program
   runs there. It draws its window with the built-in 5x7 font (it has no assets) and counts
   the keys typed into it. */
#include "../app.h"

#define HW 360
#define HH 150

struct hello {
    struct surface win;
    u64 keys;
    char last;
};

static void draw(struct hello *h) {
    struct surface *s = &h->win;
    fill(s, 0, 0, HW, HH, rgb(250, 250, 252));
    text(s, 16, 16, "Hello from the SD card", rgb(30, 30, 36), 2);
    text(s, 16, 48, "Not in the manifest: loaded from a file,", rgb(90, 90, 100), 1);
    text(s, 16, 60, "measured, and given only its own memory", rgb(90, 90, 100), 1);
    text(s, 16, 72, "and this window.", rgb(90, 90, 100), 1);
    struct line l = {.n = 0};
    put_s(&l, "keys typed: ");
    put_dec(&l, h->keys);
    if (h->keys) {
        put_s(&l, "  last: ");
        char c[2] = {h->last, 0};
        put_s(&l, c);
    }
    l.b[l.n] = 0;
    text(s, 16, 110, l.b, rgb(58, 110, 230), 2);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct hello *h = (struct hello *)DATA;
    struct line l = {.n = 0};
    app_assets();                     /* maps the spare run, where the window's pixels go */
    h->win = app_surface(HW, HH);
    h->keys = 0;
    h->last = 0;
    draw(h);
    u64 opened = app_open(HW, HH, "Hello");
    put_s(&l, "hello: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "hello: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind != EV_KEY || e.a < 32 || e.a > 126) continue;
        h->keys++;
        h->last = (char)e.a;
        draw(h);
        dirty = 1;
    }
}
