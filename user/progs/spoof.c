/* spoof: a program from the card that tries to take another program's name (test/spoof.sh).

   The display server names a window after the program it came from, and `run`, Apps and the
   dock's pinned programs look for that name: `run clock` or a click on Clock brings the
   window named clock forward instead of starting Clock. The name comes with the icon a
   program lends (ICON, user/app.h): four pages that start with the loader's marker and end
   with the name of the file the loader ran. A program can write a marker and any name into
   its own memory; the display must take a name only from the pages the loader wrote, in the
   program's code run, which nothing can write (user/display.c, on_icon).

   It opens two windows (a well-formed icon may name only one), then lends four pages with
   the marker, an icon and the name "clock", from each run it holds: the spare run (read-only,
   read-write, and asking for the execute right it does not have there), its data pages and
   its stack, each as its own capability gives them. Then its code run without the execute
   right (the loader's pages, its own name), and with it, from pages the loader did not write
   (no marker). The display must refuse every one, and afterwards nothing may be named clock.
   Last, the pages the loader wrote, as app_open lends them: its own name, which the display
   must take. Every line starts "spoof: ".

   Its stack moves into its data pages first, so the whole stack run is free to hold a
   forged icon (the display reads the name from a run's last 16 bytes: the stack's top). */
#include "../app.h"
#include "../elf.h"

#define WIN_W 120
#define WIN_H 60
#define WIN_PAGES 8                 /* 120 x 60 x 4 = 28800 bytes */
#define FORGE_OFF 160               /* four pages of the spare run for a forged icon */

static void say(const char *a, const char *b, const char *c) {
    struct line l = {.n = 0};
    put_s(&l, "spoof: ");
    put_s(&l, a);
    put_s(&l, b);
    put_s(&l, c);
    put_s(&l, "\n");
    flush(&l);
}

/* Four pages that look like the loader's: the marker, an icon's size and pixels, and a
   name at the very end. */
static void forge(unsigned char *at, const char *name) {
    memset(at, 0, 4 * 4096);
    unsigned *m = (unsigned *)at;
    m[0] = ICON_MAGIC;
    m[1] = 8 + 16 * 16 * 4;
    m[2] = 16;
    m[3] = 16;
    for (int i = 0; i < 16 * 16; i++) m[4 + i] = 0xffe04030;
    for (int i = 0; i < 15 && name[i]; i++) at[ICON_NAME_AT + i] = (unsigned char)name[i];
}

static struct res raise_name(const char *name) {
    u64 w[2] = {0, 0};
    for (int i = 0; i < 15 && name[i]; i++) w[i / 8] |= (u64)(unsigned char)name[i] << (8 * (i % 8));
    return sys(SYS_CALL, ENDPOINT, OP_RAISE, w[0], w[1], 0);
}

static int open_window(u64 off, unsigned color) {
    unsigned *px = (unsigned *)PAGE(SPARE_PAGE + off);
    for (int i = 0; i < WIN_W * WIN_H; i++) px[i] = color;
    struct res d = sys(SYS_DERIVE, SPARE, R, off, WIN_PAGES, 0);
    if (d.status != OK) return 0;
    struct res r = sys(SYS_CALL, ENDPOINT, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0x666f6f7073 /* "spoof" */, d.x[1] + 1);
    return r.status == OK && r.x[1] == 0;
}

/* Lend `count` pages of run `cap` from `off`, asking for `rights`, as an icon. The rights
   the capability really has (what derive gave) go in the line. 1 if the display took it. */
static int lend(const char *what, u64 cap, u64 rights, u64 off, u64 count) {
    struct res d = sys(SYS_DERIVE, cap, rights, off, count, 0);
    if (d.status != OK) {
        say(what, ": could not derive it", "");
        return 0;
    }
    u64 bits = sys1(SYS_CAPINFO, d.x[1]).x[1];
    char rwx[4] = {bits & R ? 'r' : '-', bits & W ? 'w' : '-', bits & X ? 'x' : '-', 0};
    struct res r = sys(SYS_CALL, ENDPOINT, OP_ICON, 0, 0, d.x[1] + 1);
    sys1(SYS_DROP, d.x[1]);
    int took = r.status == OK && r.x[1] == 0;
    struct line l = {.n = 0};
    put_s(&l, "spoof: ");
    put_s(&l, what);
    put_s(&l, " (");
    put_s(&l, rwx);
    put_s(&l, took ? "): taken" : "): refused");
    put_s(&l, "\n");
    flush(&l);
    return took;
}

__attribute__((used, noreturn)) void spoof_main(u64 stack_top) {
    app_assets();
    int wins = open_window(64, 0x3050a0) + open_window(64 + WIN_PAGES, 0x50a030);
    struct line l = {.n = 0};
    put_s(&l, "spoof: opened ");
    put_dec(&l, (u64)wins);
    put_s(&l, " windows\n");
    flush(&l);

    /* the name "clock", with an icon, in every run it can write */
    unsigned char *stack = (unsigned char *)(stack_top - 4 * 4096);
    forge((unsigned char *)PAGE(SPARE_PAGE + FORGE_OFF), "clock");
    forge((unsigned char *)DATA, "clock");
    forge(stack, "clock");
    int taken = 0, tries = 0, named = 0;
    const char *const whats[] = {"clock from its spare pages, read-only", "clock from its spare pages, read-write",
                                 "clock from its spare pages, asking for execute", "clock from its data pages",
                                 "clock from its stack"};
    const u64 caps[] = {SPARE, SPARE, SPARE, 1, 2}, rights[] = {R, R | W, R | X, R | X, R | X},
              offs[] = {FORGE_OFF, FORGE_OFF, FORGE_OFF, 0, 0};
    for (int i = 0; i < 5; i++, tries++) {
        taken += lend(whats[i], caps[i], rights[i], offs[i], 4);
        struct res r = raise_name("clock");
        named += r.status == OK && r.x[1] == 0;
    }
    /* its code run: the loader's pages without the execute right, then pages the loader did
       not write, with it */
    taken += lend("its own name from its code run, read-only", 0, R, ICON_IMAGE_PAGE, 4);
    taken += lend("its code run from page 0, no marker", 0, R | X, 0, 4);
    tries += 2;
    struct res r = raise_name("clock");
    named += r.status == OK && r.x[1] == 0;
    put_s(&l, "spoof: claims refused: ");
    put_dec(&l, (u64)(tries - taken));
    put_s(&l, " of ");
    put_dec(&l, (u64)tries);
    put_s(&l, named ? "; a window was named clock" : "; no window named clock");
    put_s(&l, "\n");
    flush(&l);

    /* the pages the loader wrote, as app_open lends them: its own name */
    int own = lend("its own name from its code run, read and execute", 0, R | X, ICON_IMAGE_PAGE, 4);
    r = raise_name("spoof");
    put_s(&l, "spoof: done: its own name ");
    put_s(&l, own && r.status == OK && r.x[1] == 0 ? "taken, and found by name" : "NOT taken");
    put_s(&l, "\n");
    flush(&l);

    for (;;) {
        struct event e = app_wait(0);
        if (e.kind == EV_CLOSE) exit_task();
    }
}

/* Move the stack into the data pages, to their end at PAGE(24) (0x80018000), so pages 20 to
   23 hold it, and run, told where it was: the stack run's top. */
__attribute__((naked, section(".text.start"))) void _start(void) {
    __asm__ volatile("mov x0, sp\n"
                     "movz x9, #0x8001, lsl #16\n"
                     "movk x9, #0x8000\n"
                     "mov sp, x9\n"
                     "b spoof_main\n");
}
