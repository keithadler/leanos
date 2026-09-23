/* fuzz: throws thousands of system calls with made-up arguments at the kernel, from an open
   slot, and checks every answer against what the proofs promise:

     - a call that needs a capability this slot does not hold (power, start, exec, the
       disk, interrupts) is always refused;
     - a number that is not a system call gets "no such call";
     - write never reads memory the slot has not mapped;
     - a derived capability never has a right, or a frame, its source did not have;
     - after all of it, the slot is still itself: same badge, same data, same code.

   It keeps the calls that would only hurt itself out of the mix (unmapping the pages it
   uses, dropping its own capabilities), because a program that shoots itself proves nothing about
   the kernel. Everything else is fair game, including junk messages to the display server,
   which must keep working. The seed is printed, so a failure can be run again. */
#include "../ui.h"

#define FW 420
#define FH 250
/* The pages it leaves alone: code, data, its assets and window (the spare run, from page 64),
   and its stack (the last four of 8192). Maps and unmaps land between. */
#define FREE_LO 300
#define FREE_HI 8180
#define ROUNDS 40
#define PER_ROUND 500

enum { NCHECK = 6 };
static const char *check_names[NCHECK] = {
    "calls needing a capability it lacks", "numbers that are not calls", "writes from memory it has not mapped",
    "derived capabilities", "messages to the display server", "calls it may make",
};

struct fuzz {
    struct ui ui;
    struct surface win;
    u64 seed, rng, calls, round, first_cap, last;
    u64 ok[NCHECK], bad[NCHECK];
    char why[80];
    u64 canary[64];
    u64 code_sum;
    int done;
};

static u64 next(struct fuzz *f) {
    u64 x = f->rng;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return f->rng = x;
}

/* Arguments that find edges: small numbers, boundaries, and anything at all. */
static u64 arg(struct fuzz *f) {
    static const u64 edge[] = {0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 255, 256, 4095, 4096, 0x7fffffff,
                               0x80000000UL, 0xffffffffUL, 1UL << 32, 1UL << 48, 1UL << 63, ~0UL, ~0UL - 1};
    switch (next(f) % 4) {
    case 0: return next(f) % 40;
    case 1: return edge[next(f) % (sizeof edge / sizeof edge[0])];
    case 2: return next(f) % 9000;
    default: return next(f);
    }
}

/* Addresses no task may read: the kernel's own memory, devices, and nowhere at all. */
static u64 bad_address(struct fuzz *f) {
    static const u64 bad[] = {0, 0x1000, 0x80000, 0x40000000UL, 0x7ffff000UL, 0xfe201000UL,
                              0x80000000UL + 8192 * 4096UL, 1UL << 40, 1UL << 48, ~0UL - 4095};
    return bad[next(f) % (sizeof bad / sizeof bad[0])] + next(f) % 4096;
}

static u64 ncaps(void) {
    u64 n = 0;
    while (sys1(SYS_CAPINFO, n).status == OK) n++;
    return n;
}

static void fail(struct fuzz *f, int check, const char *what, u64 call, u64 answer) {
    f->bad[check]++;
    if (f->why[0]) return;
    struct line l = {.n = 0};
    put_s(&l, what);
    put_s(&l, " (call ");
    put_dec(&l, call);
    put_s(&l, ", got ");
    put_dec(&l, answer);
    put_s(&l, ")");
    for (u64 i = 0; i < l.n && i < sizeof f->why - 1; i++) f->why[i] = l.b[i];
    f->why[l.n < sizeof f->why - 1 ? l.n : sizeof f->why - 1] = 0;
}

static void expect_refused(struct fuzz *f, int check, u64 call, struct res r) {
    if (r.status == OK) fail(f, check, "a call it has no capability for succeeded", call, r.status);
    else f->ok[check]++;
}

static void one(struct fuzz *f) {
    u64 pick = next(f) % 16;
    f->calls++;
    if (pick == 0) {                                   /* calls that need what it lacks */
        static const u64 need[] = {SYS_POWER, SYS_START, SYS_EXEC, SYS_BLOCKREAD, SYS_BLOCKWRITE, SYS_IRQACK};
        u64 n = need[next(f) % 6];
        expect_refused(f, 0, n, sys(n, arg(f), arg(f), arg(f), arg(f), arg(f)));
    } else if (pick == 1) {                            /* not a call at all */
        u64 n = 22 + next(f) % 2000;
        if (next(f) % 4 == 0) n = ~0UL - next(f) % 16;
        struct res r = sys(n, arg(f), arg(f), arg(f), arg(f), arg(f));
        if (r.status != NO_CALL) fail(f, 1, "a number that is not a call was taken", n, r.status);
        else f->ok[1]++;
    } else if (pick == 2) {                            /* write from memory it cannot read */
        struct res r = sys(SYS_WRITE, bad_address(f), 1 + next(f) % 64,0,0,0);
        if (r.status == OK) fail(f, 2, "write read memory the slot has not mapped", SYS_WRITE, r.status);
        else f->ok[2]++;
    } else if (pick == 3 || pick == 4) {               /* derive: never more than the source */
        u64 c = next(f) % (f->first_cap + 3);
        struct res src = sys(SYS_CAPINFO, c, 0,0,0,0);
        struct res d = sys(SYS_DERIVE, c, arg(f), arg(f), arg(f), 0);
        if (d.status != OK) { f->ok[3]++; return; }
        if (src.status != OK) { fail(f, 3, "derived from a capability it does not hold", SYS_DERIVE, 0); return; }
        struct res got = sys(SYS_CAPINFO, d.x[1],0,0,0,0);
        if (got.status != OK || (got.x[1] & ~src.x[1]) || got.x[2] != src.x[2] ||
            (src.x[2] == 0 && got.x[3] > src.x[3]))
            fail(f, 3, "a derived capability grew", SYS_DERIVE, got.x[1]);
        else f->ok[3]++;
        /* Map it somewhere, or not; unmap it, or not; then let it go, so every capability
           past its own is one it does not hold. */
        u64 at = FREE_LO + next(f) % (FREE_HI - FREE_LO - 256);   /* a run is at most 228 pages */
        if (next(f) % 2) sys(SYS_MAP, d.x[1], at,0,0,0);
        if (next(f) % 3 == 0) sys(SYS_UNMAP, at, next(f) % 64,0,0,0);
        sys(SYS_DROP, d.x[1],0,0,0,0);
    } else if (pick == 5) {                            /* junk to the display server */
        u64 op = next(f) % 3 ? 7 + next(f) % 300 : next(f) % 8;
        if (next(f) % 2) sys(SYS_SEND, ENDPOINT, op, arg(f), arg(f), 0);
        else if (op != OP_WAIT) sys(SYS_CALL, ENDPOINT, op, arg(f), arg(f), 0);
        f->ok[4]++;
    } else {                                           /* the rest, anything goes */
        static const u64 fine[] = {SYS_YIELD, SYS_CAPINFO, SYS_WHOAMI, SYS_BOOTINFO, SYS_MAP,
                                   SYS_UNMAP, SYS_DROP, SYS_SEND, SYS_REPLY, SYS_SLEEP};
        u64 n = fine[next(f) % (sizeof fine / sizeof fine[0])];
        u64 a0 = arg(f);
        /* Its own frames and endpoint stay put, and so do the pages it uses (unmap takes a
           range of pages, not a capability): those would only hurt itself. */
        if (n == SYS_UNMAP) {
            u64 at = FREE_LO + a0 % (FREE_HI - FREE_LO);
            if (next(f) % 2) sys(SYS_UNMAP, at, next(f) % (FREE_HI - at + 1), 0, 0, 0);
            else sys(SYS_UNMAP, 8192 + a0 % (1UL << 39), arg(f), 0, 0, 0);    /* past the window */
            f->ok[5]++;
            return;
        }
        if ((n == SYS_MAP || n == SYS_DROP) && a0 < f->first_cap)
            a0 = f->first_cap + next(f) % 40;
        if (n == SYS_MAP || n == SYS_DROP) {
            struct res r = sys(n, a0, arg(f), arg(f), 0, 0);
            if (r.status == OK) fail(f, 5, "it acted on a capability it does not hold", n, r.status);
            else f->ok[5]++;
            return;
        }
        if (n == SYS_SEND && a0 == ENDPOINT) a0 = 40;
        if (n == SYS_SLEEP) a0 %= 3;
        sys(n, a0, arg(f), arg(f), arg(f), arg(f));
        f->ok[5]++;
    }
}

static u64 sum_code(void) {
    u64 s = 0;
    const volatile u64 *p = (const volatile u64 *)PAGE(0);
    for (u64 i = 0; i < 12 * 4096 / 8; i++) s = s * 31 + p[i];
    return s;
}

static void draw(struct fuzz *f) {
    struct surface *s = &f->win;
    fill(s, 0, 0, FW, FH, rgb(250, 250, 252));
    font_text(s, &f->ui.title, 20, 36, f->done ? (f->why[0] ? "The kernel slipped" : "Nothing got through")
                                               : "Fuzzing the kernel", rgb(24, 26, 36));
    struct line l = {.n = 0};
    put_dec(&l, f->calls);
    put_s(&l, " system calls with made-up arguments");
    l.b[l.n] = 0;
    font_text(s, &f->ui.body, 20, 62, l.b, rgb(90, 92, 104));
    int bw = FW - 40, done = (int)(f->round * (u64)bw / ROUNDS);
    round_rect(s, 20, 74, bw, 8, 4, rgb(226, 228, 236), 255);
    if (done) round_rect(s, 20, 74, done, 8, 4, f->why[0] ? rgb(220, 72, 62) : rgb(58, 110, 230), 255);
    for (int i = 0; i < NCHECK; i++) {
        int y = 110 + 20 * i;
        struct line n = {.n = 0};
        put_dec(&n, f->ok[i] + f->bad[i]);
        n.b[n.n] = 0;
        font_text(s, &f->ui.bold, 20, y, n.b, rgb(24, 26, 36));
        font_text(s, &f->ui.body, 80, y, check_names[i], rgb(60, 62, 74));
        if (f->bad[i]) font_text(s, &f->ui.bold, FW - 70, y, "FAILED", rgb(220, 72, 62));
        else font_text(s, &f->ui.body, FW - 50, y, "held", rgb(40, 150, 90));
    }
    if (f->why[0]) text_wrap(s, &f->ui.small, 20, FH - 12, FW - 40, 14, f->why, rgb(220, 72, 62));
    else {
        struct line d = {.n = 0};
        put_s(&d, "seed ");
        put_dec(&d, f->seed);
        d.b[d.n] = 0;
        font_text(s, &f->ui.small, 20, FH - 12, d.b, rgb(140, 144, 158));
    }
}

__attribute__((section(".text.start"))) void _start(void) {
    struct fuzz *f = (struct fuzz *)DATA;
    struct line l = {.n = 0};
    memset(f, 0, sizeof *f);
    ui_load(&f->ui, app_assets());
    f->win = app_surface(FW, FH);
    f->seed = f->rng = (ticks() ^ 0x9e3779b97f4a7c15UL) | 1;
    draw(f);
    u64 opened = app_open(FW, FH, "Fuzz");
    put_s(&l, "fuzz: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, ", seed ");
    put_dec(&l, f->seed);
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();

    u64 me = sys0(SYS_WHOAMI).x[1];
    for (int i = 0; i < 64; i++) f->canary[i] = f->seed * (u64)(i + 1);
    f->code_sum = sum_code();
    f->first_cap = ncaps();

    for (f->round = 0; f->round < ROUNDS; f->round++) {
        for (int i = 0; i < PER_ROUND; i++) one(f);
        /* whatever it derived and kept, it lets go of, so the list does not fill up */
        while (sys1(SYS_DROP, f->first_cap).status == OK) {}
        draw(f);
        struct event e = app_poll(1);
        if (e.kind == EV_CLOSE) exit_task();
    }
    if (sys0(SYS_WHOAMI).x[1] != me) fail(f, 5, "its badge changed", SYS_WHOAMI, 0);
    for (int i = 0; i < 64; i++)
        if (f->canary[i] != f->seed * (u64)(i + 1)) { fail(f, 5, "its data changed under it", 0, 0); break; }
    if (sum_code() != f->code_sum) fail(f, 5, "its code changed under it", 0, 0);
    f->done = 1;
    draw(f);

    u64 bad = 0, ok = 0;
    for (int i = 0; i < NCHECK; i++) { bad += f->bad[i]; ok += f->ok[i]; }
    put_s(&l, "fuzz: ");
    put_dec(&l, f->calls);
    put_s(&l, " calls, ");
    put_dec(&l, ok);
    put_s(&l, " answered as promised, ");
    put_dec(&l, bad);
    put_s(&l, " not");
    if (f->why[0]) {
        put_s(&l, ": ");
        put_s(&l, f->why);
    }
    put_s(&l, "\n");
    flush(&l);
    int dirty = 1;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
    }
}
