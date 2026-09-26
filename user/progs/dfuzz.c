/* dfuzz: a fuzzer for the display server (user/display.c), from an open slot. test/dfuzz.sh
   puts it on a card of its own under several names and Terminal runs each into an open slot,
   where a program reaches only the display (endpoint 0, its capability 4), its own memory
   and its folder apps/NAME. The name picks what it does: dfuzz and dfuzz2 the whole run
   below, dfuzzx and dfuzzf the same until they exit or fault in the middle of it, dfuzzc
   copy and paste by the user's hand (clip_mode).

   The display owns the framebuffer and composites every window from memory the apps grant
   it. It is trusted user-space code that cannot be restarted: a crash freezes the machine.
   So it must answer every message, whatever its op, words and grant hold, with an answer
   the protocol (user/app.h) allows, never draw a program's pixels or words where the
   stacking rules do not put them, never keep what it does not use, never stop, never hang.
   dfuzz checks the answers from the one side a program can reach; test/dfuzz.sh checks the
   screen, the log and the kernel heap.

     0. If the seed file says "n": a window one pixel wide with a wide title, between two
        pauses, for the test's screenshots.
     1. Fixed cases, each with the answer the protocol allows. WAIT and POLL with no window,
        and with a grant. OPEN with sizes 0, huge and past 16 bits, too few pages, more pages
        than a window's slot, no grant, an endpoint as the grant (the kernel refuses it), and
        once: a window taller than the room between the menu bar and the dock, and one from
        the code run or the stack. ICON with a bad marker, a size past 64, no grant, more
        than its four pages. SET with every `what`, in and out of range (a card program may
        set nothing); START, RAISE and PENDING (a card program is not Apps); ZONE (anyone
        may ask: a quarter hour in range); COPY unasked; unknown ops; every op as a plain
        send with a grant, then a call that must still be answered. Once without a window,
        then again holding one.
     2. Requests near the display's limits: windows of sizes at and around its bounds from
        grants of 1 to 200 pages anywhere in the spare run, read-only or read-write, and
        icons with good and bad markers, sizes, names and page counts, each checked against
        the rule (on_open, on_icon): what it must refuse, refused. They open windows until
        the table is full.
     3. Floods: requests it cannot make, and windows that do not fit; the display must
        answer each and log a few.
     4. Random requests: each op with random words, a grant or none, a call or a plain send,
        every answer in the set the protocol allows. WAIT only before it has a window (with
        one, a WAIT with nothing to say is held by design); POLL, which never blocks, after.
     5. RAISE of its own name (given with a made-up icon), again and again; then windows
        until the display refuses one, some from runs another window already shows. Then it
        waits on its window, so the display still delivers its own events, and a screenshot
        has something to show.

   Every answer must come (the kernel status is OK) and be one the protocol allows. The
   seed is in its folder (seed, written by the test: "SEED [COUNT [n]]"), and printed, so a
   run can be replayed. Every line starts "dfuzz: NAME in slot N". */
#include "../app.h"
#include "../fs.h"
#include "../elf.h"

#define WIN_OFF 64          /* the window's pixels: spare-run page 128 (after the assets) */
#define WIN_W 80
#define WIN_H 50
#define WIN_PAGES 4         /* 80 x 50 x 4 = 16000 bytes, 4 pages */
#define ICON_OFF 160        /* four scratch pages for a made-up icon grant */
#define BIG_OFF 176         /* a run to grant when a window claims more pages than it has */
#define SHOWN 8             /* wrong answers described, at most */

struct df {
    struct fs_client fs;
    char name[16];
    u64 me, seed, rng, requests, wrong, shown, taken, t0;
    int have_win;           /* it has opened at least one real window */
};

/* ---- small things ---- */

static u64 next(struct df *f) {
    u64 x = f->rng;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return f->rng = x;
}

static void say(struct df *f, const char *what, u64 n, const char *rest) {
    struct line l = {.n = 0};
    put_s(&l, "dfuzz: ");
    put_s(&l, f->name);
    put_s(&l, " in slot ");
    put_dec(&l, f->me);
    put_s(&l, ": ");
    put_s(&l, what);
    if (rest) {
        put_dec(&l, n);
        put_s(&l, rest);
    }
    put_s(&l, "\n");
    flush(&l);
}

static const char *op_name(u64 op) {
    static const char *const names[] = {"op 0", "OPEN", "WAIT", "SET", "POLL", "ICON", "START",
                                        "RAISE", "PENDING", "ZONE", "COPY"};
    return op >= 1 && op <= 10 ? names[op] : "op 11+";
}

/* A wrong answer: counted, and the first few described. */
static void wrong(struct df *f, const char *what, u64 op, struct res r) {
    f->wrong++;
    if (f->shown++ >= SHOWN) return;
    struct line l = {.n = 0};
    put_s(&l, "dfuzz: ");
    put_s(&l, f->name);
    put_s(&l, ": WRONG: ");
    put_s(&l, what);
    put_s(&l, ", ");
    put_s(&l, op_name(op));
    put_s(&l, ": kernel ");
    put_dec(&l, r.status);
    put_s(&l, ", x1 ");
    put_dec(&l, r.x[1]);
    put_s(&l, " (");
    put_dec(&l, r.x[2]);
    put_s(&l, ", ");
    put_dec(&l, r.x[3]);
    put_s(&l, ")\n");
    flush(&l);
}

/* Every call to the display must come back with the kernel's OK: the message was carried,
   the display answered, it did not stop. */
static int answered(struct df *f, const char *what, u64 op, struct res r) {
    f->requests++;
    if (r.status != OK) {
        wrong(f, what, op, r);
        return 0;
    }
    return 1;
}

/* A call to the display, and its reply. */
static struct res dcall(struct df *f, u64 op, u64 w1, u64 w2, u64 grant) {
    return sys(SYS_CALL, ENDPOINT, op, w1, w2, grant);
}

/* A read-only capability to `count` pages of the spare run from `off`, granted to a call. */
static struct res grant_call(struct df *f, u64 op, u64 w1, u64 w2, u64 off, u64 count, u64 rights) {
    struct res d = sys(SYS_DERIVE, SPARE, rights, off, count, 0);
    if (d.status != OK) return d;
    struct res r = dcall(f, op, w1, w2, d.x[1] + 1);
    sys1(SYS_DROP, d.x[1]);        /* the display kept its own copy if it took one */
    return r;
}

/* Assert the reply's x1 is one of an allowed pair (b < 0: only a). */
static void want1(struct df *f, const char *what, u64 op, struct res r, int a, int b) {
    if (!answered(f, what, op, r)) return;
    if ((int)r.x[1] != a && (b < 0 || (int)r.x[1] != b)) wrong(f, what, op, r);
}

/* ---- the window and the icon ---- */

static void paint(u64 off, int w, int h, unsigned color) {
    unsigned *px = (unsigned *)PAGE(SPARE_PAGE + off);
    for (int i = 0; i < w * h; i++) px[i] = color;
}

/* Open a WIN_W x WIN_H window from the spare run at `off`. OK if the display took it. */
static u64 open_win(struct df *f, u64 off, unsigned color) {
    paint(off, WIN_W, WIN_H, color);
    struct res r = grant_call(f, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0x7a75666420UL /* " dfuz" */,
                              off, WIN_PAGES, R);
    if (!answered(f, "open a window", OP_OPEN, r)) return BAD_ARG;
    return r.x[1] == 0 ? OK : BAD_ARG;
}

/* Lay a made-up icon (a marker, a size, then pixels, a name at the end) in the scratch
   pages, so ICON can be handed a well-formed or a broken one. */
static void make_icon(u64 off, unsigned magic, unsigned size, unsigned w, unsigned h, const char *name) {
    unsigned *m = (unsigned *)PAGE(SPARE_PAGE + off);
    for (u64 i = 0; i < 4 * 1024; i++) m[i] = 0;
    m[0] = magic;
    m[1] = size;
    m[2] = w;
    m[3] = h;
    u64 pixels = (u64)w * h;
    if (pixels > 4 * 1024 - 8) pixels = 4 * 1024 - 8;    /* never past the four scratch pages */
    for (u64 i = 0; i < pixels; i++) m[4 + i] = 0xff4080c0;
    unsigned char *nm = (unsigned char *)m + 4 * 4096 - 16;
    for (int i = 0; i < 16; i++) nm[i] = 0;
    for (int i = 0; name && name[i] && i < 15; i++) nm[i] = (unsigned char)name[i];
}

/* ---- 1. fixed adversarial cases ---- */

/* The requests the display refuses whether or not the program has a window. */
static void fixed(struct df *f, const char *when) {
    /* OPEN: bad sizes, with a grant big enough to never be the reason it is refused. */
    want1(f, "open 0x0", OP_OPEN, grant_call(f, OP_OPEN, 0, 0, WIN_OFF, WIN_PAGES, R), 1, -1);
    want1(f, "open huge", OP_OPEN,
          grant_call(f, OP_OPEN, (u64)2000 << 16 | 1000, 0, WIN_OFF, WIN_PAGES, R), 1, -1);
    /* w in the high word past 16 bits, so w * h * 4 is enormous: still refused, no overflow. */
    want1(f, "open w huge", OP_OPEN,
          grant_call(f, OP_OPEN, (u64)0x7fffff << 16 | 480, 0, WIN_OFF, WIN_PAGES, R), 1, -1);
    /* the size does not match the granted pages: a large window, a one-page grant. */
    want1(f, "open too few pages", OP_OPEN,
          grant_call(f, OP_OPEN, (u64)300 << 16 | 200, 0, WIN_OFF, 1, R), 1, -1);
    /* a window bigger than any: 900 x 480 needs 422 pages, past WIN_MAX_PAGES. */
    want1(f, "open past the table", OP_OPEN,
          grant_call(f, OP_OPEN, (u64)900 << 16 | 480, 0, BIG_OFF, 40, R), 1, -1);
    /* OPEN with no grant at all: the display cannot make a window from nothing. */
    want1(f, "open no grant", OP_OPEN, dcall(f, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0, 0), 1, -1);
    /* A small window, but a grant of far more pages than a window's slot holds. The display
       maps the whole granted run at the window's slot, so a grant past WIN_MAX_PAGES (184)
       would overrun into the next window's slot and draw this program's pixels there. It
       must refuse a grant with more pages than a window may use. */
    want1(f, "open with an over-large grant", OP_OPEN,
          grant_call(f, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0, 0, 200, R), 1, -1);
    /* A window as tall as allowed (480): there is less room than that between the menu bar
       and the dock, and the display must still keep it below the menu bar (as a drag does),
       never put its title bar, with a title the program chose, over the menu bar. The screen
       check in test/dfuzz.sh sees where it went. */
    int first = !f->have_win;           /* the cases that take a window: once, not per pass */
    if (first) {
        paint(BIG_OFF, 80, 480, 0x6040a0);
        want1(f, "open a window taller than the room", OP_OPEN,
              grant_call(f, OP_OPEN, (u64)80 << 16 | 480, 0x6c6c6174 /* "tall" */, BIG_OFF, 38, R), 0, 1);
    }
    /* a grant of the code run (read + execute): frames all the same; the display draws the
       program's own code as pixels, which is only its own memory. It must not stop. */
    paint(WIN_OFF, WIN_W, WIN_H, 0x203040);
    if (first) {
        /* the code run from an even slot, the stack (capability 2, four pages) from an odd one */
        struct res d = sys(SYS_DERIVE, f->me % 2 ? 2 : 0, R, 0, WIN_PAGES, 0);
        if (d.status == OK) {
            struct res r = dcall(f, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0, d.x[1] + 1);
            /* success or refusal both allowed; if it opened, the window stays (its own memory). */
            want1(f, f->me % 2 ? "open from the stack" : "open from the code run", OP_OPEN, r, 0, 1);
            sys1(SYS_DROP, d.x[1]);
        }
    }
    /* its endpoint capability as the grant: not memory, so the kernel refuses to send it, and
       the display never sees it */
    {
        struct res r = dcall(f, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0, ENDPOINT + 1);
        f->requests++;
        if (r.status != BAD_ARG) wrong(f, "an endpoint granted", OP_OPEN, r);
    }

    /* ICON: a bad marker, a bad size, a good one to no matching state. */
    make_icon(ICON_OFF, 0xdeadbeef, 1, 16, 16, f->name);
    want1(f, "icon bad marker", OP_ICON, grant_call(f, OP_ICON, 0, 0, ICON_OFF, 4, R), 1, -1);
    make_icon(ICON_OFF, 0x43494e4cu, 1, 200, 200, f->name);   /* w, h past 64: a name only */
    want1(f, "icon huge size", OP_ICON, grant_call(f, OP_ICON, 0, 0, ICON_OFF, 4, R), 0, 1);
    want1(f, "icon no grant", OP_ICON, dcall(f, OP_ICON, 0, 0, 0), 1, -1);
    /* An icon lives in four pages (a marker, a size, the pixels, a name). A grant of more
       than four pages, mapped at the window's four-page icon slot, would overrun into the
       next window's icon slot. With a window in front and a well-formed icon, the display
       must still refuse a grant that is not four pages. */
    make_icon(ICON_OFF, 0x43494e4cu, 1, 16, 16, f->name);
    want1(f, "icon with an over-large grant", OP_ICON,
          grant_call(f, OP_ICON, 0, 0, ICON_OFF, 8, R), 1, -1);

    /* SET: a card program may change nothing. Every what, in and out of range. */
    want1(f, "set background", OP_SET, dcall(f, OP_SET, 1 /* SET_BACKGROUND */, 0, 0), 1, -1);
    want1(f, "set background oob", OP_SET, dcall(f, OP_SET, 1, 99, 0), 1, -1);
    want1(f, "set zone", OP_SET, dcall(f, OP_SET, 2 /* SET_ZONE */, 720, 0), 1, -1);
    want1(f, "set zone oob", OP_SET, dcall(f, OP_SET, 2, ~0UL, 0), 1, -1);
    want1(f, "set unknown what", OP_SET, dcall(f, OP_SET, 99, 0, 0), 1, -1);

    /* START, RAISE, PENDING: a card program is not Apps. START must be refused; RAISE with a
       made-up name finds nothing (1); PENDING answers 0 with no name. */
    want1(f, "start", OP_START, dcall(f, OP_START, 0, 0, 0), 1, -1);
    want1(f, "start oob", OP_START, dcall(f, OP_START, 99, 0, 0), 1, -1);
    want1(f, "raise nothing", OP_RAISE, dcall(f, OP_RAISE, 0x6f6f666162, 0x7a, 0), 1, -1);
    want1(f, "pending", OP_PENDING, dcall(f, OP_PENDING, 0, 0, 0), 0, -1);

    /* ZONE: anyone may ask. The answer is a quarter hour between -12:00 and +14:00, biased. */
    {
        struct res r = dcall(f, OP_ZONE, 0, 0, 0);
        if (answered(f, "zone", OP_ZONE, r)) {
            long m = (long)r.x[2] - 12 * 60;
            if (r.x[1] != 0 || r.x[2] > 26 * 60 || m < -12 * 60 || m > 14 * 60 || m % 15)
                wrong(f, "zone out of range", OP_ZONE, r);
        }
    }

    /* COPY nobody asked for: refused. */
    want1(f, "copy unasked", OP_COPY, dcall(f, OP_COPY, 0x4141414141414141UL, 0, 0), 1, -1);

    /* Unknown op numbers. */
    want1(f, "op 0", 0, dcall(f, 0, 0, 0, 0), 1, -1);
    want1(f, "op 11", 11, dcall(f, 11, 0, 0, 0), 1, -1);
    want1(f, "op big", 0x7ff, dcall(f, 0x7ff, next(f), next(f), 0), 1, -1);

    /* Grants by plain send, nobody asked for: the display must let go of every one, or its
       64 capabilities fill and it can take no more (test/chaos.sh tests the same for
       plain sends; here every op, call and send). */
    for (u64 op = 0; op <= 12; op++) {
        struct res d = sys(SYS_DERIVE, SPARE, R, WIN_OFF, WIN_PAGES, 0);
        if (d.status == OK) {
            sys(SYS_SEND, ENDPOINT, op, next(f), next(f), d.x[1] + 1);
            sys1(SYS_DROP, d.x[1]);
        }
    }
    /* After the plain sends the display must still answer a call. */
    want1(f, "alive after plain grants", OP_ZONE, dcall(f, OP_ZONE, 0, 0, 0), 0, -1);

    say(f, when, f->requests, " requests so far, checked");
}

/* WAIT and POLL with no window (only safe before a window is open: WAIT with a window and
   nothing to say blocks by design). Both answer EV_NONE. */
static void wait_no_window(struct df *f) {
    want1(f, "wait, no window", OP_WAIT, dcall(f, OP_WAIT, 0, 0, 0), EV_NONE, -1);
    want1(f, "wait dirty, no window", OP_WAIT, dcall(f, OP_WAIT, 1, 0, 0), EV_NONE, -1);
    want1(f, "poll, no window", OP_POLL, dcall(f, OP_POLL, 0, 0, 0), EV_NONE, -1);
    /* WAIT with a grant and no window: the grant is dropped, the answer is EV_NONE. */
    want1(f, "wait with a grant", OP_WAIT,
          grant_call(f, OP_WAIT, 0, 0, WIN_OFF, WIN_PAGES, R), EV_NONE, -1);
}

/* ---- 3. random requests ---- */

/* The answer x1 the protocol allows for op, as a set this checks against. Returns 1 if x1
   is allowed. */
static int reply_ok(struct df *f, u64 op, int have_win, struct res r) {
    u64 x = r.x[1];
    switch (op) {
    case OP_OPEN: return x == 0 || x == 1;                 /* took it, or refused */
    case OP_WAIT:
    case OP_POLL: return x <= 8;                           /* EV_NONE .. EV_PASTE */
    case OP_SET: return x == 0 || x == 1;
    case OP_ICON: return x == 0 || x == 1;
    case OP_START: return x == 0 || x == 1;
    case OP_RAISE: return x == 0 || x == 1;
    case OP_PENDING: return x == 0;                        /* not Apps: 0, no name */
    case OP_ZONE: return x == 0 && r.x[2] <= 26 * 60;
    case OP_COPY: return x == 0 || x == 1;
    default: return x == 1;                                /* unknown op */
    }
    (void)f; (void)have_win;
}

/* A window or an icon made to sit near the display's limits, with the answer the rule
   (user/display.c: on_open, on_icon) demands when it must refuse: a window needs 1 to 900 by
   1 to 480 pixels, a grant of at least its pages and at most a window's slot (184 pages); an
   icon exactly its four pages and the marker. When the rule allows it, the display may still
   refuse (its table of 12 windows may be full, the window may have its icon): 0 or 1. */
static void structured(struct df *f) {
    static const u64 ws[] = {0, 1, 2, 80, 479, 480, 481, 899, 900, 901, 1024, 65535};
    u64 w = ws[next(f) % 12], h = ws[next(f) % 12];
    if (next(f) & 1) { w = next(f) % 1000; h = next(f) % 600; }
    u64 pages = 1 + next(f) % 200;
    u64 off = next(f) % (224 - pages + 1);        /* anywhere in the spare run below the file buffer */
    u64 rights = next(f) % 4 ? R : R | W;         /* read-only, as apps lend it, or read-write */
    if (next(f) % 3) {
        u64 need = (w * h * 4 + 4095) / 4096;
        int allowed = w >= 1 && w <= 900 && h >= 1 && h <= 480 && pages >= need && pages <= 184;
        struct res r = grant_call(f, OP_OPEN, w << 16 | h, next(f), off, pages, rights);
        if (answered(f, "structured open", OP_OPEN, r) && (r.x[1] > 1 || (!allowed && r.x[1] != 1)))
            wrong(f, allowed ? "structured open, allowed" : "structured open the rule refuses", OP_OPEN, r);
        if (r.status == OK && r.x[1] == 0) { f->have_win = 1; f->taken++; }
    } else {
        int good = next(f) % 4 != 0;
        unsigned iw = (unsigned)(next(f) % 80), ih = (unsigned)(next(f) % 80);
        char name[16];
        for (int i = 0; i < 15; i++) name[i] = (char)(next(f) % 4 ? 'a' + next(f) % 26 : next(f) % 256);
        name[next(f) % 16] = 0;
        name[15] = 0;
        u64 ipages = next(f) % 3 ? 4 : 1 + next(f) % 12;
        make_icon(ICON_OFF, good ? 0x43494e4cu : (unsigned)next(f), (unsigned)(next(f) % 3), iw, ih, name);
        struct res r = grant_call(f, OP_ICON, 0, 0, ICON_OFF, ipages, R);
        int must_refuse = !good || ipages != 4;
        if (answered(f, "structured icon", OP_ICON, r) && (r.x[1] > 1 || (must_refuse && r.x[1] != 1)))
            wrong(f, must_refuse ? "structured icon the rule refuses" : "structured icon", OP_ICON, r);
    }
}

static void random_run(struct df *f, u64 count) {
    for (u64 i = 0; i < count; i++) {
        u64 op = next(f) % 13;                 /* 0..12: the ops and a couple past them */
        if (f->have_win && op == OP_WAIT) op = OP_POLL;   /* a WAIT with a window may block */
        u64 w1 = next(f), w2 = next(f);
        int use_grant = next(f) & 1;
        int as_call = op != OP_WAIT ? (next(f) & 1) : 1;  /* WAIT (no window) as a call */
        u64 grant = 0, gi = 0;
        if (use_grant) {
            u64 off = WIN_OFF + (next(f) % 8) * WIN_PAGES;
            u64 cnt = 1 + next(f) % WIN_PAGES;
            struct res d = sys(SYS_DERIVE, SPARE, R, off, cnt, 0);
            if (d.status == OK) { gi = d.x[1]; grant = gi + 1; }
        }
        if (as_call) {
            struct res r = dcall(f, op, w1, w2, grant);
            if (answered(f, "random", op, r) && !reply_ok(f, op, f->have_win, r))
                wrong(f, "random reply out of range", op, r);
        } else {
            /* a plain send wants no answer; the display must not block or keep the grant */
            sys(SYS_SEND, ENDPOINT, op, w1, w2, grant);
            f->requests++;
        }
        if (grant) sys1(SYS_DROP, gi);
    }
}

/* ---- 4. the window limit ---- */

static void window_limit(struct df *f) {
    u64 opened = 0;
    int refused = 0;
    for (u64 k = 0; k < 14; k++) {
        u64 off = WIN_OFF + (k % 8) * WIN_PAGES;
        u64 r = open_win(f, off, 0x28607a + (unsigned)k * 0x101);
        if (r == OK) opened++;
        else { refused = 1; break; }
    }
    if (opened) f->have_win = 1;    /* it already had one from before, too */
    if (!refused && opened) {
        /* the table did not fill from this slot alone; that is fine (others hold windows) */
        say(f, "opened ", opened, " windows, the table not yet full from this slot");
    } else {
        say(f, "opened ", opened, " windows, then the display refused one");
    }
}

/* ---- dfuzzc: copy and paste, by the user's hand ----

   One window, and the user (test/dfuzz.sh) presses Ctrl+C, Ctrl+V, Ctrl+C and the close
   button. The first copy is answered with 4800 bytes, 16 to a call: the display takes them
   up to its 4096 and refuses every call after the copy ended. The paste must bring back
   exactly the 4096 bytes. The second copy is answered 2.5 s late: refused. After the close
   button, a copy nobody asked for: refused. */
static char pattern(u64 i) { return (char)('a' + i % 26); }

static void clip_mode(struct df *f) {
    f->have_win = open_win(f, WIN_OFF, 0x40a060) == OK;
    say(f, "copy and paste: window ", (u64)f->have_win, "");
    int copies = 0;
    u64 got = 0, bad = 0;
    for (;;) {
        struct event e = app_wait(0);
        if (e.kind == EV_COPY && copies++ == 0) {
            u64 sent = 0, refused = 0;
            for (int c = 0; c < 300; c++, sent += 16) {
                u64 w[2] = {0, 0};
                for (int k = 0; k < 16; k++) w[k / 8] |= (u64)(unsigned char)pattern(sent + (u64)k) << (8 * (k % 8));
                struct res r = dcall(f, OP_COPY, w[0], w[1], 0);
                if (!answered(f, "copy", OP_COPY, r)) continue;
                if (r.x[1] != (sent < CLIP_MAX ? 0UL : 1UL)) wrong(f, "copy past the clipboard's size", OP_COPY, r);
                refused += r.x[1] == 1;
            }
            say(f, "copy: sent 4800 bytes; the calls past 4096 refused: ", refused, "");
        } else if (e.kind == EV_COPY) {
            sleep_ms(COPY_MS + 500);
            want1(f, "a copy answered late", OP_COPY, dcall(f, OP_COPY, 0x4c4c, 0, 0), 1, -1);
            say(f, "copy: a late answer refused", 0, 0);
        } else if (e.kind == EV_PASTE) {
            char t[16];
            int n = paste_text(e, t);
            for (int i = 0; i < n; i++) bad += t[i] != pattern(got + (u64)i);
            got += (u64)n;
            if (n < 16) say(f, "paste: got ", got, bad ? " bytes, NOT as copied" : " bytes, as copied");
            if (n < 16 && (bad || got != CLIP_MAX)) f->wrong++;
        } else if (e.kind == EV_CLOSE) {
            want1(f, "a copy after the window closed", OP_COPY, dcall(f, OP_COPY, 0x5a5a, 0, 0), 1, -1);
            struct line l = {.n = 0};
            put_s(&l, "dfuzz: ");
            put_s(&l, f->name);
            put_s(&l, " in slot ");
            put_dec(&l, f->me);
            put_s(&l, ": closed; all done: ");
            put_dec(&l, f->requests);
            put_s(&l, " requests, ");
            put_dec(&l, f->wrong);
            put_s(&l, " wrong\n");
            flush(&l);
            exit_task();
        }
    }
}

__attribute__((section(".text.start"))) void _start(void) {
    struct df *f = (struct df *)DATA;
    memset(f, 0, sizeof *f);
    app_assets();
    fs_init(&f->fs, SPARE_PAGE);
    f->me = sys0(SYS_WHOAMI).x[1];

    /* the name it was run as: the loader wrote it at the end of the icon pages */
    const volatile unsigned char *at = (const volatile unsigned char *)PAGE(ICON_IMAGE_PAGE);
    f->name[0] = '?';
    f->name[1] = 0;
    if (*(const volatile unsigned *)at == ICON_MAGIC)
        for (int i = 0; i < 16; i++) f->name[i] = i < 15 ? (char)at[ICON_NAME_AT + i] : 0;

    /* the seed, from its folder (the test wrote "SEED [COUNT]"), or a default */
    char path[32], seedbuf[32];
    int n = 0;
    const char *pre = "apps/";
    for (int i = 0; pre[i]; i++) path[n++] = pre[i];
    for (int i = 0; f->name[i]; i++) path[n++] = f->name[i];
    const char *sf = "/seed";
    for (int i = 0; sf[i]; i++) path[n++] = sf[i];
    path[n] = 0;
    u64 seed = 0, rcount = 4000;
    int narrow = 0;                       /* "SEED COUNT n": first, a window one pixel wide */
    long got = fs_read_all(&f->fs, path, seedbuf, sizeof seedbuf - 1);
    if (got > 0) {
        seedbuf[got] = 0;
        int i = 0;
        while (seedbuf[i] >= '0' && seedbuf[i] <= '9') seed = seed * 10 + (u64)(seedbuf[i++] - '0');
        if (seedbuf[i] == ' ') {
            i++;
            u64 c = 0;
            while (seedbuf[i] >= '0' && seedbuf[i] <= '9') c = c * 10 + (u64)(seedbuf[i++] - '0');
            if (c) rcount = c;
            narrow = seedbuf[i] == ' ' && seedbuf[i + 1] == 'n';
        }
    }
    if (!seed) seed = 0x9e3779b97f4a7c15UL ^ (f->me * 2654435761UL);
    f->seed = seed;
    f->rng = seed ? seed : 1;
    say(f, "seed ", f->seed, "");

    /* 1. fixed cases with no window, and WAIT/POLL with no window */
    wait_no_window(f);
    int len = 0;
    while (f->name[len]) len++;
    if (len && f->name[len - 1] == 'c') clip_mode(f);

    /* A window one pixel wide, with a wide title: the display must draw its title bar, its
       buttons and its title only inside its frame, never over what lies beside it (clicks
       there go to the window below). test/dfuzz.sh compares the screen before and after. */
    if (narrow) {
        say(f, "about to open a narrow window", 0, 0);
        sleep_ms(800);
        paint(WIN_OFF, 1, 40, 0x20c0f0);
        want1(f, "open a window one pixel wide", OP_OPEN,
              grant_call(f, OP_OPEN, (u64)1 << 16 | 40, 0x5757575757575757UL /* "WWWWWWWW" */, WIN_OFF, 1, R), 0, -1);
        say(f, "a narrow window is up", 0, 0);
        sleep_ms(800);
    }
    fixed(f, "no window: ");

    /* open one window, then the fixed cases again (a window in the way) */
    f->have_win = open_win(f, WIN_OFF, 0x3a6ee6 + (unsigned)f->me) == OK;
    fixed(f, "with a window: ");

    /* dfuzzx and dfuzzf end here, in the middle of an exchange: grants sent by plain send,
       nobody asked for, then an exit, or a fault (a write to its own code). The display must
       drop what they lent and forget their windows before the slot starts again. */
    char last = len ? f->name[len - 1] : 0;
    if (last == 'x' || last == 'f') {
        for (int i = 0; i < 20; i++) {
            struct res d = sys(SYS_DERIVE, SPARE, R, WIN_OFF, WIN_PAGES, 0);
            if (d.status == OK) {
                sys(SYS_SEND, ENDPOINT, i % 2 ? OP_POLL : OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0, d.x[1] + 1);
                sys1(SYS_DROP, d.x[1]);
            }
        }
        say(f, last == 'x' ? "exiting after " : "faulting after ", f->requests, " requests, 0 wrong so far");
        if (f->wrong) say(f, "WRONG answers: ", f->wrong, "");
        if (last == 'f') *(volatile u64 *)PAGE(0) = 1;   /* its own code: not writable */
        exit_task();
    }

    /* A moment: a new window takes the focus, and the test may still be typing into
       Terminal to start the next dfuzz. Then requests made near the display's limits, which
       open windows until its table is full. */
    sleep_ms(1500);
    f->t0 = millis();
    for (u64 i = 0; i < rcount / 4 + 1; i++) structured(f);
    say(f, "near the limits: windows taken ", f->taken, ", checked");
    say(f, "near the limits took ", millis() - f->t0, " ms");
    f->t0 = millis();

    /* 2. floods the display must answer and quiet: requests it cannot make, and windows it
       refuses (each refusal it logs holds the kernel while the serial port takes the line) */
    for (int i = 0; i < 200; i++) dcall(f, 0x555, next(f), next(f), 0);
    f->requests += 200;
    for (int i = 0; i < 100; i++)
        want1(f, "a flood of windows that do not fit", OP_OPEN,
              grant_call(f, OP_OPEN, 0, 0, WIN_OFF, WIN_PAGES, R), 1, -1);
    want1(f, "alive after the flood", OP_ZONE, dcall(f, OP_ZONE, 0, 0, 0), 0, -1);

    /* 3. random requests (they open no window, in practice: random sizes are never that small) */
    say(f, "random requests start", 0, 0);
    random_run(f, rcount);

    /* the display still answers after the random run */
    want1(f, "alive after random", OP_ZONE, dcall(f, OP_ZONE, 0, 0, 0), 0, -1);

    say(f, "floods and random requests took ", millis() - f->t0, " ms");
    /* 4. the window limit */
    /* RAISE of its own name, over and over: the name came with its made-up icon (ICON with a
       name only). Each is answered (0: brought forward); the display logs a few, not all. */
    u64 nm[2] = {0, 0};
    for (int i = 0; i < 15 && f->name[i]; i++) nm[i / 8] |= (u64)(unsigned char)f->name[i] << (8 * (i % 8));
    for (int i = 0; i < 100; i++) want1(f, "raise its own name", OP_RAISE, dcall(f, OP_RAISE, nm[0], nm[1], 0), 0, 1);
    window_limit(f);

    struct line l = {.n = 0};
    put_s(&l, "dfuzz: ");
    put_s(&l, f->name);
    put_s(&l, " in slot ");
    put_dec(&l, f->me);
    put_s(&l, ": all done: ");
    put_dec(&l, f->requests);
    put_s(&l, " requests, ");
    put_dec(&l, f->wrong);
    put_s(&l, " wrong\n");
    flush(&l);

    /* hold a window and hear its close button, so a screenshot has something to show and
       the display keeps delivering this program's own events */
    for (;;) {
        if (!f->have_win) { sleep_ms(1000); continue; }
        struct event e = app_wait(0);
        if (e.kind == EV_CLOSE) exit_task();
    }
}
