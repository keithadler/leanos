/* chaos: a test program that pushes the trusted base (the runtime's allocator and freeing,
   the machine layer's tables and kernel lock) to the limits the proofs allow, from an open
   slot. test/chaos.sh puts it on a card of its own under several names, and what it does
   depends on the name it was run as (Terminal writes it into the image, beside the icon):

     hog    every per-task limit at once: a 16 KiB file written and read back through the
            file server, a window, 100 calls to the display that grant it the whole spare
            run, all 8192 pages of its window mapped (and each one read), capabilities
            derived until the kernel says full (64), sleeps. Then it waits for its window's
            next event, a call the display holds until then, until it is stopped.
    hogx    the same, then exits.
    hogf    the same, then writes to its own code, which stops it (a fault).
    busy    never waits for long: rounds of capabilities derived, mapped (each map rebuilds
            its level-3 table, the kernel's largest object), unmapped and dropped, calls and
            plain sends to the display that grant it the spare run, and every 16th round a
            file written and read back; several at once keep all four cores in the kernel.
    files   file rounds only, back to back: the file server's queue always full.
    pest    100 plain sends (no reply wanted) to the file server and 100 to the display,
            each granting its spare run, then a file round: a server must let go of every
            grant it does not keep, or its 64 capabilities fill and it can take no request
            that carries one, which is every file request.
    wins    opens small windows until the display refuses one, then waits.
    nap     sleeps, a second at a time.

   Every line it prints starts "chaos: NAME in slot N". What it checks itself (a file that
   reads back different, a limit the kernel does not keep) it counts as a surprise. */
#include "../ui.h"
#include "../fs.h"
#include "../elf.h"

#define WIN_W 60
#define WIN_H 40
#define WIN_PAGES 3              /* 60 x 40 x 4 bytes */
#define SPARE_RUN 228
#define STACK_FIRST 8188         /* the stack's four pages, left as they are */
#define CHURN_PAGE 400           /* where busy maps and unmaps its pieces */

enum { HOG, HOGX, HOGF, BUSY, FILES, PEST, WINS, NAP, UNKNOWN };
static const char *const mode_names[] = {"hog", "hogx", "hogf", "busy", "files", "pest", "wins", "nap"};

struct chaos {
    struct fs_client fs;
    char name[16];
    char path[64];
    int mode;
    u64 me, surprises, windows, grants, caps, rounds;
};

static void say(struct chaos *c, const char *what, u64 n, const char *rest) {
    struct line l = {.n = 0};
    put_s(&l, "chaos: ");
    put_s(&l, c->name);
    put_s(&l, " in slot ");
    put_dec(&l, c->me);
    put_s(&l, ": ");
    put_s(&l, what);
    if (rest) {
        put_dec(&l, n);
        put_s(&l, rest);
    }
    put_s(&l, "\n");
    flush(&l);
}

static int same(const char *a, const char *b) {
    while (*a && *a == *b) a++, b++;
    return *a == *b;
}

/* Which name it was run as: Terminal puts the card file's name into the image, at the end
   of the icon's pages (user/elf.h), so it needs nobody's answer. */
static void find_name(struct chaos *c) {
    const volatile unsigned char *at = (const volatile unsigned char *)PAGE(ICON_IMAGE_PAGE);
    c->mode = UNKNOWN;
    c->name[0] = '?';
    c->name[1] = 0;
    if (*(const volatile unsigned *)at == ICON_MAGIC)
        for (int i = 0; i < 16; i++) c->name[i] = i < 15 ? (char)at[ICON_NAME_AT + i] : 0;
    for (int m = 0; m < UNKNOWN; m++)
        if (same(c->name, mode_names[m])) c->mode = m;
}

/* A window of WIN_W x WIN_H from the spare run's pages at `offset` (read-only to the
   display). OK if the display took it. No icon: the display then never takes it for a
   program already open, so the same program can run in several slots. */
static u64 open_window(u64 offset, unsigned color) {
    unsigned *px = (unsigned *)PAGE(SPARE_PAGE + offset);
    for (int i = 0; i < WIN_W * WIN_H; i++) px[i] = color;
    struct res ro = sys(SYS_DERIVE, SPARE, R, offset, WIN_PAGES, 0);
    if (ro.status != OK) return ro.status;
    struct res r = sys(SYS_CALL, ENDPOINT, OP_OPEN, (u64)WIN_W << 16 | WIN_H, 0x736f616863UL /* "chaos" */,
                       ro.x[1] + 1);
    sys1(SYS_DROP, ro.x[1]);     /* the display holds its own copy, if it took it */
    return r.status == OK && r.x[1] == 0 ? OK : BAD_ARG;
}

/* Write a file of FS_CHUNK bytes and read it back. 1 if it came back the same. */
static int file_round(struct chaos *c, u64 salt) {
    char *d = c->fs.buf + FS_DATA_OFF;
    for (u64 i = 0; i < FS_CHUNK; i++) d[i] = (char)(i * 7 + salt * 13 + c->me);
    fs_path(&c->fs, c->path);
    if (fs_call(&c->fs, FS_WRITE, FS_CHUNK).x[1] != FS_OK) return 0;
    for (u64 i = 0; i < FS_CHUNK; i++) d[i] = 0;
    if (fs_read(&c->fs, c->path) != (long)FS_CHUNK) return 0;
    for (u64 i = 0; i < FS_CHUNK; i++)
        if (d[i] != (char)(i * 7 + salt * 13 + c->me)) return 0;
    return 1;
}

static u64 ncaps(void) {
    u64 n = 0;
    while (sys1(SYS_CAPINFO, n).status == OK) n++;
    return n;
}

/* Every limit a task has, at once. */
static void hog(struct chaos *c) {
    if (!file_round(c, 1)) c->surprises++;
    c->windows = open_window(APP_WIN_OFFSET, 0x3a6ee6 + c->me) == OK;
    /* Grants: the display drops a capability that does not become a window. */
    for (int i = 0; i < 100; i++)
        c->grants += sys(SYS_CALL, ENDPOINT, OP_POLL, 0, 0, SPARE + 1).status == OK;
    /* All 8192 pages: copies of the spare run from page 24 up, a piece of it for the gap
       below the stack, then the spare run once more where the program keeps it. */
    u64 v = 24;
    for (; v + SPARE_RUN <= STACK_FIRST; v += SPARE_RUN)
        c->surprises += sys2(SYS_MAP, SPARE, v).status != OK;
    struct res piece = sys(SYS_DERIVE, SPARE, R | W, 0, STACK_FIRST - v, 0);
    c->surprises += piece.status != OK || sys2(SYS_MAP, piece.x[1], v).status != OK;
    c->surprises += sys2(SYS_MAP, SPARE, SPARE_PAGE).status != OK;
    for (u64 p = 0; p < 8192; p++) (void)*(volatile unsigned char *)PAGE(p);   /* else a fault */
    /* Capabilities until the kernel refuses: exactly 64, and the 65th is "full". */
    struct res d;
    while ((d = sys(SYS_DERIVE, SPARE, R, 0, 1, 0)).status == OK) {}
    c->caps = ncaps();
    c->surprises += d.status != FULL || c->caps != 64;
    /* No receive right on any endpoint: a receive with a timeout is refused. */
    c->surprises += sys(SYS_RECVT, ENDPOINT, 10, 0, 0, 0).status != BAD_ARG;
    for (int i = 0; i < 3; i++) sleep_ms(10);
    /* The file server still answers with every capability slot taken (its buffer's is kept). */
    if (!file_round(c, 2)) c->surprises++;
    struct line l = {.n = 0};
    put_s(&l, "chaos: ");
    put_s(&l, c->name);
    put_s(&l, " in slot ");
    put_dec(&l, c->me);
    put_s(&l, ": ");
    put_dec(&l, c->caps);
    put_s(&l, " capabilities, 8192 pages mapped, ");
    put_s(&l, c->windows ? "a window, " : "no window, ");
    put_dec(&l, c->grants);
    put_s(&l, " grants to the display, ");
    put_dec(&l, c->surprises);
    put_s(&l, " surprises\n");
    flush(&l);
}

/* Wait on its window for good (the display holds the call), or sleep if it has none. */
static void wait_forever(struct chaos *c) {
    for (;;) {
        if (!c->windows) { sleep_ms(1000); continue; }
        struct event e = app_wait(0);
        if (e.kind == EV_CLOSE) exit_task();
    }
}

static void busy(struct chaos *c) {
    c->windows = open_window(APP_WIN_OFFSET, 0xe0483e + c->me) == OK;
    if (!file_round(c, 0)) c->surprises++;          /* its buffer's capability comes first */
    u64 first = ncaps();
    for (c->rounds = 1;; c->rounds++) {
        for (u64 i = 0; i < 16; i++) {
            struct res d = sys(SYS_DERIVE, SPARE, R | W, i, 1, 0);
            if (d.status != OK || sys2(SYS_MAP, d.x[1], CHURN_PAGE + i).status != OK) { c->surprises++; break; }
            (void)*(volatile unsigned char *)PAGE(CHURN_PAGE + i);
        }
        sys2(SYS_UNMAP, CHURN_PAGE, 16);
        while (sys1(SYS_DROP, first).status == OK) {}
        for (int i = 0; i < 4; i++) sys(SYS_CALL, ENDPOINT, OP_POLL, 0, 0, SPARE + 1);
        sys(SYS_SEND, ENDPOINT, 0x7ff, c->rounds, 0, SPARE + 1);     /* a request it cannot make */
        sys0(SYS_YIELD);
        if (c->rounds % 16) continue;
        if (!file_round(c, c->rounds)) c->surprises++;
        say(c, "", c->rounds, c->surprises ? " rounds, SURPRISED" : " rounds, 0 surprises");
    }
}

/* The file server and nothing else, as fast as it answers. */
static void files(struct chaos *c) {
    for (c->rounds = 1;; c->rounds++) {
        if (!file_round(c, c->rounds)) c->surprises++;
        if (c->rounds % 4 == 0) say(c, "", c->rounds, c->surprises ? " rounds, SURPRISED" : " rounds, 0 surprises");
    }
}

/* Grants nobody asked for, by plain send, then a request that needs the file server. */
static void pest(struct chaos *c) {
    u64 fs = 0, display = 0;
    for (int i = 0; i < 100; i++) {
        fs += sys(SYS_SEND, FS_ENDPOINT, FS_STAT, 0, 0, SPARE + 1).status == OK;
        display += sys(SYS_SEND, ENDPOINT, 0x7ff, 0, 0, SPARE + 1).status == OK;
    }
    int files_ok = file_round(c, 3);
    struct line l = {.n = 0};
    put_s(&l, "chaos: pest in slot ");
    put_dec(&l, c->me);
    put_s(&l, ": 100 grants sent to the file server, ");
    put_dec(&l, fs);
    put_s(&l, " taken; 100 to the display, ");
    put_dec(&l, display);
    put_s(&l, files_ok ? " taken; its file still reads back\n" : " taken; its file DID NOT read back\n");
    flush(&l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct chaos *c = (struct chaos *)DATA;
    memset(c, 0, sizeof *c);
    app_assets();                /* the spare run at SPARE_PAGE: pixels and the file buffer */
    fs_init(&c->fs, SPARE_PAGE);
    c->me = sys0(SYS_WHOAMI).x[1];
    find_name(c);
    const char *prefix = "apps/";
    int n = 0;
    for (int i = 0; prefix[i]; i++) c->path[n++] = prefix[i];
    for (int i = 0; c->name[i]; i++) c->path[n++] = c->name[i];
    c->path[n++] = '/';
    c->path[n++] = 'f';
    c->path[n++] = (char)('0' + c->me / 10);
    c->path[n++] = (char)('0' + c->me % 10);
    c->path[n] = 0;
    switch (c->mode) {
    case HOG:
        hog(c);
        wait_forever(c);
    case HOGX:
        hog(c);
        exit_task();
    case HOGF:
        hog(c);
        *(volatile u64 *)PAGE(0) = 1;           /* its own code: not writable */
        exit_task();
    case BUSY:
        busy(c);
        exit_task();
    case FILES:
        files(c);
        exit_task();
    case PEST:
        pest(c);
        wait_forever(c);
    case WINS:
        for (u64 k = 0; k < 20 && open_window(APP_WIN_OFFSET + WIN_PAGES * k, 0x28965a + k) == OK; k++)
            c->windows++;
        say(c, "", c->windows, " windows, then the display refused one");
        wait_forever(c);
    case NAP:
        say(c, "asleep", 0, 0);
        for (;;) sleep_ms(1000);
    default:
        say(c, "run under a name it does not know", 0, 0);
        exit_task();
    }
}
