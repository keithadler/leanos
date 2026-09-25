/* restart: a test program for restarting an open slot while the display still knows its
   last run (test/restart.sh). What it does depends on the card file's name it was run as
   (the loader writes it into the image, beside the icon):

     blip   opens a window, then asks the file server about its own folder, over and over,
            timing each answer. When one takes far longer than the rest, someone else is
            loading a program (Terminal reading it from the card, after it has asked the
            display whether one is open, and before it starts it): blip exits then, so the
            slot it leaves is stopped between the display's last answer and the start.
     other  opens a window titled with its name and waits on it, printing every event it
            receives, with its own name, so a test can tell whose events reached whom.

   Every line it prints starts "restart: NAME in slot N". */
#include "../ui.h"
#include "../fs.h"
#include "../elf.h"

#define RW 120
#define RH 60

struct rs {
    struct fs_client fs;
    char name[16];
    u64 me;
};

static void head(struct line *l, struct rs *r) {
    put_s(l, "restart: ");
    put_s(l, r->name);
    put_s(l, " in slot ");
    put_dec(l, r->me);
    put_s(l, ": ");
}

static int same(const char *a, const char *b) {
    while (*a && *a == *b) a++, b++;
    return *a == *b;
}

/* Its load takes the file server a while (several requests): the table makes the program
   larger than one request carries, as big.c does. */
static const unsigned char ballast[36 * 1024] = {1};

/* Wait until the file server is busy with someone else's load, then exit: two answers in
   a row that each took far longer than the quickest. */
static void blip(struct rs *r) {
    char path[32] = "apps/blip";
    u64 quick = ~0UL;
    for (int i = 0; i < 64; i++) {
        u64 t0 = micros();
        fs_stat(&r->fs, path, 0);
        u64 d = micros() - t0;
        if (d < quick) quick = d;
    }
    struct line l = {.n = 0};
    head(&l, r);
    put_s(&l, "ready, the quickest answer took ");
    put_dec(&l, quick);
    put_s(&l, " us\n");
    flush(&l);
    u64 limit = 2 * quick + 1000, slow = 0;
    for (;;) {
        u64 t0 = micros();
        fs_stat(&r->fs, path, 0);
        u64 d = micros() - t0;
        if (d < limit) { slow = 0; continue; }
        if (!slow++) continue;
        head(&l, r);
        put_s(&l, "the file server was busy for ");
        put_dec(&l, d);
        put_s(&l, " us; exiting\n");
        flush(&l);
        exit_task();
    }
}

__attribute__((section(".text.start"))) void _start(void) {
    struct rs *r = (struct rs *)DATA;
    memset(r, 0, sizeof *r);
    app_assets();
    fs_init(&r->fs, SPARE_PAGE);
    r->me = sys0(SYS_WHOAMI).x[1];
    (void)((const volatile unsigned char *)ballast)[r->me];
    const volatile unsigned char *at = (const volatile unsigned char *)PAGE(ICON_IMAGE_PAGE);
    r->name[0] = '?';
    if (*(const volatile unsigned *)at == ICON_MAGIC)
        for (int i = 0; i < 15; i++) r->name[i] = (char)at[ICON_NAME_AT + i];
    struct surface s = app_surface(RW, RH);
    fill(&s, 0, 0, RW, RH, same(r->name, "blip") ? rgb(230, 90, 60) : rgb(60, 120, 230) + (unsigned)r->me);
    u64 opened = app_open(RW, RH, r->name);
    struct line l = {.n = 0};
    head(&l, r);
    put_s(&l, "opened");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    if (same(r->name, "blip")) blip(r);
    for (;;) {
        struct event e = app_wait(0);
        head(&l, r);
        put_s(&l, "event ");
        put_dec(&l, e.kind);
        put_s(&l, " ");
        if (e.kind == EV_KEY && e.a >= 32 && e.a < 127) {
            char c[2] = {(char)e.a, 0};
            put_s(&l, c);
        } else put_dec(&l, e.a);
        put_s(&l, " ");
        put_dec(&l, e.b);
        put_s(&l, "\n");
        flush(&l);
        if (e.kind == EV_CLOSE) exit_task();
    }
}
