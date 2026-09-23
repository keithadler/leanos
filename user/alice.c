/* alice's Notes. She draws a window in her own memory, hands the display server a
   read-only capability to exactly those pages, and then asks it, over and over, for her
   next event. Keys she is given go into the note. She also keeps a secret in her data
   pages and checks that nobody changes it. */
#include "lib.h"
#include "gfx.h"

#define WIN_W 240
#define WIN_H 150
#define WIN_PAGES ((WIN_W * WIN_H * 4 + 4095) / 4096)
#define SPARE 3
enum { OP_OPEN = 1, OP_WAIT = 2 };
enum { EV_KEY = 1 };

struct notes {
    u64 secret;
    char text[400];
    int len;
};

static void draw(struct surface *win, struct notes *n) {
    gradient(win, 0, 0, WIN_W, WIN_H, rgb(255, 252, 240), rgb(252, 238, 210));
    text(win, 12, 10, "Notes", rgb(60, 50, 40), 2);
    fill(win, 12, 30, WIN_W - 24, 1, rgb(220, 200, 170));
    /* The note, wrapped at the window's edge, then a cursor. */
    int x = 12, y = 40, cols = (WIN_W - 24) / 12;
    int col = 0;
    for (int i = 0; i < n->len; i++) {
        char c = n->text[i];
        if (c == '\n' || col == cols) { y += 18; col = 0; x = 12; if (c == '\n') continue; }
        char s[2] = {c, 0};
        text(win, x, y, s, rgb(40, 40, 48), 2);
        x += 12;
        col++;
    }
    fill(win, x, y - 1, 2, 16, rgb(52, 88, 158));
    text(win, 12, WIN_H - 18, "only alice can write this page", rgb(160, 130, 100), 1);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct notes *n = (struct notes *)DATA;
    n->secret = 0x5ec12e7;
    n->len = 0;
    struct line l = {.n = 0};
    put_s(&l, "alice: wrote secret ");
    put_hex(&l, n->secret);
    put_s(&l, " to my data page\n");
    flush(&l);

    sys2(SYS_MAP, SPARE, 64);
    struct surface win = surface_of((unsigned *)PAGE(64), WIN_W, WIN_H);
    draw(&win, n);

    /* A read-only capability to exactly the window's pages, and a title. */
    struct res ro = sys(SYS_DERIVE, SPARE, R, 0, WIN_PAGES, 0);
    u64 title = 0;
    const char *t = "Notes";
    for (int i = 0; t[i]; i++) title |= (u64)(unsigned char)t[i] << (8 * i);
    struct res opened = sys(SYS_CALL, ENDPOINT, OP_OPEN, (u64)WIN_W << 16 | WIN_H, title, ro.x[1] + 1);
    put_s(&l, "alice: opened a ");
    put_dec(&l, WIN_W);
    put_s(&l, "x");
    put_dec(&l, WIN_H);
    put_s(&l, " window, read-only, ");
    put_dec(&l, WIN_PAGES);
    put_s(&l, " pages");
    put_s(&l, outcome(opened.status == OK && opened.x[1] == 0 ? OK : BAD_ARG));
    put_s(&l, "\n");
    flush(&l);

    u64 dirty = 0;
    for (;;) {
        struct res e = sys(SYS_CALL, ENDPOINT, OP_WAIT, dirty, 0, 0);
        dirty = 0;
        if (n->secret != 0x5ec12e7) {
            put_s(&l, "alice: SECRET CHANGED\n");
            flush(&l);
        }
        if (e.status != OK || e.x[1] != EV_KEY) continue;
        char c = (char)e.x[2];
        if ((c == 8 || c == 127) && n->len > 0) n->len--;
        else if (c == '\r' || c == '\n') { if (n->len < 399) n->text[n->len++] = '\n'; }
        else if (c >= 32 && c < 127 && n->len < 399) n->text[n->len++] = c;
        else continue;
        draw(&win, n);
        dirty = 1;
    }
}
