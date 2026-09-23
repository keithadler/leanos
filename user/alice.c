/* alice keeps a secret in her data page, draws a window in her own memory, and hands the
   display server a read-only capability to just those pages. At the end she checks nobody
   changed her secret. */
#include "lib.h"
#include "gfx.h"

#define WIN_W 240
#define WIN_H 100
#define WIN_PAGES ((WIN_W * WIN_H * 4 + 4095) / 4096)

__attribute__((section(".text.start"))) void _start(void) {
    volatile u64 *secret = (u64 *)DATA;
    *secret = 0x5ec12e7;
    struct line l = {.n = 0};
    put_s(&l, "alice: wrote secret ");
    put_hex(&l, *secret);
    put_s(&l, " to my data page\n");
    flush(&l);

    /* Draw into the start of the spare run, mapped at page 64. */
    sys2(SYS_MAP, 3, 64);
    struct surface win = {(unsigned *)PAGE(64), WIN_W, WIN_H, WIN_W};
    gradient(&win, 0, 0, WIN_W, WIN_H, rgb(255, 250, 235), rgb(250, 222, 180));
    text(&win, 12, 10, "Hello from alice", rgb(40, 40, 40), 2);
    text(&win, 12, 36, "These pixels are my memory.", rgb(90, 60, 30), 1);
    text(&win, 12, 50, "The display may read them;", rgb(90, 60, 30), 1);
    text(&win, 12, 64, "nobody else can, and nobody", rgb(90, 60, 30), 1);
    text(&win, 12, 78, "can write them. Proved.", rgb(90, 60, 30), 1);
    fill(&win, WIN_W - 30, 10, 18, 18, rgb(58, 150, 96));

    /* A read-only capability to exactly the window's pages, sent with its size. */
    struct res ro = sys(SYS_DERIVE, 3, R, 0, WIN_PAGES, 0);
    struct res sent = sys(SYS_SEND, ENDPOINT, WIN_W, WIN_H, 0, ro.x[1] + 1);
    put_s(&l, "alice: sent the display a ");
    put_dec(&l, WIN_W);
    put_s(&l, "x");
    put_dec(&l, WIN_H);
    put_s(&l, " window, read-only, ");
    put_dec(&l, WIN_PAGES);
    put_s(&l, " pages");
    put_s(&l, outcome(sent.status));
    put_s(&l, "\n");
    flush(&l);

    spin(3000000);
    put_s(&l, *secret == 0x5ec12e7 ? "alice: secret intact, exiting\n" : "alice: SECRET CHANGED\n");
    flush(&l);
    exit_task();
}
