/* alice keeps a secret in her data page, shares another page with the server read-only,
   and sends it a message. At the end she checks nobody changed her secret. */
#include "lib.h"

static const char text[] = "a page alice drew into and shared, read-only";

__attribute__((section(".text.start"))) void _start(void) {
    volatile u64 *secret = (u64 *)DATA;
    *secret = 0x5ec12e7;
    struct line l = {.n = 0};
    put_s(&l, "alice: wrote secret ");
    put_hex(&l, *secret);
    put_s(&l, " to my data page\n");
    flush(&l);

    /* Draw into the first spare page, then hand the server a read-only capability to just
       that page: offset 0, one frame of the 28. */
    sys2(SYS_MAP, 3, 64);
    char *shared = (char *)PAGE(64);
    u64 n = 0;
    for (; text[n]; n++) shared[n] = text[n];
    struct res ro = sys(SYS_DERIVE, 3, R, 0, 1, 0);
    struct res sent = sys(SYS_SEND, ENDPOINT, n, 0, 0, ro.x[1] + 1);
    put_s(&l, "alice: granted the server read-only capability ");
    put_dec(&l, ro.x[1]);
    put_s(&l, " to one page of my memory");
    put_s(&l, outcome(sent.status));
    put_s(&l, "\n");
    flush(&l);

    spin(3000000);
    sent = sys(SYS_SEND, ENDPOINT, 7, 8, 9, 0);
    put_s(&l, "alice: sent the words 7 8 9");
    put_s(&l, outcome(sent.status));
    put_s(&l, "\n");
    flush(&l);

    spin(3000000);
    put_s(&l, *secret == 0x5ec12e7 ? "alice: secret intact, exiting\n" : "alice: SECRET CHANGED\n");
    flush(&l);
    exit_task();
}
