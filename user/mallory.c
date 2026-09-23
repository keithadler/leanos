/* mallory may send to the server, with badge 2, but not receive and not grant. She tries
   everything else anyway. */
#include "lib.h"

static void report(const char *what, struct res r) {
    struct line l = {.n = 0};
    put_s(&l, "mallory: ");
    put_s(&l, what);
    put_s(&l, outcome(r.status));
    put_s(&l, "\n");
    flush(&l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    put_s(&l, "mallory: I am task ");
    put_dec(&l, sys0(SYS_WHOAMI).x[1]);
    put_s(&l, "\n");
    flush(&l);

    report("map capability 9 (not mine) at page 5", sys2(SYS_MAP, 9, 5));
    report("print 16 bytes of kernel memory at 0x80000", sys2(SYS_WRITE, 0x80000, 16));
    report("receive on the server's endpoint", sys1(SYS_RECV, ENDPOINT));
    report("grant my data page to the server", sys(SYS_SEND, ENDPOINT, 1, 2, 3, 1 + 1));
    report("map the endpoint as memory", sys2(SYS_MAP, ENDPOINT, 5));

    struct res d = sys2(SYS_DERIVE, ENDPOINT, RECV | SEND | GRANT);
    put_s(&l, "mallory: asked for every right on the endpoint, got ");
    put_ep_rights(&l, sys1(SYS_CAPINFO, d.x[1]).x[1]);
    put_s(&l, "\n");
    flush(&l);

    report("send 666 to the server", sys(SYS_SEND, ENDPOINT, 666, 0, 0, 0));

    put_s(&l, "mallory: reading page 64 directly, which nobody mapped for me\n");
    flush(&l);
    volatile u64 *p = (u64 *)PAGE(64);
    u64 v = *p;
    put_s(&l, "mallory: SHOULD NOT GET HERE, read ");
    put_hex(&l, v);
    put_s(&l, "\n");
    flush(&l);
    exit_task();
}
