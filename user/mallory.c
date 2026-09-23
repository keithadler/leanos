/* mallory may send to the display server, with badge 2, but not receive and not grant.
   She tries everything else anyway, including the screen. */
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
    report("receive on the display's endpoint", sys1(SYS_RECV, ENDPOINT));
    report("send the display a window of my pixels", sys(SYS_SEND, ENDPOINT, 100, 100, 0, 1 + 1));
    report("map the framebuffer (capability 5, which is the display's)", sys2(SYS_MAP, 5, 1024));
    report("map the endpoint as memory", sys2(SYS_MAP, ENDPOINT, 5));

    struct res d = sys2(SYS_DERIVE, ENDPOINT, RECV | SEND | GRANT);
    put_s(&l, "mallory: asked for every right on the endpoint, got ");
    put_ep_rights(&l, sys1(SYS_CAPINFO, d.x[1]).x[1]);
    put_s(&l, "\n");
    flush(&l);

    report("read block 0 of the SD card through capability 20, which I do not have",
           sys(SYS_BLOCKREAD, 20, 0, DATA, 0, 0));
    report("read block 0 of the SD card through my endpoint capability",
           sys(SYS_BLOCKREAD, ENDPOINT, 0, DATA, 0, 0));
    report("ask the display for a window without pixels", sys(SYS_SEND, ENDPOINT, 640, 480, 0, 0));

    put_s(&l, "mallory: writing to the screen's physical address 0x3c100000 directly\n");
    flush(&l);
    volatile u64 *p = (u64 *)0x3c100000UL;
    *p = 0xbad;
    put_s(&l, "mallory: SHOULD NOT GET HERE\n");
    flush(&l);
    exit_task();
}
