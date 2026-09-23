/* The server receives three messages on its endpoint. The badge tells it who sent each
   one; the kernel sets badges, so a sender cannot pretend to be someone else. When a
   message carries a frame, the server maps it and prints what is on it. */
#include "lib.h"

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    put_s(&l, "server: waiting for messages\n");
    flush(&l);
    for (int i = 0; i < 3; i++) {
        struct res r = sys1(SYS_RECV, ENDPOINT);
        put_s(&l, "server: from badge ");
        put_dec(&l, r.x[1]);
        put_s(&l, ": ");
        put_dec(&l, r.x[2]);
        put_s(&l, " ");
        put_dec(&l, r.x[3]);
        put_s(&l, " ");
        put_dec(&l, r.x[4]);
        if (r.x[5]) {
            u64 cap = r.x[5] - 1;
            struct res info = sys1(SYS_CAPINFO, cap);
            put_s(&l, ", with a frame capability (");
            put_rights(&l, info.x[1]);
            put_s(&l, ")");
            flush(&l);
            sys2(SYS_MAP, cap, 8);
            put_s(&l, "; mapped at page 8, it says: ");
            flush(&l);
            sys2(SYS_WRITE, PAGE(8), r.x[2]);
        }
        put_s(&l, "\n");
        flush(&l);
    }
    put_s(&l, "server: done\n");
    flush(&l);
    exit_task();
}
