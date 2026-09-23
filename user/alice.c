/* alice keeps a secret in her data page and checks, after the others have tried their
   worst, that nobody changed it. She never yields: the timer takes turns away from her. */
#include "lib.h"

__attribute__((section(".text.start"))) void _start(void) {
    volatile u64 *secret = (u64 *)PAGE(1);
    *secret = 0x5ec12e7;
    struct line l = {.n = 0};
    put_s(&l, "alice: wrote secret ");
    put_hex(&l, *secret);
    put_s(&l, " to my data page\n");
    flush(&l);
    for (int round = 1; round <= 3; round++) {
        spin(3000000);
        put_s(&l, "alice: still working, round ");
        put_dec(&l, round);
        put_s(&l, "\n");
        flush(&l);
    }
    put_s(&l, *secret == 0x5ec12e7 ? "alice: secret intact, exiting\n" : "alice: SECRET CHANGED\n");
    flush(&l);
    exit_task();
}
