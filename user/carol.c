/* carol tries to run code she wrote. No capability can be both writable and executable,
   so the page she writes to can never run. */
#include "lib.h"

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    struct res d = sys2(SYS_DERIVE, 1, W | X);
    put_s(&l, "carol: asked for write+execute on my data frame, got ");
    put_rights(&l, sys1(SYS_CAPINFO, d.x[1]).x[1]);
    put_s(&l, "\n");
    flush(&l);

    volatile unsigned *code = (unsigned *)DATA;
    code[0] = 0xd65f03c0; /* ret */
    spin(1000000);
    put_s(&l, "carol: jumping into the instruction I wrote in my data page\n");
    flush(&l);
    ((void (*)(void))DATA)();
    put_s(&l, "carol: SHOULD NOT GET HERE\n");
    flush(&l);
    exit_task();
}
