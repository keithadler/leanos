/* deep: a test program that gives the kernel its longest lists. It maps every page of its
   8192-page window (its spare run of 228 frames, again and again, and a piece of it for the
   gap at the end), then makes each walk over its mappings go all the way with nothing to
   take out: an unmap of no page, and a drop of a capability no page needs. Then it waits,
   holding all 8192 mappings, so that the next program started in another slot makes the
   kernel walk them once more, to take back that slot's frames. test/stack.sh runs it and
   reads the kernel stack's peak. */
#include "../lib.h"

#define SPARE 3              /* capability 3: the spare run, 228 frames, read-write */
#define SPARE_PAGES 228
#define STACK_FIRST 8188     /* the stack's four pages, which stay as they are */

static u64 piece(u64 count) {
    struct res r = sys(SYS_DERIVE, SPARE, R | W, 0, count, 0);
    return r.status == OK ? r.x[1] : ~0UL;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    u64 refused = 0;
    /* Pages 24 to 8187 (code and data are below, the stack above): 35 copies of the spare
       run, then a 184-page piece of it. */
    u64 v = 24;
    for (; v + SPARE_PAGES <= STACK_FIRST; v += SPARE_PAGES)
        refused += sys(SYS_MAP, SPARE, v, 0, 0, 0).status != OK;
    refused += sys(SYS_MAP, piece(STACK_FIRST - v), v, 0, 0, 0).status != OK;
    /* Walks that keep every mapping: unmap no page, drop a capability no page needs. */
    refused += sys(SYS_UNMAP, 100, 0, 0, 0, 0).status != OK;
    refused += sys(SYS_DROP, piece(1), 0, 0, 0, 0).status != OK;
    /* Every page of the window can be read now (a page that could not would stop us). */
    for (u64 p = 0; p < 8192; p++) (void)*(volatile unsigned char *)PAGE(p);
    put_s(&l, "deep: all 8192 pages mapped, ");
    put_dec(&l, refused);
    put_s(&l, " calls refused\n");
    flush(&l);
    for (;;) sleep_ms(1000);
}
