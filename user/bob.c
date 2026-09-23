/* bob tries to get at memory that is not his: a capability he does not hold, more rights
   than he was given, the kernel's own memory through `write`, and finally a raw read of a
   page nobody mapped for him. */
#include "lib.h"

static void report(const char *what, struct res r) {
    struct line l = {.n = 0};
    put_s(&l, "bob: ");
    put_s(&l, what);
    put_s(&l, r.status == OK ? " -> ok" : r.status == NO_CAP ? " -> refused, no such capability"
                                       : " -> refused, bad argument");
    put_s(&l, "\n");
    flush(&l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    put_s(&l, "bob: I am task ");
    put_dec(&l, sys(SYS_WHOAMI, 0, 0).value);
    put_s(&l, "\n");
    flush(&l);

    report("map capability 9 (not mine) at page 5", sys(SYS_MAP, 9, 5));
    report("print 16 bytes of kernel memory at 0x40080000", sys(SYS_WRITE, 0x40080000, 16));
    report("print from page 7, which I have not mapped", sys(SYS_WRITE, PAGE(7), 16));

    struct res d = sys(SYS_DERIVE, 1, R | W | X);
    struct res info = sys(SYS_CAPINFO, d.value, 0);
    put_s(&l, "bob: asked for rwx on my data frame, got capability ");
    put_dec(&l, d.value);
    put_s(&l, " with ");
    put_rights(&l, info.value);
    put_s(&l, "\n");
    flush(&l);

    report("map my spare frame (capability 3) at page 2", sys(SYS_MAP, 3, 2));
    volatile u64 *spare = (u64 *)PAGE(2);
    *spare = 42;
    put_s(&l, "bob: wrote and read back ");
    put_dec(&l, *spare);
    put_s(&l, " through page 2\n");
    flush(&l);

    spin(2000000);
    put_s(&l, "bob: now reading page 3 directly, which is not mapped\n");
    flush(&l);
    volatile u64 *nothing = (u64 *)PAGE(3);
    u64 v = *nothing;
    put_s(&l, "bob: SHOULD NOT GET HERE, read ");
    put_hex(&l, v);
    put_s(&l, "\n");
    flush(&l);
    exit_task();
}
