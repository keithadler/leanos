/* forge: a program from the card whose own code run carries a forged icon (test/spoof.sh).

   The display server takes a window's name only from four pages of the program's code run
   that start with the loader's marker (user/display.c, on_icon): the one run nothing can
   write. But a program chooses which four pages of it to lend, and its code run holds
   whatever its file holds. So this one carries, at the start of a page of its constants,
   the marker, an icon and the name "clock", and lends those pages with the execute right.
   The loaders (Terminal's `run`, Apps) must refuse to run it at all: the marker may start
   no page of an image but the one the loader writes (image_marked in user/elf.h). If it
   runs all the same, it says what the display did with its claim. */
#include "../app.h"
#include "../elf.h"

struct forged {
    unsigned head[4];               /* the marker, the size, the icon's width and height */
    unsigned px[16 * 16];
    unsigned char pad[4 * 4096 - 16 - 16 * 16 * 4 - 16];
    char name[16];                  /* at the very end, where the loader writes a name */
};
static const struct forged forged __attribute__((aligned(4096), used)) = {
    .head = {ICON_MAGIC, 8 + 16 * 16 * 4, 16, 16}, .name = "clock"};

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    app_assets();
    unsigned *px = (unsigned *)PAGE(SPARE_PAGE + 64);
    for (int i = 0; i < 120 * 60; i++) px[i] = 0xa03050;
    struct res d = sys(SYS_DERIVE, SPARE, R, 64, 8, 0);
    struct res r = sys(SYS_CALL, ENDPOINT, OP_OPEN, 120 << 16 | 60, 0x6567726f66 /* "forge" */, d.x[1] + 1);
    u64 page = ((u64)&forged - PAGE(0)) / 4096;
    struct res ic = sys(SYS_DERIVE, 0, R | X, page, 4, 0);
    r = sys(SYS_CALL, ENDPOINT, OP_ICON, 0, 0, ic.x[1] + 1);
    put_s(&l, "forge: ran; claim clock from its code run, page ");
    put_dec(&l, page);
    put_s(&l, r.status == OK && r.x[1] == 0 ? ": TAKEN\n" : ": refused\n");
    flush(&l);
    for (;;) {
        struct event e = app_wait(0);
        if (e.kind == EV_CLOSE) exit_task();
    }
}
