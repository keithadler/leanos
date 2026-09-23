/* The display server. It owns the framebuffer (capability 5, 300 pages) and nothing else
   can reach it. Clients send it a window: a size in the message words and, with it, a
   read-only capability to the pixels they drew. The server decorates each window, names
   it by the sender's badge (which the kernel sets, so it cannot be forged), and copies it
   onto the screen. */
#include "lib.h"
#include "gfx.h"

#define FRAMEBUFFER 5
#define FB_PAGE 1024      /* where the framebuffer is mapped */
#define WINDOW_PAGE 2048  /* where a client's window is mapped while it is drawn */

static const char *name_of(u64 badge) {
    return badge == 1 ? "alice" : badge == 2 ? "mallory" : "unknown";
}

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static void desktop(struct surface *screen) {
    gradient(screen, 0, 0, screen->w, screen->h, rgb(22, 40, 74), rgb(34, 110, 120));
    fill(screen, 0, 0, screen->w, 24, rgb(245, 243, 236));
    fill(screen, 0, 24, screen->w, 1, rgb(190, 186, 176));
    text(screen, 10, 5, "leanos", rgb(30, 30, 30), 2);
    const char *right = "access control proved in Lean";
    text(screen, screen->w - 10 - text_width(right, 2), 5, right, rgb(90, 90, 90), 2);
}

static void window(struct surface *screen, int x, int y, const char *title, const struct surface *content) {
    int w = content->w + 4, h = content->h + 26;
    fill(screen, x + 6, y + 6, w, h, rgb(10, 20, 35));                /* shadow */
    fill(screen, x, y, w, h, rgb(245, 243, 236));                     /* frame */
    fill(screen, x + 2, y + 2, w - 4, 20, rgb(58, 96, 150));          /* title bar */
    text(screen, x + 8, y + 5, title, rgb(255, 255, 255), 2);
    blit(screen, x + 2, y + 24, content);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    struct res m = sys2(SYS_MAP, FRAMEBUFFER, FB_PAGE);
    if (m.status != OK) {
        put_s(&l, "display: no framebuffer to draw on");
        say(&l);
        exit_task();
    }
    struct surface screen = {(unsigned *)PAGE(FB_PAGE), 640, 480, 640};
    desktop(&screen);
    put_s(&l, "display: desktop drawn on the 640x480 framebuffer");
    say(&l);

    int placed = 0;
    for (;;) {
        struct res r = sys1(SYS_RECV, ENDPOINT);
        u64 badge = r.x[1], w = r.x[2], h = r.x[3], cap = r.x[5];
        put_s(&l, "display: ");
        put_s(&l, name_of(badge));
        if (!cap) {
            put_s(&l, " asked for a window but sent no pixels; ignored");
            say(&l);
            continue;
        }
        cap -= 1;
        struct res info = sys1(SYS_CAPINFO, cap);
        u64 need = (w * h * 4 + 4095) / 4096;
        if (w == 0 || h == 0 || w > 600 || h > 400 || info.x[2] != 0 || info.x[3] < need) {
            put_s(&l, " sent a window that does not fit its pixels; ignored");
            say(&l);
            continue;
        }
        sys2(SYS_MAP, cap, WINDOW_PAGE);
        struct surface content = {(unsigned *)PAGE(WINDOW_PAGE), (int)w, (int)h, (int)w};
        int x = 60 + 40 * placed, y = 70 + 36 * placed;
        placed++;
        window(&screen, x, y, name_of(badge), &content);
        put_s(&l, "'s window, ");
        put_dec(&l, w);
        put_s(&l, "x");
        put_dec(&l, h);
        put_s(&l, " from a read-only capability to ");
        put_dec(&l, info.x[3]);
        put_s(&l, " pages, drawn at (");
        put_dec(&l, x);
        put_s(&l, ", ");
        put_dec(&l, y);
        put_s(&l, ")");
        say(&l);
    }
}
