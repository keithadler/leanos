/* The client side of the display server's protocol, for an app with one window.

   An app draws its window into its own spare run, after its assets, and hands the display
   server a read-only capability to exactly those pages. Then it asks, over and over, for its
   next event; the display answers when it has one. EV_CLOSE means the window's close button
   was clicked: the app should stop. */
#pragma once
#include "lib.h"
#include "gfx.h"
#include "assets.h"

enum { OP_OPEN = 1, OP_WAIT = 2, OP_SET = 3 };
enum { EV_NONE = 0, EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4, EV_CLOSE = 5 };
enum { SET_BACKGROUND = 1 };

#define SPARE 3
#define SPARE_PAGE 64       /* where an app maps its spare run: assets first */
#define APP_WIN_OFFSET 64   /* the window's pixels, this many pages into the spare run */
#define APP_WIN_PAGES 160   /* the most a window may use (the display's limit) */

struct event { u64 kind, a, b; };

#define NSLOTS 12  /* program slots in the manifest */

/* Map the spare run (read-write, the app's own) and return its assets. */
static inline const unsigned char *app_assets(void) {
    sys2(SYS_MAP, SPARE, SPARE_PAGE);
    return (const unsigned char *)PAGE(SPARE_PAGE);
}

static inline struct surface app_surface(int w, int h) {
    return surface_of((unsigned *)PAGE(SPARE_PAGE + APP_WIN_OFFSET), w, h);
}

/* Ask the display for a window showing the pixels app_surface returns. */
static inline u64 app_open(int w, int h, const char *title) {
    u64 pages = ((u64)w * (u64)h * 4 + 4095) / 4096, t = 0;
    for (int i = 0; i < 8 && title[i]; i++) t |= (u64)(unsigned char)title[i] << (8 * i);
    struct res ro = sys(SYS_DERIVE, SPARE, R, APP_WIN_OFFSET, pages, 0);
    if (ro.status != OK) return ro.status;
    struct res r = sys(SYS_CALL, ENDPOINT, OP_OPEN, (u64)w << 16 | (u64)h, t, ro.x[1] + 1);
    return r.status == OK && r.x[1] == 0 ? OK : BAD_ARG;
}

/* Wait for the next event. `dirty`: the app redrew its pixels since it last asked. */
static inline struct event app_wait(int dirty) {
    struct res e = sys(SYS_CALL, ENDPOINT, OP_WAIT, (u64)dirty, 0, 0);
    struct event ev = {e.status == OK ? e.x[1] : EV_NONE, e.x[2], e.x[3]};
    return ev;
}

/* A slot's name, as the manifest orders them. */
static inline const char *slot_name(u64 k) {
    static const char *const names[NSLOTS] = {"Notes", "Display server", "Test: mallory", "Test: carol",
                                              "Input driver", "Terminal", "Settings", "Security",
                                              "File server", "Files", "Open slot 10", "Open slot 11"};
    return k < NSLOTS ? names[k] : "?";
}
