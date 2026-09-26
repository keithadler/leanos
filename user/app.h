/* The client side of the display server's protocol, for an app with one window.

   An app draws its window into its own spare run, after its assets, and hands the display
   server a read-only capability to exactly those pages. Then it asks, over and over, for its
   next event; the display answers when it has one. EV_CLOSE means the window's close button
   was clicked: the app should stop. */
#pragma once
#include "lib.h"
#include "gfx.h"
#include "assets.h"

enum { OP_OPEN = 1, OP_WAIT = 2, OP_SET = 3, OP_POLL = 4, OP_ICON = 5, OP_START = 6, OP_RAISE = 7, OP_PENDING = 8,
       OP_ZONE = 9, OP_COPY = 10 };
enum { EV_NONE = 0, EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4, EV_CLOSE = 5, EV_LAUNCH = 6, EV_COPY = 7,
       EV_PASTE = 8 };
/* The arrow keys, as EV_KEY codes (the input driver turns ESC [ A..D into these). */
enum { KEY_UP = 128, KEY_DOWN = 129, KEY_RIGHT = 130, KEY_LEFT = 131 };
enum { SET_BACKGROUND = 1, SET_ZONE = 2 };

#define SPARE 3
#define SPARE_PAGE 64       /* where an app maps its spare run: assets first */
#define APP_WIN_OFFSET 64   /* the window's pixels, this many pages into the spare run */
#define APP_WIN_PAGES 164   /* the most a window may use: the spare run's 228 pages less the assets' 64 */

struct event { u64 kind, a, b; };

#define NSLOTS 17  /* program slots in the manifest */

/* Map the spare run (read-write, the app's own) and return its assets. */
static inline const unsigned char *app_assets(void) {
    sys2(SYS_MAP, SPARE, SPARE_PAGE);
    return (const unsigned char *)PAGE(SPARE_PAGE);
}

static inline struct surface app_surface_at(u64 offset, int w, int h) {
    return surface_of((unsigned *)PAGE(SPARE_PAGE + offset), w, h);
}
static inline struct surface app_surface(int w, int h) { return app_surface_at(APP_WIN_OFFSET, w, h); }

/* Ask the display for a window showing the pixels app_surface_at(offset) returns. */
static inline u64 app_open_at(u64 offset, int w, int h, const char *title) {
    u64 pages = ((u64)w * (u64)h * 4 + 4095) / 4096, t = 0;
    for (int i = 0; i < 8 && title[i]; i++) t |= (u64)(unsigned char)title[i] << (8 * i);
    struct res ro = sys(SYS_DERIVE, SPARE, R, offset, pages, 0);
    if (ro.status != OK) return ro.status;
    struct res r = sys(SYS_CALL, ENDPOINT, OP_OPEN, (u64)w << 16 | (u64)h, t, ro.x[1] + 1);
    if (r.status != OK || r.x[1] != 0) return BAD_ARG;
    /* If the loader put this program's icon and name in its image (pages 12-15 of the code
       run, see elf.h), lend the display those pages, for the title bar and the dock, with the
       code run's read and execute rights: the display takes a name only from pages that can
       execute, and those are only ever a program's own code run, which nothing can write. */
    if (*(const volatile unsigned *)PAGE(12) == 0x43494e4cu) {
        struct res ic = sys(SYS_DERIVE, 0, R | X, 12, 4, 0);
        if (ic.status == OK) sys(SYS_CALL, ENDPOINT, OP_ICON, 0, 0, ic.x[1] + 1);
    }
    return OK;
}
static inline u64 app_open(int w, int h, const char *title) { return app_open_at(APP_WIN_OFFSET, w, h, title); }

/* If the program from the card file `name` already has a window, ask the display to bring
   it to the front, and say so: one copy of a program is enough. The name goes in two
   message words, eight bytes each (ASCII never sets a word's top bit, which messages drop). */
static inline int app_raise(const char *name) {
    u64 w[2] = {0, 0};
    for (int i = 0; i < 15 && name[i]; i++) w[i / 8] |= (u64)(unsigned char)name[i] << (8 * (i % 8));
    struct res r = sys(SYS_CALL, ENDPOINT, OP_RAISE, w[0], w[1], 0);
    return r.status == OK && r.x[1] == 0;
}

/* A launcher (Terminal, Apps) calls this after it finds an open slot not running and just
   before it starts a program there. The display forgets the windows of every stopped
   program before it answers any call, so by the time the slot starts again the display
   holds nothing of its last run: not its window (whose pixels the start takes back), not a
   call it held for it (whose reply slot the start frees, for the next caller to take). An
   OP_RAISE with no name asks nothing else. */
static inline void app_before_start(void) { sys(SYS_CALL, ENDPOINT, OP_RAISE, 0, 0, 0); }

/* The display holds at most 7 waiting windows' calls (the kernel gives it 8 reply slots, and
   it keeps one free). With more windows waiting, it answers the one that has waited longest
   with no event (EV_NONE), and answers again at once, with no event, while that window has
   none and the slots are still taken: a program that waits must then ask again only after
   a moment, as app_wait does, or it and the display spin. */
#define WAIT_AGAIN_MS 100

/* Wait for the next event (never EV_NONE). `dirty`: the app redrew its pixels since it last
   asked. */
static inline struct event app_wait(int dirty) {
    for (;;) {
        struct res e = sys(SYS_CALL, ENDPOINT, OP_WAIT, (u64)dirty, 0, 0);
        if (e.status == OK && e.x[1] != EV_NONE) {
            struct event ev = {e.x[1], e.x[2], e.x[3]};
            return ev;
        }
        dirty = 0;               /* the display drew it when it took the call */
        sleep_ms(WAIT_AGAIN_MS);
    }
}

/* The next event if there is one, EV_NONE if not: never blocks. For a program that keeps
   time itself (with sleep) and must still hear the close button. */
static inline struct event app_poll(int dirty) {
    struct res e = sys(SYS_CALL, ENDPOINT, OP_POLL, (u64)dirty, 0, 0);
    struct event ev = {e.status == OK ? e.x[1] : EV_NONE, e.x[2], e.x[3]};
    return ev;
}

/* The time zone the display server keeps (zone.h): minutes east of UTC. Anyone may ask; only
   Settings may change it. The answer comes biased by 12 hours: a message word is never
   negative. UTC if the display does not answer. */
static inline long app_zone(void) {
    struct res r = sys(SYS_CALL, ENDPOINT, OP_ZONE, 0, 0, 0);
    long m = r.status == OK && r.x[1] == 0 && r.x[2] <= 26 * 60 ? (long)r.x[2] - 12 * 60 : 0;
    return m % 15 ? 0 : m;
}

/* Copy and paste. The display server keeps what was copied: up to CLIP_MAX bytes of text,
   printable ASCII and line breaks. Text moves between programs only by the user's hand:

   - EV_COPY: the user pressed Ctrl+C (or chose Edit, Copy) with this window in front. Answer
     with app_copy() at once. The display takes a copy only from the window it asked, once,
     within COPY_MS of asking; OP_COPY at any other time is refused.
   - EV_PASTE: the user pressed Ctrl+V (or Edit, Paste) with this window in front. The text
     comes as a run of EV_PASTE events, up to 16 bytes each in a and b (paste_text() takes
     them out); one with fewer than 16 bytes is the last.

   There is no request that reads what was copied: a program sees it only when the user
   pastes into its window. */
#define CLIP_MAX 4096
#define COPY_MS 2000

/* Answer EV_COPY: send the display `n` bytes of text, 16 to a call (bytes 1 to 127 only; the
   display keeps printable ASCII and line breaks). A call with fewer than 16 bytes, or the
   one that reaches CLIP_MAX, ends the copy. OK if the display took it. */
static inline u64 app_copy(const char *text, u64 n) {
    u64 i = 0, sent = 0;
    for (;;) {
        u64 w[2] = {0, 0};
        int k = 0;
        while (k < 16 && i < n && sent < CLIP_MAX) {
            unsigned char c = (unsigned char)text[i++];
            if (c == 0 || c > 127) continue;
            w[k / 8] |= (u64)c << (8 * (k % 8));
            k++;
            sent++;
        }
        struct res r = sys(SYS_CALL, ENDPOINT, OP_COPY, w[0], w[1], 0);
        if (r.status != OK || r.x[1] != 0) return BAD_ARG;
        if (k < 16 || sent == CLIP_MAX) return OK;
    }
}

/* The text an EV_PASTE event carries, into out: how many bytes (fewer than 16: the last). */
static inline int paste_text(struct event e, char out[16]) {
    int n = 0;
    for (int k = 0; k < 16; k++) {
        char c = (char)(((k < 8 ? e.a : e.b) >> (8 * (k % 8))) & 0x7f);
        if (!c) break;
        out[n++] = c;
    }
    return n;
}

/* A slot's name, as the manifest orders them. */
static inline const char *slot_name(u64 k) {
    static const char *const names[NSLOTS] = {"Notes", "Display server", "Test: mallory", "Test: carol",
                                              "Input driver", "Terminal", "Settings", "Security",
                                              "File server", "Files", "Open slot 10", "Open slot 11",
                                              "Open slot 12", "Open slot 13", "Open slot 14", "Open slot 15",
                                              "Apps"};
    return k < NSLOTS ? names[k] : "?";
}
