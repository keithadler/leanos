/* tour: a guided tour of why leanos is harder to attack than a typical Linux desktop.

   The tour is itself an untrusted program from the SD card, in an open slot: it holds only
   its own memory and a window. On each page it really tries an attack and shows what the
   kernel answered, then says what a typical Linux desktop would have allowed. Right arrow,
   Enter, space or a click: next page. Left arrow or Backspace: back.

   The comparisons are about Linux as most desktops ship it; where Linux has a mitigation
   that closes the gap when it is switched on, the page names it. */
#include "../app.h"

#define TW 600
#define TH 270
#define MARGIN 20
#define COLS ((TW - 2 * MARGIN) / 12)   /* characters per line at scale 2 */

enum { TRY_NONE, TRY_FILES, TRY_MEMORY, TRY_DISK, TRY_KEYS, TRY_WX, TRY_TAMPER, TRY_POWER };

struct page {
    const char *title;
    int try;
    const char *leanos;
    const char *linux_;
};

static const struct page pages[] = {
    {"A guided tour", TRY_NONE,
     "This tour is an untrusted program from the SD card. On each page it really tries an "
     "attack, and you see what the kernel answered.",
     "Next: right arrow, Enter or a click. Back: left arrow. Close the window to stop."},
    {"Your files", TRY_FILES,
     "A program gets only the capabilities its slot is given. This one was never given the "
     "file server, so it has nothing to ask with.",
     "Every program you run has all of your user's rights: ~/.ssh, your browser profile, "
     "every document. Unless you sandbox it (Flatpak, SELinux)."},
    {"Other programs' memory", TRY_MEMORY,
     "Memory is reached only through capabilities, and the proofs show a program only ever "
     "holds its own frames (theorem confined).",
     "Processes of the same user can read each other's memory (ptrace, /proc/PID/mem); Yama "
     "limits it on many distributions, to a program's children."},
    {"The disk", TRY_DISK,
     "Only the file server holds any of the SD card, and only its data partition (theorem "
     "disk_only_file_server).",
     "root can read and write every disk block, and so can any program that becomes root: "
     "through sudo, a setuid bug or a kernel exploit."},
    {"Your keystrokes", TRY_KEYS,
     "Only the input driver can touch the keyboard (uart_confined), and the display server "
     "hands each key only to the window in front.",
     "On X11, still used by many desktops, any program can read every key typed in any "
     "window. Wayland stops that; X11 does not."},
    {"Writing, then running code", TRY_WX,
     "No page is ever both writable and executable (theorem no_write_execute): code an "
     "attacker writes can never be run.",
     "A program may map memory writable and executable (JIT compilers rely on it). SELinux "
     "can forbid it per program; by default most may."},
    {"Tampered programs", TRY_TAMPER,
     "Every program the manifest names is measured (SHA-256) before it runs; change one bit "
     "and it never starts (theorem only_verified_runs).",
     "Secure Boot checks the bootloader and kernel. The programs you run are not checked "
     "against anything by default (IMA can, but is rarely on)."},
    {"No all-powerful account", TRY_POWER,
     "There is no root. The screen, the disk, the power switch and starting programs each "
     "belong to one component, fixed in the manifest.",
     "root can do anything, and one privilege-escalation bug in the kernel or in any setuid "
     "program gives any process root."},
    {"Checked by proofs", TRY_NONE,
     "The kernel's decisions are 1,100 lines of Lean, compiled into it, with 42 "
     "machine-checked theorems. 61 deliberate breaks: the proofs catch all.",
     "Tens of millions of lines of C, reviewed and tested, not proved. Thousands of kernel "
     "CVEs were published in 2024 alone."},
    {"What Linux does better", TRY_NONE,
     "leanos trusts what its proofs do not cover: its C machine layer, the Lean compiler, "
     "its model of the MMU, the hardware (see TRUST.md).",
     "Linux runs on almost anything, with drivers, networking and decades of hardening; "
     "switched on, its mitigations close many of these gaps."},
    {"The difference", TRY_NONE,
     "On leanos a program starts with nothing and is given what it needs. That is the "
     "default, and the proofs say it holds.",
     "On Linux a program starts with everything its user has, and you take away what you "
     "can. That is the end of the tour."},
};
#define NPAGES (int)(sizeof pages / sizeof pages[0])

struct tour {
    struct surface win;
    int page;
    char result[160];
    int refused;         /* the try's outcome: 1 refused, 0 allowed, -1 no try */
};

static void set(struct tour *t, const char *what, u64 code) {
    struct line l = {.n = 0};
    put_s(&l, what);
    put_s(&l, outcome(code));
    int n = (int)l.n < 159 ? (int)l.n : 159;
    for (int i = 0; i < n; i++) t->result[i] = l.b[i];
    t->result[n] = 0;
    t->refused = code != OK;
}

/* Really try this page's attack, and keep what the kernel said. */
static void attempt(struct tour *t) {
    t->refused = -1;
    t->result[0] = 0;
    switch (pages[t->page].try) {
    case TRY_FILES:        /* the file server's endpoint would be a capability this program lacks */
        set(t, "Asked the file server for your files", sys(SYS_CALL, 20, 1, 0, 0, 0).status);
        break;
    case TRY_MEMORY: {
        u64 a = sys2(SYS_MAP, 20, 1000).status;                       /* someone else's frames */
        u64 b = sys(SYS_DERIVE, 1, R, 0, 9, 0).status;                /* 9 pages of an 8-page run */
        set(t, "Mapped frames it was not given, and stretched its own", a != OK && b != OK ? BAD_ARG : OK);
        break;
    }
    case TRY_DISK:         /* through the only endpoint it holds, the display server's */
        set(t, "Read block 0 of the SD card", sys(SYS_BLOCKREAD, 4, 0, DATA, 0, 0).status);
        break;
    case TRY_KEYS:         /* every key arrives at the display server's endpoint */
        set(t, "Listened on the display server's endpoint", sys1(SYS_RECV, 4).status);
        break;
    case TRY_WX: {
        struct res d = sys(SYS_DERIVE, 1, R | W | X, 0, 1, 0);
        u64 bits = d.status == OK ? sys1(SYS_CAPINFO, d.x[1]).x[1] : 0;
        if (d.status == OK) sys1(SYS_DROP, d.x[1]);
        struct line l = {.n = 0};
        put_s(&l, "Asked for write+execute on its data, got ");
        put_rights(&l, bits);
        int n = (int)l.n < 159 ? (int)l.n : 159;
        for (int i = 0; i < n; i++) t->result[i] = l.b[i];
        t->result[n] = 0;
        t->refused = (bits & (W | X)) != (W | X);
        break;
    }
    case TRY_TAMPER: {
        int ok = 0, bad = 0;
        for (u64 k = 0; k < NSLOTS; k++) {
            u64 v = sys1(SYS_BOOTINFO, k).x[1];
            ok += v == 1;
            bad += v == 2;
        }
        struct line l = {.n = 0};
        put_s(&l, "Checked now: ");
        put_dec(&l, (u64)ok);
        put_s(&l, " programs match the manifest, ");
        put_dec(&l, (u64)bad);
        put_s(&l, " refused");
        int n = (int)l.n < 159 ? (int)l.n : 159;
        for (int i = 0; i < n; i++) t->result[i] = l.b[i];
        t->result[n] = 0;
        t->refused = -1;
        break;
    }
    case TRY_POWER:
        set(t, "Tried to switch the machine off", sys(SYS_POWER, 20, 0, 0, 0, 0).status);
        break;
    }
    struct line l = {.n = 0};
    put_s(&l, "tour: ");
    put_s(&l, pages[t->page].title);
    if (t->result[0]) {
        put_s(&l, ": ");
        put_s(&l, t->result);
    }
    put_s(&l, "\n");
    flush(&l);
}

/* Words of `s` wrapped at `cols` characters, from y down; returns the y after them. */
static int wrap(struct surface *s, int x, int y, const char *str, unsigned c, int cols) {
    while (*str) {
        int n = 0, cut = 0;
        while (str[n] && n < cols) {
            if (str[n] == ' ') cut = n;
            n++;
        }
        if (str[n] && cut > 0) n = cut;
        char line[64];
        for (int i = 0; i < n && i < 63; i++) line[i] = str[i];
        line[n < 63 ? n : 63] = 0;
        text(s, x, y, line, c, 2);
        y += 17;
        str += n;
        while (*str == ' ') str++;
    }
    return y;
}

static void draw(struct tour *t) {
    struct surface *s = &t->win;
    const struct page *p = &pages[t->page];
    fill(s, 0, 0, TW, TH, rgb(250, 250, 252));
    struct line l = {.n = 0};
    put_dec(&l, (u64)(t->page + 1));
    put_s(&l, " / ");
    put_dec(&l, (u64)NPAGES);
    l.b[l.n] = 0;
    text(s, TW - MARGIN - text_width(l.b, 2), 16, l.b, rgb(150, 150, 160), 2);
    text(s, MARGIN, 14, p->title, rgb(28, 30, 40), 3);
    int y = 48;
    if (t->result[0]) {
        unsigned bg = t->refused == 1 ? rgb(232, 246, 236) : t->refused == 0 ? rgb(252, 232, 230) : rgb(236, 240, 250);
        unsigned fg = t->refused == 1 ? rgb(24, 120, 60) : t->refused == 0 ? rgb(180, 40, 30) : rgb(50, 70, 140);
        round_rect(s, MARGIN - 8, y - 6, TW - 2 * MARGIN + 16, 44, 8, bg, 255);
        wrap(s, MARGIN, y, t->result, fg, COLS);
        y += 48;
    }
    int first = t->page == 0, last = t->page == NPAGES - 1;
    text(s, MARGIN, y, first ? "What this is" : "On leanos", rgb(58, 110, 230), 2);
    y = wrap(s, MARGIN, y + 18, p->leanos, rgb(40, 40, 50), COLS) + 6;
    text(s, MARGIN, y, first ? "How" : last ? "On Linux" : "On a typical Linux desktop", rgb(150, 90, 30), 2);
    wrap(s, MARGIN, y + 18, p->linux_, rgb(70, 70, 80), COLS);
}

static void go(struct tour *t, int page) {
    if (page < 0 || page >= NPAGES) return;
    t->page = page;
    attempt(t);
    draw(t);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct tour *t = (struct tour *)DATA;
    struct line l = {.n = 0};
    app_assets();
    t->win = app_surface(TW, TH);
    t->page = 0;
    t->result[0] = 0;
    t->refused = -1;
    draw(t);
    u64 opened = app_open(TW, TH, "Tour");
    put_s(&l, "tour: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "tour: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        int page = t->page;
        if (e.kind == EV_DOWN) page++;
        else if (e.kind == EV_KEY && (e.a == KEY_RIGHT || e.a == '\r' || e.a == ' ' || e.a == 'n')) page++;
        else if (e.kind == EV_KEY && (e.a == KEY_LEFT || e.a == 127 || e.a == 8 || e.a == 'p')) page--;
        else continue;
        if (page == t->page || page < 0 || page >= NPAGES) continue;
        go(t, page);
        dirty = 1;
    }
}
