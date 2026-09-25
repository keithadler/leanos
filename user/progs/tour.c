/* tour: a guided tour of why leanos is harder to attack than a typical Linux desktop.

   The tour is itself an untrusted program from the SD card, in an open slot: it holds only
   its own memory and a window. On each page it really tries an attack and shows what the
   kernel answered, then says what a typical Linux desktop would have allowed. Right arrow,
   Enter, space or a click: next page. Left arrow or Backspace: back.

   The comparisons are about Linux as most desktops ship it; where Linux has a mitigation
   that closes the gap when it is switched on, the page names it. */
#include "../ui.h"
#include "../fs.h"

#define TW 640
#define TH 288
#define WIN_OFFSET 40        /* the window's pixels: right after the fonts, in the spare run */
#define PAD 24
#define COL_W ((TW - 3 * PAD) / 2)

enum { TRY_NONE, TRY_FILES, TRY_MEMORY, TRY_DISK, TRY_KEYS, TRY_CLIP, TRY_WX, TRY_TAMPER, TRY_POWER };

struct page {
    const char *title;
    int try;
    const char *leanos;
    const char *linux_;
    const char *left, *right;      /* the columns' headings, when not the usual ones */
};

static const struct page pages[] = {
    {"A guided tour", TRY_NONE,
     "This tour is an untrusted program from the SD card. On each page it really tries an "
     "attack, and you see what the kernel answered.",
     "Next: right arrow, Enter or a click. Back: left arrow. Close the window to stop."},
    {"Your files", TRY_FILES,
     "A program from the card reaches only its own folder and the files you hand it (run "
     "edit notes.txt). The kernel tells the file server who is asking; it cannot be faked.",
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
    {"What you copy", TRY_CLIP,
     "The display server keeps what you copy and gives it only to the window you paste into. "
     "No request reads it, and it takes a copy only from the window you pressed Ctrl+C in.",
     "On X11 any program can read the clipboard, or replace it, at any time, with no key "
     "pressed. Wayland gives it only to the window in front."},
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
     "The kernel's decisions are 1,400 lines of Lean, compiled into it, with 65 "
     "machine-checked theorems. 94 deliberate breaks: the proofs catch all.",
     "Tens of millions of lines of C, reviewed and tested, not proved. Thousands of kernel "
     "CVEs were published in 2024 alone."},
    {"What Linux does better", TRY_NONE,
     "leanos trusts what its proofs do not cover: its C machine layer, the Lean compiler, "
     "its model of the MMU, the hardware (see TRUST.md).",
     "Linux runs on almost anything, with drivers, networking and decades of hardening; "
     "switched on, its mitigations close many of these gaps.",
     "What leanos still trusts", "Where Linux is ahead"},
    {"The difference", TRY_NONE,
     "On leanos a program starts with nothing and is given what it needs. That is the "
     "default, and the proofs say it holds.",
     "On Linux a program starts with everything its user has, and you take away what you "
     "can. That is the end of the tour."},
};
#define NPAGES (int)(sizeof pages / sizeof pages[0])

struct tour {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    int page;
    char what[96];       /* what the attempt was */
    char said[96];       /* what the kernel said */
    int verdict;         /* 1 refused, 0 allowed, 2 a check (no attack), -1 no attempt */
};

static void copy(char *to, const char *from, int max) {
    int i = 0;
    for (; from[i] && i < max - 1; i++) to[i] = from[i];
    to[i] = 0;
}

static const char *said_of(u64 code) {
    return code == NO_CAP ? "no such capability" : code == BAD_ARG ? "not allowed" : code == OK ? "allowed" : "refused";
}

static void result(struct tour *t, const char *what, u64 code) {
    copy(t->what, what, sizeof t->what);
    copy(t->said, said_of(code), sizeof t->said);
    t->verdict = code != OK;
}

/* Really try this page's attack, and keep what the kernel said. */
static void attempt(struct tour *t) {
    t->verdict = -1;
    t->what[0] = t->said[0] = 0;
    switch (pages[t->page].try) {
    case TRY_FILES: {      /* your note, which nobody gave it; then its own folder, which it has */
        fs_path(&t->fs, "notes.txt");
        u64 note = fs_call(&t->fs, FS_READ, 0).x[1];
        u64 own = fs_write(&t->fs, "apps/tour/visited.txt", "yes", 3);
        result(t, "Read your note (notes.txt)", note == FS_DENIED && own == FS_OK ? BAD_ARG : OK);
        if (note == FS_DENIED && own == FS_OK)
            copy(t->said, "not given to it (its own folder, apps/tour: allowed)", sizeof t->said);
        break;
    }
    case TRY_MEMORY: {
        u64 a = sys2(SYS_MAP, 20, 1000).status;                       /* someone else's frames */
        u64 b = sys(SYS_DERIVE, 1, R, 0, 9, 0).status;                /* 9 pages of an 8-page run */
        result(t, "Map memory it was not given, and stretch its own", a != OK && b != OK ? BAD_ARG : OK);
        break;
    }
    case TRY_DISK:         /* through the only endpoint it holds, the display server's */
        result(t, "Read block 0 of the SD card", sys(SYS_BLOCKREAD, 4, 0, DATA, 0, 0).status);
        break;
    case TRY_KEYS:         /* every key arrives at the display server's endpoint */
        result(t, "Listen where every keystroke arrives", sys1(SYS_RECV, 4).status);
        break;
    case TRY_CLIP: {       /* ask for what was copied (no request does), then slip text in */
        struct res g = sys(SYS_CALL, 4, OP_COPY + 1, 0, 0, 0);
        struct res c = sys(SYS_CALL, 4, OP_COPY, 0x656b6166 /* "fake" */, 0, 0);
        int refused = g.status == OK && g.x[1] != 0 && c.status == OK && c.x[1] != 0;
        result(t, "Read the clipboard, and write it unasked", refused ? BAD_ARG : OK);
        if (refused) copy(t->said, "no such request; not asked", sizeof t->said);
        break;
    }
    case TRY_WX: {
        struct res d = sys(SYS_DERIVE, 1, R | W | X, 0, 1, 0);
        u64 bits = d.status == OK ? sys1(SYS_CAPINFO, d.x[1]).x[1] : 0;
        if (d.status == OK) sys1(SYS_DROP, d.x[1]);
        copy(t->what, "Ask for memory both writable and executable", sizeof t->what);
        struct line l = {.n = 0};
        put_s(&l, "got ");
        put_rights(&l, bits);
        put_s(&l, (bits & (W | X)) == (W | X) ? "" : ": never both");
        l.b[l.n] = 0;
        copy(t->said, l.b, sizeof t->said);
        t->verdict = (bits & (W | X)) != (W | X);
        break;
    }
    case TRY_TAMPER: {
        int ok = 0, bad = 0;
        for (u64 k = 0; k < NSLOTS; k++) {
            u64 v = sys1(SYS_BOOTINFO, k).x[1];
            ok += v == 1;
            bad += v == 2;
        }
        copy(t->what, "Check every program the manifest names", sizeof t->what);
        struct line l = {.n = 0};
        put_dec(&l, (u64)ok);
        put_s(&l, " match, ");
        put_dec(&l, (u64)bad);
        put_s(&l, " refused");
        l.b[l.n] = 0;
        copy(t->said, l.b, sizeof t->said);
        t->verdict = 2;
        break;
    }
    case TRY_POWER:
        result(t, "Switch the machine off", sys(SYS_POWER, 20, 0, 0, 0, 0).status);
        break;
    }
    struct line l = {.n = 0};
    put_s(&l, "tour: ");
    put_s(&l, pages[t->page].title);
    if (t->what[0]) {
        put_s(&l, ": ");
        put_s(&l, t->what);
        put_s(&l, " -> ");
        put_s(&l, t->verdict == 1 ? "refused, " : t->verdict == 0 ? "ALLOWED, " : "");
        put_s(&l, t->said);
    }
    put_s(&l, "\n");
    flush(&l);
}

/* A rounded label: text on a tinted pill, right-aligned at x1. */
static void pill(struct tour *t, int x1, int y, const char *s, unsigned bg, unsigned fg) {
    int w = font_width(&t->ui.small_bold, s) + 20;
    round_rect(&t->win, x1 - w, y, w, 22, 11, bg, 255);
    font_text(&t->win, &t->ui.small_bold, x1 - w + 10, y + 15, s, fg);
}

static void draw(struct tour *t) {
    struct surface *s = &t->win;
    const struct page *p = &pages[t->page];
    struct ui *u = &t->ui;
    int last = t->page == NPAGES - 1, first = t->page == 0;
    fill(s, 0, 0, TW, TH, rgb(252, 252, 254));
    fill(s, 0, 0, TW, 4, rgb(58, 110, 230));

    /* step, title, progress */
    struct line l = {.n = 0};
    put_s(&l, first ? "GUIDED TOUR" : "STEP ");
    if (!first) {
        put_dec(&l, (u64)t->page);
        put_s(&l, " OF ");
        put_dec(&l, (u64)(NPAGES - 1));
    }
    l.b[l.n] = 0;
    font_text(s, &u->small_bold, PAD, 30, l.b, rgb(58, 110, 230));
    font_text(s, &u->title, PAD, 62, first ? "Why leanos is harder to attack" : p->title, rgb(22, 24, 34));
    for (int i = 0; i < NPAGES; i++) {
        int x = TW - PAD - (NPAGES - i) * 12 + 4;
        round_rect(s, x, 22, i == t->page ? 8 : 6, i == t->page ? 8 : 6, 4,
                   i == t->page ? rgb(58, 110, 230) : i < t->page ? rgb(160, 180, 230) : rgb(214, 218, 228), 255);
    }

    int y = 80;
    if (t->what[0]) {
        /* the live attempt */
        unsigned edge = t->verdict == 1 ? rgb(46, 170, 100) : t->verdict == 0 ? rgb(220, 60, 50) : rgb(58, 110, 230);
        round_rect(s, PAD, y, TW - 2 * PAD, 54, 12, rgb(244, 246, 250), 255);
        round_rect(s, PAD, y, 5, 54, 2, edge, 255);
        font_text(s, &u->small_bold, PAD + 18, y + 20, "LIVE, JUST NOW, FROM THIS PROGRAM", rgb(130, 136, 152));
        font_text(s, &u->medium, PAD + 18, y + 42, t->what, rgb(30, 32, 42));
        int px = TW - PAD - 14;
        if (t->verdict == 1) pill(t, px, y + 16, "REFUSED", rgb(222, 244, 230), rgb(24, 128, 64));
        else if (t->verdict == 0) pill(t, px, y + 16, "ALLOWED", rgb(252, 226, 224), rgb(190, 40, 30));
        else pill(t, px, y + 16, "CHECKED", rgb(226, 234, 252), rgb(40, 80, 180));
        int sw = font_width(&u->small, t->said);
        font_text(s, &u->small, px - sw, y + 48, t->said, rgb(120, 126, 140));
        y += 72;
    } else {
        y += 10;
    }

    /* the two columns */
    int lx = PAD, rx = PAD * 2 + COL_W;
    round_rect(s, lx, y, 8, 8, 4, rgb(58, 110, 230), 255);
    font_text(s, &u->bold, lx + 16, y + 9, p->left ? p->left : first ? "What this is" : "On leanos", rgb(58, 110, 230));
    round_rect(s, rx, y, 8, 8, 4, rgb(214, 130, 40), 255);
    font_text(s, &u->bold, rx + 16, y + 9,
              p->right ? p->right : first ? "How to use it" : last ? "On Linux" : "On a typical Linux desktop",
              rgb(190, 110, 30));
    text_wrap(s, &u->body, lx, y + 34, COL_W, 21, p->leanos, rgb(40, 42, 54));
    text_wrap(s, &u->body, rx, y + 34, COL_W, 21, p->linux_, rgb(70, 72, 84));

    const char *nav = t->page == 0 ? "Next: right arrow, Enter or a click" : last ? "Left arrow: back" : "Left arrow: back    Right arrow or Enter: next";
    font_text(s, &u->small, TW - PAD - font_width(&u->small, nav), TH - 14, nav, rgb(150, 154, 166));
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
    ui_load(&t->ui, app_assets());
    t->win = app_surface_at(WIN_OFFSET, TW, TH);
    fs_init(&t->fs, SPARE_PAGE);
    t->page = 0;
    t->what[0] = 0;
    t->verdict = -1;
    draw(t);
    u64 opened = app_open_at(WIN_OFFSET, TW, TH, "Tour");
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
