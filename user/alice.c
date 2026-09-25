/* alice's Notes. She draws a window in her own memory, hands the display server a
   read-only capability to exactly those pages, and then asks it, over and over, for her
   next event. Keys she is given go into the note, and the note is saved to the file server
   as notes.txt after every change, so it is back when Notes starts again. She also keeps a
   secret in her data pages and checks that nobody changes it.

   Copy (Ctrl+C) takes the whole note; a paste (Ctrl+V) goes at its end, where the caret is. */
#include "app.h"
#include "fs.h"

#define WIN_W 300
#define WIN_H 200
#define WIN_PAGES ((WIN_W * WIN_H * 4 + 4095) / 4096)
#define WIN_OFFSET 16     /* pages into the spare run (SPARE_PAGE): assets first, then the window's pixels */
enum { F_HEAD = 5, F_TEXT = 6, F_SMALL = 3 };

struct notes {
    u64 secret;
    char text[400];
    int len;
    struct font head, body, small;
    struct fs_client fs;
};

static void draw(struct surface *win, struct notes *n) {
    fill(win, 0, 0, WIN_W, WIN_H, rgb(255, 255, 255));
    font_text(win, &n->head, 18, 32, "Today", rgb(28, 28, 32));
    fill(win, 18, 44, WIN_W - 36, 1, rgb(232, 232, 236));
    /* The note, wrapped at the window's edge, then a caret. */
    int x = 18, y = 72, right = WIN_W - 18;
    for (int i = 0; i < n->len; i++) {
        char c = n->text[i];
        char s[2] = {c, 0};
        int cw = font_width(&n->body, s);
        if (c == '\n' || x + cw > right) {
            x = 18;
            y += 24;
            if (c == '\n' || c == ' ') continue;
        }
        x = font_text(win, &n->body, x, y, s, rgb(40, 40, 48));
    }
    fill(win, x + 1, y - 15, 2, 19, rgb(58, 110, 230));
    font_text(win, &n->small, 18, WIN_H - 14, "Only alice can write this page.", rgb(160, 160, 170));
}

__attribute__((section(".text.start"))) void _start(void) {
    struct notes *n = (struct notes *)DATA;
    n->secret = 0x5ec12e7;
    n->len = 0;
    struct line l = {.n = 0};
    put_s(&l, "alice: wrote secret ");
    put_hex(&l, n->secret);
    put_s(&l, " to my data page\n");
    flush(&l);

    sys2(SYS_MAP, SPARE, SPARE_PAGE);
    const unsigned char *assets = (const unsigned char *)PAGE(SPARE_PAGE);
    fs_init(&n->fs, SPARE_PAGE);
    long saved = fs_read(&n->fs, "notes.txt");
    if (saved >= 0) {
        const char *d = fs_data(&n->fs);
        for (long i = 0; i < saved && i < 399; i++) n->text[n->len++] = d[i];
        put_s(&l, "alice: loaded notes.txt, ");
        put_dec(&l, (u64)n->len);
        put_s(&l, " bytes\n");
    } else {
        put_s(&l, "alice: no saved note yet\n");
    }
    flush(&l);
    n->head = font_of(assets, F_HEAD);
    n->body = font_of(assets, F_TEXT);
    n->small = font_of(assets, F_SMALL);
    struct surface win = surface_of((unsigned *)PAGE(SPARE_PAGE + WIN_OFFSET), WIN_W, WIN_H);
    draw(&win, n);

    /* A read-only capability to exactly the window's pages, and a title. */
    struct res ro = sys(SYS_DERIVE, SPARE, R, WIN_OFFSET, WIN_PAGES, 0);
    u64 title = 0;
    const char *t = "Notes";
    for (int i = 0; t[i]; i++) title |= (u64)(unsigned char)t[i] << (8 * i);
    struct res opened = sys(SYS_CALL, ENDPOINT, OP_OPEN, (u64)WIN_W << 16 | WIN_H, title, ro.x[1] + 1);
    put_s(&l, "alice: opened a ");
    put_dec(&l, WIN_W);
    put_s(&l, "x");
    put_dec(&l, WIN_H);
    put_s(&l, " window, read-only, ");
    put_dec(&l, WIN_PAGES);
    put_s(&l, " pages");
    put_s(&l, outcome(opened.status == OK && opened.x[1] == 0 ? OK : BAD_ARG));
    put_s(&l, "\n");
    flush(&l);

    u64 dirty = 0;
    int pasted = 0;
    for (;;) {
        struct res e = sys(SYS_CALL, ENDPOINT, OP_WAIT, dirty, 0, 0);
        dirty = 0;
        if (n->secret != 0x5ec12e7) {
            put_s(&l, "alice: SECRET CHANGED\n");
            flush(&l);
        }
        if (e.status != OK || e.x[1] == EV_NONE) {   /* no event: ask again in a moment (app_wait) */
            sleep_ms(WAIT_AGAIN_MS);
            continue;
        }
        if (e.status == OK && e.x[1] == EV_CLOSE) {
            put_s(&l, "alice: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.status == OK && e.x[1] == EV_COPY) {
            u64 st = app_copy(n->text, (u64)n->len);
            put_s(&l, "alice: copied ");
            put_dec(&l, (u64)n->len);
            put_s(&l, " bytes");
            put_s(&l, outcome(st));
            put_s(&l, "\n");
            flush(&l);
            continue;
        }
        if (e.status == OK && e.x[1] == EV_PASTE) {
            /* a run of events: the text goes in as it comes, and is saved when the last is in */
            struct event ev = {EV_PASTE, e.x[2], e.x[3]};
            char piece[16];
            int k = paste_text(ev, piece);
            for (int i = 0; i < k; i++) {
                char c = piece[i] == '\r' ? '\n' : piece[i];
                if (n->len < 399 && (c == '\n' || (c >= 32 && c < 127))) { n->text[n->len++] = c; pasted++; }
            }
            if (k == 16) continue;
            put_s(&l, "alice: pasted ");
            put_dec(&l, (u64)pasted);
            put_s(&l, " bytes\n");
            flush(&l);
            pasted = 0;
        } else if (e.status != OK || e.x[1] != EV_KEY) {
            continue;
        } else {
            char c = (char)e.x[2];
            if ((c == 8 || c == 127) && n->len > 0) n->len--;
            else if (c == '\r' || c == '\n') { if (n->len < 399) n->text[n->len++] = '\n'; }
            else if (c >= 32 && c < 127 && n->len < 399) n->text[n->len++] = c;
            else continue;
        }
        draw(&win, n);
        dirty = 1;
        if (fs_write(&n->fs, "notes.txt", n->text, (u64)n->len) != FS_OK) {
            put_s(&l, "alice: could not save notes.txt\n");
            flush(&l);
        }
    }
}
