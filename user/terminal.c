/* Terminal. A line of text in, an answer out. Every answer comes from asking the kernel
   (which task this is, what capabilities it holds, what the boot checks found) or the file
   server (ls, cat, write, rm). It holds no more authority than any app: its own frames, and
   send + grant to the display server and the file server. */
#include "app.h"
#include "fs.h"
#include "elf.h"

/* Terminal's launch capabilities for the open slots, which run programs from the SD card. */
#define LAUNCH_OPEN 6
#define OPEN_FIRST 10
#define OPEN_SLOTS 6
#define IMAGE_OFFSET 192   /* the program image, in the spare run: pages 192-207 */

#define TW 460
#define TH 272
#define PAD 12
#define ROWS 13
#define COLS 52
#define CMD_MAX 160      /* a command line may be longer than the window; it scrolls */
#define LINE_H 19
enum { F_MONO = 1 };

struct term {
    char text[ROWS][COLS + 1];  /* scrollback, oldest first; the prompt line is drawn below */
    unsigned char kind[ROWS];   /* 0 output, 1 a command that was typed */
    int n;
    char cmd[CMD_MAX + 1];
    int len;
    struct font mono;
    struct surface win;
    struct fs_client fs;
};

static const unsigned BG = 0x171a21, FG = 0xdde2ec, DIM = 0x8a93a6, GREEN = 0x7fd1a0;

static void push(struct term *t, const char *s, u64 n, int kind) {
    while (1) {
        u64 take = n > COLS ? COLS : n;
        if (t->n == ROWS) {
            for (int i = 1; i < ROWS; i++) {
                for (int j = 0; j <= COLS; j++) t->text[i - 1][j] = t->text[i][j];
                t->kind[i - 1] = t->kind[i];
            }
            t->n--;
        }
        for (u64 j = 0; j < take; j++) t->text[t->n][j] = s[j];
        t->text[t->n][take] = 0;
        t->kind[t->n++] = (unsigned char)kind;
        if (n <= COLS) return;
        s += take;
        n -= take;
    }
}

static void out(struct term *t, struct line *l) {
    push(t, l->b, l->n, 0);
    l->n = 0;
}

static void say(struct term *t, const char *s) { push(t, s, slen(s), 0); }

static void draw(struct term *t) {
    struct surface *s = &t->win;
    fill(s, 0, 0, TW, TH, BG);
    int y = PAD + 13;
    /* the scrollback shows the last ROWS - 1 lines, so the prompt always fits */
    int first = t->n > ROWS - 1 ? t->n - (ROWS - 1) : 0;
    for (int i = first; i < t->n; i++, y += LINE_H) {
        int x = PAD;
        if (t->kind[i]) x = font_text(s, &t->mono, x, y, "$ ", GREEN);
        font_text(s, &t->mono, x, y, t->text[i], t->kind[i] ? FG : DIM);
    }
    int x = font_text(s, &t->mono, PAD, y, "$ ", GREEN);
    t->cmd[t->len] = 0;
    /* the end of the line, if it is wider than the window */
    int from = t->len > COLS - 3 ? t->len - (COLS - 3) : 0;
    x = font_text(s, &t->mono, x, y, t->cmd + from, FG);
    fill(s, x + 1, y - 12, 8, 16, GREEN);
}

static int starts(const char *s, const char *w) {
    while (*w) if (*s++ != *w++) return 0;
    return *s == 0 || *s == ' ';
}

static void pad_to(struct line *l, u64 col) { while (l->n < col) l->b[l->n++] = ' '; }

static void hex8(struct line *l, u64 v) {
    for (int i = 28; i >= 0; i -= 4) l->b[l->n++] = "0123456789abcdef"[(v >> i) & 15];
}

static void cmd_caps(struct term *t, struct line *l) {
    int count = 0;
    for (u64 i = 0; i < 32; i++) {
        struct res r = sys1(SYS_CAPINFO, i);
        if (r.status != OK) break;
        count++;
        put_s(l, "cap ");
        put_dec(l, i);
        pad_to(l, 7);
        if (r.x[2] == 0) {
            put_s(l, "frames    ");
            put_dec(l, r.x[3]);
            put_s(l, r.x[3] == 1 ? " page  " : " pages ");
            put_rights(l, r.x[1]);
        } else if (r.x[2] == 1) {
            put_s(l, "endpoint  ");
            put_ep_rights(l, r.x[1]);
        } else if (r.x[2] == 2) {
            put_s(l, "interrupt line ");
            put_dec(l, r.x[3]);
        } else {
            put_s(l, "starts ");
            put_s(l, slot_name(r.x[3]));
        }
        out(t, l);
    }
    put_s(l, "terminal: caps -> ");
    put_dec(l, (u64)count);
    put_s(l, " capabilities\n");
    flush(l);
}

static void cmd_boot(struct term *t, struct line *l) {
    int verified = 0;
    for (u64 k = 0; k < NSLOTS; k++) {
        struct res r = sys1(SYS_BOOTINFO, k);
        if (r.status != OK) break;
        put_s(l, slot_name(k));
        pad_to(l, 16);
        if (r.x[1] == 1) { put_s(l, "verified "); hex8(l, r.x[2]); verified++; }
        else if (r.x[1] == 2) put_s(l, "REFUSED  ");
        else put_s(l, "not loaded");
        pad_to(l, 35);
        put_s(l, r.x[4] == 1 ? "running" : r.x[4] == 2 ? "stopped" : "");
        out(t, l);
    }
    put_s(l, "terminal: boot -> ");
    put_dec(l, (u64)verified);
    put_s(l, " verified\n");
    flush(l);
}

static const char *fs_error(u64 code) {
    return code == FS_NOT_FOUND ? "no such file" : code == FS_FULL ? "no room"
         : code == FS_NO_SERVER ? "the file server did not answer" : "not a valid name";
}

/* The first word of `c` into `word`; returns the rest. */
static const char *word_of(const char *c, char *word, int max) {
    while (*c == ' ') c++;
    int n = 0;
    while (*c && *c != ' ' && n < max) word[n++] = *c++;
    word[n] = 0;
    while (*c == ' ') c++;
    return c;
}

static void fs_log(struct line *l, const char *cmd, const char *name, const char *result) {
    put_s(l, "terminal: ");
    put_s(l, cmd);
    if (name) { put_s(l, " "); put_s(l, name); }
    put_s(l, " -> ");
    put_s(l, result);
    put_s(l, "\n");
    flush(l);
}

static void cmd_ls(struct term *t, struct line *l) {
    long n = fs_list(&t->fs);
    if (n < 0) { say(t, "the file server did not answer"); fs_log(l, "ls", 0, "no answer"); return; }
    const struct fs_entry *e = fs_entries(&t->fs);
    for (long i = 0; i < n; i++) {
        put_s(l, e[i].name);
        pad_to(l, 30);
        put_dec(l, e[i].size);
        put_s(l, " bytes");
        out(t, l);
    }
    if (n == 0) say(t, "no files");
    put_s(l, "terminal: ls -> ");
    put_dec(l, (u64)n);
    put_s(l, n == 1 ? " file\n" : " files\n");
    flush(l);
}

static void cmd_cat(struct term *t, struct line *l, const char *args) {
    char name[FS_NAME_MAX + 1];
    word_of(args, name, FS_NAME_MAX);
    long n = fs_read(&t->fs, name);
    if (n < 0) { say(t, "no such file"); fs_log(l, "cat", name, "no such file"); return; }
    const char *d = fs_data(&t->fs);
    /* line by line; long lines wrap in push() */
    long start = 0;
    for (long i = 0; i <= n; i++)
        if (i == n || d[i] == '\n') {
            if (i > start || i < n) push(t, d + start, (u64)(i - start), 0);
            start = i + 1;
        }
    put_s(l, "terminal: cat ");
    put_s(l, name);
    put_s(l, " -> ");
    put_dec(l, (u64)n);
    put_s(l, " bytes\n");
    flush(l);
}

static void cmd_write(struct term *t, struct line *l, const char *args) {
    char name[FS_NAME_MAX + 1];
    const char *text = word_of(args, name, FS_NAME_MAX);
    u64 st = fs_write(&t->fs, name, text, slen(text));
    say(t, st == FS_OK ? "saved" : fs_error(st));
    fs_log(l, "write", name, st == FS_OK ? "ok" : fs_error(st));
}

static void cmd_rm(struct term *t, struct line *l, const char *args) {
    char name[FS_NAME_MAX + 1];
    word_of(args, name, FS_NAME_MAX);
    u64 st = fs_delete(&t->fs, name);
    say(t, st == FS_OK ? "removed" : fs_error(st));
    fs_log(l, "rm", name, st == FS_OK ? "ok" : fs_error(st));
}

/* Every program slot and what the kernel says about it. */
static void cmd_ps(struct term *t, struct line *l) {
    int running = 0;
    for (u64 k = 0; k < NSLOTS; k++) {
        struct res r = sys1(SYS_BOOTINFO, k);
        if (r.status != OK) break;
        put_dec(l, k);
        pad_to(l, 4);
        put_s(l, slot_name(k));
        pad_to(l, 20);
        put_s(l, r.x[4] == 1 ? "running" : r.x[4] == 2 ? "stopped" : "-");
        if (r.x[1] == 3) put_s(l, "  (from the SD card)");
        out(t, l);
        running += r.x[4] == 1;
    }
    put_s(l, "terminal: ps -> ");
    put_dec(l, (u64)running);
    put_s(l, " running\n");
    flush(l);
}

/* Read a program from the SD card, make its image, and start it in a free open slot. */
static void cmd_run(struct term *t, struct line *l, const char *args) {
    char name[FS_NAME_MAX + 1];
    word_of(args, name, FS_NAME_MAX);
    if (name[0] && app_raise(name)) {
        say(t, "already open: brought it to the front");
        fs_log(l, "run", name, "already open");
        return;
    }
    long n = fs_read(&t->fs, name);
    if (n < 0) { say(t, "no such file"); fs_log(l, "run", name, "no such file"); return; }
    unsigned char *image = (unsigned char *)PAGE(SPARE_PAGE + IMAGE_OFFSET);
    u64 len = 0;
    const char *why = elf_image((const unsigned char *)fs_data(&t->fs), (u64)n, image, &len);
    if (why) {
        put_s(l, name);
        put_s(l, ": ");
        put_s(l, why);
        out(t, l);
        fs_log(l, "run", name, why);
        return;
    }
    /* its icon, if the card has NAME.icon, rides along in the image */
    char iconname[FS_NAME_MAX + 6];
    int m = 0;
    for (; name[m] && m < FS_NAME_MAX; m++) iconname[m] = name[m];
    const char *ext = ".icon";
    for (int x = 0; ext[x]; x++) iconname[m++] = ext[x];
    iconname[m] = 0;
    long isize = fs_read(&t->fs, iconname);
    image_add_icon(image, &len, (const unsigned char *)fs_data(&t->fs), isize > 0 ? (u64)isize : 0, name);
    for (int i = 0; i < OPEN_SLOTS; i++) {
        if (sys1(SYS_BOOTINFO, OPEN_FIRST + (u64)i).x[4] == 1) continue;   /* in use */
        struct res r = sys(SYS_EXEC, LAUNCH_OPEN + (u64)i, (u64)image, len, 0, 0);
        if (r.status != OK) continue;
        put_s(l, "started ");
        put_s(l, name);
        put_s(l, " in slot ");
        put_dec(l, OPEN_FIRST + (u64)i);
        out(t, l);
        put_s(l, "terminal: run ");
        put_s(l, name);
        put_s(l, " -> slot ");
        put_dec(l, OPEN_FIRST + (u64)i);
        put_s(l, "\n");
        flush(l);
        return;
    }
    say(t, "no free slot: close a program first");
    fs_log(l, "run", name, "no free slot");
}

static void run(struct term *t, struct line *l) {
    const char *c = t->cmd;
    while (*c == ' ') c++;
    if (!*c) return;
    if (starts(c, "help")) {
        say(t, "whoami caps boot ps uptime echo clear exit");
        say(t, "ls, cat FILE, write FILE TEXT, rm FILE, run PROGRAM");
        say(t, "tour: why leanos is harder to attack than Linux");
    } else if (starts(c, "whoami")) {
        u64 me = sys0(SYS_WHOAMI).x[1];
        put_s(l, "task ");
        put_dec(l, me);
        put_s(l, " (");
        put_s(l, slot_name(me));
        put_s(l, "), no root, no users: only capabilities");
        out(t, l);
    } else if (starts(c, "caps")) {
        cmd_caps(t, l);
    } else if (starts(c, "boot")) {
        cmd_boot(t, l);
    } else if (starts(c, "ps")) {
        cmd_ps(t, l);
    } else if (starts(c, "run")) {
        cmd_run(t, l, c + 3);
    } else if (starts(c, "tour")) {
        cmd_run(t, l, " tour");
    } else if (starts(c, "ls")) {
        cmd_ls(t, l);
    } else if (starts(c, "cat")) {
        cmd_cat(t, l, c + 3);
    } else if (starts(c, "write")) {
        cmd_write(t, l, c + 5);
    } else if (starts(c, "rm")) {
        cmd_rm(t, l, c + 2);
    } else if (starts(c, "uptime")) {
        u64 ms = millis();
        put_s(l, "up ");
        put_dec(l, ms / 1000);
        put_s(l, ".");
        put_dec(l, ms / 100 % 10);
        put_s(l, " s");
        out(t, l);
    } else if (starts(c, "echo")) {
        c += 4;
        if (*c == ' ') c++;
        say(t, c);
    } else if (starts(c, "clear")) {
        t->n = 0;
    } else if (starts(c, "exit")) {
        put_s(l, "terminal: exit\n");
        flush(l);
        exit_task();
    } else {
        put_s(l, "not a command: ");
        put_s(l, c);
        out(t, l);
    }
}

__attribute__((section(".text.start"))) void _start(void) {
    struct term *t = (struct term *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    t->mono = font_of(assets, F_MONO);
    t->win = app_surface(TW, TH);
    fs_init(&t->fs, SPARE_PAGE);
    t->n = t->len = 0;
    say(t, "leanos terminal. Type help, or tour.");
    draw(t);
    u64 opened = app_open(TW, TH, "Terminal");
    put_s(&l, "terminal: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "terminal: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind != EV_KEY) continue;
        char ch = (char)e.a;
        if ((ch == 8 || ch == 127) && t->len > 0) t->len--;
        else if (ch == '\r' || ch == '\n') {
            t->cmd[t->len] = 0;
            push(t, t->cmd, (u64)t->len, 1);
            run(t, &l);
            t->len = 0;
        } else if (ch >= 32 && ch < 127 && t->len < CMD_MAX) t->cmd[t->len++] = ch;
        else continue;
        draw(t);
        dirty = 1;
    }
}
