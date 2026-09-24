/* Terminal. A line of text in, an answer out. Every answer comes from asking the kernel
   (which task this is, what capabilities it holds, what the boot checks found) or the file
   server (ls, cat, write, rm). It holds no more authority than any app: its own frames, and
   send + grant to the display server and the file server. */
#include "app.h"
#include "fs.h"
#include "elfload.h"
#include "net.h"
#include "date.h"

/* Terminal's launch capabilities for the open slots, which run programs from the SD card. */
#define LAUNCH_OPEN 6
#define OPEN_FIRST 10
#define OPEN_SLOTS 6
#define IMAGE_OFFSET 192   /* the program image, in the spare run: pages 192-207 */
#define FILE_OFFSET 208    /* a program's file as read from the card: pages 208-223, 64 KiB */

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
    struct net_client net;
    char cwd[FS_PATH_MAX + 1];  /* the folder commands are in: "" is the top */
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
         : code == FS_NO_SERVER ? "the file server did not answer" : code == FS_EXISTS ? "already there"
         : code == FS_NOT_EMPTY ? "the folder is not empty" : code == FS_NOT_DIR ? "not a folder"
         : code == FS_IS_DIR ? "a folder" : code == FS_IO ? "the card did not answer" : "not a valid name";
}

/* A path as the file server takes it: `arg` from the top folder if it starts with '/',
   else from the current folder. */
static void resolve(struct term *t, const char *arg, char *out) {
    int n = 0;
    if (arg[0] != '/')
        for (int i = 0; t->cwd[i] && n < FS_PATH_MAX; i++) out[n++] = t->cwd[i];
    else arg++;
    if (n && arg[0] && n < FS_PATH_MAX) out[n++] = '/';
    for (int i = 0; arg[i] && n < FS_PATH_MAX; i++) out[n++] = arg[i];
    out[n] = 0;
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

static void cmd_ls(struct term *t, struct line *l, const char *args) {
    char arg[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, arg, FS_PATH_MAX);
    resolve(t, arg, path);
    u64 total = 0, from = 0;
    long shown = 0;
    for (;;) {
        long n = fs_list_dir(&t->fs, path, from, &total);
        if (n < 0) { say(t, "no such folder"); fs_log(l, "ls", arg[0] ? arg : 0, "no such folder"); return; }
        const struct fs_entry *e = fs_entries(&t->fs);
        for (long i = 0; i < n; i++) {
            put_s(l, e[i].name);
            if (e[i].kind == FS_DIR) {
                put_s(l, "/");
                out(t, l);
                continue;
            }
            pad_to(l, 30);
            put_dec(l, e[i].size);
            put_s(l, " bytes");
            out(t, l);
        }
        shown += n;
        from += (u64)n;
        if (n == 0 || from >= total) break;
    }
    if (shown == 0) say(t, "nothing here");
    put_s(l, "terminal: ls");
    if (arg[0]) { put_s(l, " "); put_s(l, arg); }
    put_s(l, " -> ");
    put_dec(l, (u64)shown);
    put_s(l, shown == 1 ? " file\n" : " files\n");
    flush(l);
}

static void cmd_cat(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 size = 0, off = 0;
    for (;;) {
        long n = fs_read_at(&t->fs, path, off, &size);
        if (n < 0) { say(t, "no such file"); fs_log(l, "cat", name, "no such file"); return; }
        const char *d = fs_data(&t->fs);
        /* line by line; long lines wrap in push() */
        long start = 0;
        for (long i = 0; i <= n; i++)
            if (i == n || d[i] == '\n') {
                if (i > start || i < n) push(t, d + start, (u64)(i - start), 0);
                start = i + 1;
            }
        off += (u64)n;
        if (n == 0 || off >= size) break;
    }
    put_s(l, "terminal: cat ");
    put_s(l, name);
    put_s(l, " -> ");
    put_dec(l, off);
    put_s(l, " bytes\n");
    flush(l);
}

static void cmd_write(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    const char *text = word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = fs_write(&t->fs, path, text, slen(text));
    say(t, st == FS_OK ? "saved" : fs_error(st));
    fs_log(l, "write", name, st == FS_OK ? "ok" : fs_error(st));
}

static void cmd_rm(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = fs_delete(&t->fs, path);
    say(t, st == FS_OK ? "removed" : fs_error(st));
    fs_log(l, "rm", name, st == FS_OK ? "ok" : fs_error(st));
}

static void cmd_mkdir(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = fs_mkdir(&t->fs, path);
    say(t, st == FS_OK ? "made" : fs_error(st));
    fs_log(l, "mkdir", name, st == FS_OK ? "ok" : fs_error(st));
}

static void cmd_mv(struct term *t, struct line *l, const char *args) {
    char a[FS_PATH_MAX + 1], b[FS_PATH_MAX + 1], pa[FS_PATH_MAX + 1], pb[FS_PATH_MAX + 1];
    word_of(word_of(args, a, FS_PATH_MAX), b, FS_PATH_MAX);
    resolve(t, a, pa);
    resolve(t, b, pb);
    u64 kind = fs_stat(&t->fs, pb, 0);
    if (kind == FS_DIR) {                  /* into a folder: keep the name */
        const char *last = a;
        for (const char *p = a; *p; p++) if (*p == '/') last = p + 1;
        int n = slen(pb);
        if (n + 1 + (int)slen(last) <= FS_PATH_MAX) { pb[n] = '/'; for (int i = 0; ; i++) { pb[n + 1 + i] = last[i]; if (!last[i]) break; } }
    }
    u64 st = fs_rename(&t->fs, pa, pb);
    say(t, st == FS_OK ? "moved" : fs_error(st));
    fs_log(l, "mv", a, st == FS_OK ? "ok" : fs_error(st));
}

static void cmd_cd(struct term *t, struct line *l, const char *args) {
    char arg[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, arg, FS_PATH_MAX);
    if (!arg[0] || (arg[0] == '/' && !arg[1])) {
        t->cwd[0] = 0;
    } else if (arg[0] == '.' && arg[1] == '.' && !arg[2]) {
        int n = slen(t->cwd);
        while (n > 0 && t->cwd[n - 1] != '/') n--;
        t->cwd[n > 0 ? n - 1 : 0] = 0;
    } else {
        resolve(t, arg, path);
        if (fs_stat(&t->fs, path, 0) != FS_DIR) {
            say(t, "no such folder");
            fs_log(l, "cd", arg, "no such folder");
            return;
        }
        for (int i = 0; ; i++) { t->cwd[i] = path[i]; if (!path[i]) break; }
    }
    put_s(l, "/");
    put_s(l, t->cwd);
    out(t, l);
    fs_log(l, "cd", arg[0] ? arg : "/", "ok");
}

/* fill NAME KB CHAR: a file of KB kilobytes of CHAR, written in pieces to NAME.tmp and then
   put in place by one rename, which the file server does in one step: whatever happens,
   NAME is the old file or the new one, never half of each. */
static void cmd_fill(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], num[12], ch[4], path[FS_PATH_MAX + 1], tmp[FS_PATH_MAX + 1];
    word_of(word_of(word_of(args, name, FS_PATH_MAX - 4), num, 10), ch, 2);
    u64 kb = 0;
    for (int i = 0; num[i] >= '0' && num[i] <= '9'; i++) kb = kb * 10 + (u64)(num[i] - '0');
    resolve(t, name, path);
    int n = slen(path);
    for (int i = 0; i <= n; i++) tmp[i] = path[i];
    tmp[n] = '.'; tmp[n + 1] = 't'; tmp[n + 2] = 'm'; tmp[n + 3] = 'p'; tmp[n + 4] = 0;
    char *piece = (char *)PAGE(SPARE_PAGE + FILE_OFFSET);
    for (u64 i = 0; i < 16384; i++) piece[i] = ch[0] ? ch[0] : 'x';
    u64 st = fs_write(&t->fs, tmp, piece, 0);
    for (u64 off = 0; st == FS_OK && off < kb * 1024; off += 16000) {
        u64 take = kb * 1024 - off < 16000 ? kb * 1024 - off : 16000;
        st = fs_write_at(&t->fs, tmp, off, piece, take);
    }
    if (st == FS_OK) st = fs_rename(&t->fs, tmp, path);
    say(t, st == FS_OK ? "filled" : fs_error(st));
    fs_log(l, "fill", name, st == FS_OK ? "ok" : fs_error(st));
}

/* verify NAME: whether every byte of NAME is the same (what fill makes). */
static void cmd_verify(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 size = 0, off = 0;
    char first = 0;
    int mixed = 0;
    for (;;) {
        long n = fs_read_at(&t->fs, path, off, &size);
        if (n < 0) { say(t, "no such file"); fs_log(l, "verify", name, "no such file"); return; }
        const char *d = fs_data(&t->fs);
        for (long i = 0; i < n; i++) {
            if (!off && !i) first = d[0];
            if (d[i] != first) mixed = 1;
        }
        off += (u64)n;
        if (n == 0 || off >= size) break;
    }
    put_dec(l, off);
    put_s(l, mixed ? " bytes, mixed" : " bytes, all the same");
    out(t, l);
    put_s(l, "terminal: verify ");
    put_s(l, name);
    put_s(l, " -> ");
    put_dec(l, off);
    if (mixed) put_s(l, " bytes, mixed\n");
    else {
        put_s(l, " bytes of '");
        char c[2] = {first ? first : '-', 0};
        put_s(l, c);
        put_s(l, "'\n");
    }
    flush(l);
}

/* ---- the network (the USB driver serves it) ---- */

static const char *net_error(u64 code) {
    return code == NET_NO_DEVICE ? "no network adapter" : code == NET_NO_ADDRESS ? "no address from the network"
         : code == NET_NO_HOST ? "no such host" : code == NET_NO_ANSWER ? "no answer"
         : code == NET_UNSUPPORTED ? "only http:// (no https yet)" : code == NET_NO_SERVICE ? "the network service did not answer"
         : "not understood";
}

static void put_ip(struct line *l, unsigned ip) {
    for (int k = 3; k >= 0; k--) { put_dec(l, (ip >> (8 * k)) & 255); if (k) put_s(l, "."); }
}

static void cmd_ip(struct term *t, struct line *l) {
    struct res r = net_call(&t->net, NET_INFO, 0, 0);
    const struct net_info *i = (const struct net_info *)net_data(&t->net);
    if (r.x[1] != NET_OK || !i->device) {
        say(t, r.x[1] != NET_OK ? net_error(r.x[1]) : "no network adapter");
        fs_log(l, "ip", 0, "no network");
        return;
    }
    if (!i->up) { say(t, "no address yet"); fs_log(l, "ip", 0, "no address"); return; }
    put_s(l, "address ");
    put_ip(l, i->ip);
    put_s(l, ", gateway ");
    put_ip(l, i->gateway);
    out(t, l);
    put_s(l, "DNS ");
    put_ip(l, i->dns);
    put_s(l, ", MAC ");
    for (int k = 0; k < 6; k++) {
        char c[3] = {"0123456789abcdef"[i->mac[k] >> 4], "0123456789abcdef"[i->mac[k] & 15], 0};
        if (k) put_s(l, ":");
        put_s(l, c);
    }
    out(t, l);
    put_s(l, "terminal: ip -> ");
    put_ip(l, i->ip);
    put_s(l, "\n");
    flush(l);
}

static void cmd_ping(struct term *t, struct line *l, const char *args) {
    char host[128];
    word_of(args, host, 127);
    int answered = 0;
    for (int k = 0; k < 4; k++) {
        struct res r = net_call(&t->net, NET_PING, 0, host);
        if (r.x[1] != NET_OK) { say(t, net_error(r.x[1])); if (r.x[1] != NET_NO_ANSWER) break; continue; }
        answered++;
        put_s(l, "answer from ");
        put_ip(l, (unsigned)r.x[3]);
        put_s(l, " in ");
        put_dec(l, r.x[2]);
        put_s(l, " ms");
        out(t, l);
    }
    put_s(l, "terminal: ping ");
    put_s(l, host);
    put_s(l, " -> ");
    put_dec(l, (u64)answered);
    put_s(l, " of 4 answered\n");
    flush(l);
}

/* date: the time of day the kernel keeps (set from the network; UTC). */
static void cmd_date(struct term *t, struct line *l) {
    u64 secs = sys0(SYS_TIME).x[6];
    if (!secs) {
        say(t, "the time is not known: no time server has answered (try ntp)");
        put_s(l, "terminal: date -> not known\n");
        flush(l);
        return;
    }
    put_date(l, secs);
    out(t, l);
    put_s(l, "terminal: date -> ");
    put_date(l, secs);
    put_s(l, "\n");
    flush(l);
}

/* ntp [HOST[:PORT]]: set the time of day from a time server (pool.ntp.org by default). */
static void cmd_ntp(struct term *t, struct line *l, const char *args) {
    char host[128];
    word_of(args, host, 127);
    struct res r = net_call(&t->net, NET_TIME, 0, host);
    put_s(l, "terminal: ntp ");
    put_s(l, host[0] ? host : "pool.ntp.org");
    put_s(l, " -> ");
    if (r.x[1] != NET_OK) {
        say(t, net_error(r.x[1]));
        put_s(l, net_error(r.x[1]));
    } else {
        struct line m = {.n = 0};
        put_s(&m, "the time is ");
        put_date(&m, r.x[2]);
        out(t, &m);
        put_date(l, r.x[2]);
    }
    put_s(l, "\n");
    flush(l);
}

/* get URL [FILE]: fetch an http:// page and keep it as a file (by default, the URL's last
   name, or index.html). */
static void cmd_get(struct term *t, struct line *l, const char *args) {
    char url[240], name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    const char *rest = word_of(args, url, 239);
    word_of(rest, name, FS_PATH_MAX);
    if (!name[0]) {
        const char *last = url;
        for (const char *p = url; *p; p++) if (*p == '/') last = p + 1;
        int n = 0;
        for (; last[n] && last[n] != '?' && n < FS_NAME_MAX; n++) name[n] = last[n];
        name[n] = 0;
        if (!n) { const char *d = "index.html"; for (n = 0; d[n]; n++) name[n] = d[n]; name[n] = 0; }
    }
    struct res r = net_call(&t->net, NET_GET, 0, url);
    if (r.x[1] != NET_OK) { say(t, net_error(r.x[1])); fs_log(l, "get", url, net_error(r.x[1])); return; }
    u64 size = r.x[2], http = r.x[3];
    resolve(t, name, path);
    u64 st = fs_write(&t->fs, path, "", 0);
    char *piece = (char *)PAGE(SPARE_PAGE + FILE_OFFSET);
    for (u64 off = 0; st == FS_OK && off < size;) {
        struct res c = net_call(&t->net, NET_READ, off, 0);
        u64 n = c.x[1] == NET_OK ? c.x[2] : 0;
        if (!n) { st = FS_IO; break; }
        const char *d = net_data(&t->net);
        for (u64 k = 0; k < n; k++) piece[k] = d[k];
        st = fs_write_at(&t->fs, path, off, piece, n);
        off += n;
    }
    put_s(l, st == FS_OK ? "saved " : "could not save ");
    put_dec(l, size);
    put_s(l, " bytes as ");
    put_s(l, name);
    put_s(l, " (HTTP ");
    put_dec(l, http);
    put_s(l, ")");
    out(t, l);
    put_s(l, "terminal: get ");
    put_s(l, url);
    put_s(l, " -> ");
    put_dec(l, size);
    put_s(l, " bytes, HTTP ");
    put_dec(l, http);
    put_s(l, st == FS_OK ? "\n" : ", not saved\n");
    flush(l);
}

/* kill SLOT: stop the program from the card in open slot SLOT (10 to 15), answering or not.
   Terminal holds those slots' launch capabilities; the kernel lets nothing else stop them
   (`only_launchers_stop`). */
static void cmd_kill(struct term *t, struct line *l, const char *args) {
    char num[8];
    word_of(args, num, 6);
    u64 k = 0;
    int digits = 0;
    for (int i = 0; num[i] >= '0' && num[i] <= '9'; i++, digits++) k = k * 10 + (u64)(num[i] - '0');
    if (!digits || k < OPEN_FIRST || k >= OPEN_FIRST + OPEN_SLOTS) {
        say(t, "kill a slot from ps: 10 to 15");
        fs_log(l, "kill", num, "not an open slot");
        return;
    }
    struct res r = sys1(SYS_STOP, LAUNCH_OPEN + (k - OPEN_FIRST));
    say(t, r.status == OK ? "stopped" : "nothing running there");
    fs_log(l, "kill", num, r.status == OK ? "stopped" : "nothing running");
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
/* What a program from the card gets from the file server when it starts in open slot
   `slot`: its own folder, apps/NAME, read-write (made if new), and the files named after
   it on the command line, read-write; nothing else. Whatever the slot's last program was
   given is taken back first. */
static void give(struct term *t, struct line *l, u64 slot, const char *name, const char *files) {
    fs_unshare(&t->fs, slot);
    char folder[FS_PATH_MAX + 1] = "apps/";
    const char *last = name;
    for (const char *p = name; *p; p++) if (*p == '/') last = p + 1;
    int n = 5;
    for (int i = 0; last[i] && n < FS_PATH_MAX; i++) folder[n++] = last[i];
    folder[n] = 0;
    fs_share(&t->fs, folder, slot, FS_R | FS_W, 1);
    while (*files) {
        char word[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
        files = word_of(files, word, FS_PATH_MAX);
        if (!word[0]) break;
        resolve(t, word, path);
        u64 st = fs_share(&t->fs, path, slot, FS_R | FS_W, 0);
        put_s(l, "terminal: gave ");
        put_s(l, last);
        put_s(l, " ");
        put_s(l, path);
        put_s(l, st == FS_OK ? " -> ok\n" : " -> refused\n");
        flush(l);
    }
}

static void cmd_run(struct term *t, struct line *l, const char *args) {
    char name[FS_NAME_MAX + 1];
    const char *files = word_of(args, name, FS_NAME_MAX);
    if (name[0] && app_raise(name)) {
        say(t, "already open: brought it to the front");
        fs_log(l, "run", name, "already open");
        return;
    }
    char path[FS_PATH_MAX + 1];
    resolve(t, name, path);
    if (fs_stat(&t->fs, path, 0) != FS_FILE && name[0] != '/') {      /* not here: the top folder */
        int i = 0;
        for (; name[i]; i++) path[i] = name[i];
        path[i] = 0;
    }
    if (fs_stat(&t->fs, path, 0) != FS_FILE) { say(t, "no such file"); fs_log(l, "run", name, "no such file"); return; }
    unsigned char *image = (unsigned char *)PAGE(SPARE_PAGE + IMAGE_OFFSET);
    u64 len = 0;
    const char *why = elf_load(&t->fs, path, image, &len);
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
        give(t, l, OPEN_FIRST + (u64)i, name, files);
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
        say(t, "ls [FOLDER], cat FILE, write FILE TEXT, rm FILE");
        say(t, "mkdir FOLDER, cd FOLDER, pwd, mv FROM TO, run PROGRAM");
        say(t, "fill FILE KB CHAR, verify FILE");
        say(t, "ip, ping HOST, get http://URL [FILE], kill SLOT");
        say(t, "date, ntp [HOST[:PORT]]");
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
        cmd_ls(t, l, c + 2);
    } else if (starts(c, "mkdir")) {
        cmd_mkdir(t, l, c + 5);
    } else if (starts(c, "mv")) {
        cmd_mv(t, l, c + 2);
    } else if (starts(c, "cd")) {
        cmd_cd(t, l, c + 2);
    } else if (starts(c, "pwd")) {
        put_s(l, "/");
        put_s(l, t->cwd);
        out(t, l);
    } else if (starts(c, "kill")) {
        cmd_kill(t, l, c + 4);
    } else if (starts(c, "ip")) {
        cmd_ip(t, l);
    } else if (starts(c, "date")) {
        cmd_date(t, l);
    } else if (starts(c, "ntp")) {
        cmd_ntp(t, l, c + 3);
    } else if (starts(c, "ping")) {
        cmd_ping(t, l, c + 4);
    } else if (starts(c, "get")) {
        cmd_get(t, l, c + 3);
    } else if (starts(c, "fill")) {
        cmd_fill(t, l, c + 4);
    } else if (starts(c, "verify")) {
        cmd_verify(t, l, c + 6);
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
    net_init(&t->net, SPARE_PAGE);
    t->cwd[0] = 0;
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
