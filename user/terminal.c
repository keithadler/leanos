/* Terminal. A line of text in, an answer out. Every answer comes from asking the kernel
   (which task this is, what capabilities it holds, what the boot checks found) or the file
   server (ls, cat, write, rm). It holds no more authority than any app: its own frames, and
   send + grant to the display server and the file server.

   Copy (Ctrl+C) takes the command line being typed, or, when it is empty, what the last
   command printed (as far as the scrollback still shows it). A paste (Ctrl+V) goes onto the
   command line, line breaks as spaces: pasted text never runs a command until you press
   Return.

   The command line edits as a shell's does: Left and Right move the cursor, Home and End
   to the line's start and end, and typing, Backspace, Delete (the letter under the cursor)
   and a paste work where it is. Up and Down step through the last HIST commands, which
   history lists (the line being typed is kept, and Down past the newest comes back to it);
   !! on a line is the last of them, and !N the Nth history lists, as in a shell.
   Page Up and Page Down do nothing: Terminal keeps no more lines than it shows. Tab
   completes a command's name at the start of the line, and a file or folder name after it
   (a folder with a '/'), from the file server's listing; when several match, it completes
   what they share, and a second Tab lists them.

   CMD > FILE puts what CMD prints in FILE instead of on the screen (made in FILE.part~, then
   put in place by one rename, as cp and fill do: FILE is its old self or the new one), and
   CMD >> FILE adds it at FILE's end. CMD | CMD2 [| CMD3 ...] hands what CMD prints to CMD2,
   and grep, head, tail, wc, cat, sort, uniq, rev, tr, cut, nl and tee read it when they are
   given no file. The output is captured where it is printed (push), into the pipe buffer:
   64 KiB in the spare run where run makes a program's image, which no command that may be
   redirected uses. grep, head, tail, wc and cat write their output over their input in that
   buffer, never ahead of what they have read; sort and the others that may print more than
   they read (uniq -c, nl) take their input into the line buffer first (text_in). More
   than 64 KiB stops the line and writes nothing; so does a command that fails, whose error
   goes to the screen (as a note such as "no match" does). No quotes: '>' and '|' always
   mean this, with spaces around them or not.

   Commands run to their end before Terminal reads another key, so none may run forever:
   seq counts 100000 numbers at most, sleep 60 seconds, and there is no yes. */
#include "app.h"
#include "fs.h"
#include "elfload.h"
#include "net.h"
#include "date.h"
#include "zone.h"

/* Its code must fit the 16-page code run (user/user.ld), and at -O2 the compiler inlines
   every command into the main loop. So what runs once per command or less (the commands,
   help, Tab completion, copy and paste, the log lines) is compiled for size: COLD, as in the
   display server. Drawing the text and the keys' editing of the command line are not.
   `make` prints each program's size and what is left of its run. */
#define COLD __attribute__((cold, minsize))

/* Terminal's launch capabilities for the open slots, which run programs from the SD card. */
#define LAUNCH_OPEN 6
#define OPEN_FIRST 10
#define OPEN_SLOTS 6
#define IMAGE_OFFSET 192   /* the program image, in the spare run: pages 192-207 */
#define FILE_OFFSET 208    /* a program's file as read from the card: pages 208-223, 64 KiB */
#define PIPE_MAX (16 * 4096) /* the pipe buffer: at IMAGE_OFFSET, free unless run is running */

#define TW 460
#define TH 272
#define PAD 12
#define ROWS 13
#define COLS 52
#define CMD_MAX 160      /* a command line may be longer than the window; it scrolls */
#define LINE_H 19
#define HIST 32          /* commands Up and Down recall, oldest first */
enum { F_MONO = 1 };

struct term {
    char text[ROWS][COLS + 1];  /* scrollback, oldest first; the prompt line is drawn below */
    unsigned char kind[ROWS];   /* 0 output, 1 a command that was typed */
    unsigned char cont[ROWS];   /* 1: the row goes on from the one before (a long line, wrapped) */
    int n;
    int paste_from, dropped;    /* where a paste began on the command line (-1: none), and what did not fit */
    char cmd[CMD_MAX + 1];
    int len, cur;               /* the command line's length, and where the cursor is in it */
    int hn, hpos, tabbed;       /* commands kept; which is on the line (hn: the one being typed); the last key was Tab */
    char typed[CMD_MAX + 1];    /* the line being typed, kept while Up and Down show others */
    char hist[HIST][CMD_MAX + 1];
    struct font mono;
    struct surface win;
    struct fs_client fs;
    struct net_client net;
    char cwd[FS_PATH_MAX + 1];  /* the folder commands are in: "" is the top */
    /* > and |: while `capture` is set, what a command prints goes into the pipe buffer, capn
       bytes so far; `over`: more did not fit; `failed`: the command said an error; `joined`:
       the next line goes on from the last (a piece of a file that did not end in '\n');
       `piped`: the command has input, the pipe buffer's first `inn` bytes */
    u64 capn, inn;
    int capture, over, failed, joined, piped;
};

_Static_assert(sizeof(struct term) <= 8 * 4096, "Terminal's state is larger than its data run");

static const unsigned BG = 0x171a21, FG = 0xdde2ec, DIM = 0x8a93a6, GREEN = 0x7fd1a0;

static char *pipe_buf(void) { return (char *)PAGE(SPARE_PAGE + IMAGE_OFFSET); }

__attribute__((noinline)) static void push(struct term *t, const char *s, u64 n, int kind) {
    if (t->capture && !kind) {
        /* into the pipe buffer, with its '\n'; `s` may be in it, never before where this goes */
        char *b = pipe_buf();
        if (t->over || t->capn + n + !t->joined > PIPE_MAX) { t->over = 1; return; }
        for (u64 j = 0; j < n; j++) b[t->capn++] = s[j];
        if (!t->joined) b[t->capn++] = '\n';
        t->joined = 0;
        return;
    }
    for (int more = 0;; more = 1) {
        u64 take = n > COLS ? COLS : n;
        if (t->n == ROWS) {
            for (int i = 1; i < ROWS; i++) {
                for (int j = 0; j <= COLS; j++) t->text[i - 1][j] = t->text[i][j];
                t->kind[i - 1] = t->kind[i];
                t->cont[i - 1] = t->cont[i];
            }
            t->n--;
        }
        for (u64 j = 0; j < take; j++) t->text[t->n][j] = s[j];
        t->text[t->n][take] = 0;
        t->cont[t->n] = (unsigned char)more;
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

/* The screen, even while the output goes into a file or a pipe, as stderr does elsewhere:
   notes such as "no match", and errors, which stop the line (`failed`). */
COLD static void to_screen(struct term *t, const char *s, u64 n, int failed) {
    int c = t->capture;
    t->capture = 0;
    push(t, s, n, 0);
    t->capture = c;
    t->failed |= failed;
}
#define note(t, s) to_screen(t, s, slen(s), 0)
#define fail(t, s) to_screen(t, s, slen(s), 1)

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
    /* the end of the line, if it is wider than the window, or from the cursor if that is further back */
    int from = t->len > COLS - 3 ? t->len - (COLS - 3) : 0;
    if (t->cur < from) from = t->cur;
    font_text(s, &t->mono, x, y, t->cmd + from, FG);
    /* the cursor: a block, with the letter under it (if any) drawn in the background's color */
    char under[2] = {t->cmd[t->cur], 0};
    t->cmd[t->cur] = 0;
    x += font_width(&t->mono, t->cmd + from);
    t->cmd[t->cur] = under[0];
    fill(s, x + 1, y - 12, 8, 16, GREEN);
    font_text(s, &t->mono, x, y, under, BG);
}

static int scopy(char *d, const char *s) { int n = 0; while ((d[n] = s[n])) n++; return n; }
static int same(const char *a, const char *b) { while (*a && *a == *b) a++, b++; return *a == *b; }

/* A letter onto the command line at the cursor. */
__attribute__((noinline)) static void insert(struct term *t, char c) {
    if (t->len >= CMD_MAX) return;
    for (int i = t->len; i > t->cur; i--) t->cmd[i] = t->cmd[i - 1];
    t->cmd[t->cur++] = c;
    t->len++;
}

/* Return: keep the line for Up, unless it is empty or the same as the last one kept. */
__attribute__((noinline)) static void remember(struct term *t) {
    const char *c = t->cmd;
    while (*c == ' ') c++;
    if (*c && !(t->hn && same(t->hist[t->hn - 1], t->cmd))) {
        if (t->hn == HIST) {
            for (int i = 1; i < HIST; i++) scopy(t->hist[i - 1], t->hist[i]);
            t->hn--;
        }
        scopy(t->hist[t->hn++], t->cmd);
    }
    t->hpos = t->hn;
}

/* Up and Down: command `to` onto the line (t->hn: the line that was being typed). */
__attribute__((noinline)) static void recall(struct term *t, int to) {
    if (to < 0 || to > t->hn) return;
    t->cmd[t->len] = 0;
    if (t->hpos == t->hn) scopy(t->typed, t->cmd);
    t->hpos = to;
    t->len = t->cur = scopy(t->cmd, to == t->hn ? t->typed : t->hist[to]);
}

static int starts(const char *s, const char *w) {
    while (*w) if (*s++ != *w++) return 0;
    return *s == 0 || *s == ' ';
}

COLD static void pad_to(struct line *l, u64 col) { while (l->n < col) l->b[l->n++] = ' '; }

COLD static void hex8(struct line *l, u64 v) {
    for (int i = 28; i >= 0; i -= 4) l->b[l->n++] = "0123456789abcdef"[(v >> i) & 15];
}

COLD static void cmd_caps(struct term *t, struct line *l) {
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

COLD static void cmd_boot(struct term *t, struct line *l) {
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

COLD static const char *fs_error(u64 code) {
    return code == FS_NOT_FOUND ? "no such file" : code == FS_FULL ? "no room"
         : code == FS_NO_SERVER ? "the file server did not answer" : code == FS_EXISTS ? "already there"
         : code == FS_NOT_EMPTY ? "the folder is not empty" : code == FS_NOT_DIR ? "not a folder"
         : code == FS_IS_DIR ? "a folder" : code == FS_IO ? "the card did not answer" : "not a valid name";
}

/* A path as the file server takes it: `arg` from the top folder if it starts with '/',
   else from the current folder. */
COLD static void resolve(struct term *t, const char *arg, char *out) {
    int n = 0;
    if (arg[0] != '/')
        for (int i = 0; t->cwd[i] && n < FS_PATH_MAX; i++) out[n++] = t->cwd[i];
    else arg++;
    if (n && arg[0] && n < FS_PATH_MAX) out[n++] = '/';
    for (int i = 0; arg[i] && n < FS_PATH_MAX; i++) out[n++] = arg[i];
    out[n] = 0;
}

/* The first word of `c` into `word`; returns the rest. */
COLD static const char *word_of(const char *c, char *word, int max) {
    while (*c == ' ') c++;
    int n = 0;
    while (*c && *c != ' ' && n < max) word[n++] = *c++;
    word[n] = 0;
    while (*c == ' ') c++;
    return c;
}

COLD static void fs_log(struct line *l, const char *cmd, const char *name, const char *result) {
    put_s(l, "terminal: ");
    put_s(l, cmd);
    if (name) { put_s(l, " "); put_s(l, name); }
    put_s(l, " -> ");
    put_s(l, result);
    put_s(l, "\n");
    flush(l);
}

/* ls [-a] [FOLDER]: without -a, programs' icons (NAME.icon, fs.h) are left out. */
COLD static void cmd_ls(struct term *t, struct line *l, const char *args) {
    char arg[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    const char *rest = word_of(args, arg, FS_PATH_MAX);
    int all = same(arg, "-a");
    if (all) word_of(rest, arg, FS_PATH_MAX);
    resolve(t, arg, path);
    u64 total = 0, from = 0;
    long shown = 0;
    for (;;) {
        long n = fs_list_dir(&t->fs, path, from, &total);
        if (n < 0) { fail(t, "no such folder"); fs_log(l, "ls", arg[0] ? arg : 0, "no such folder"); return; }
        const struct fs_entry *e = fs_entries(&t->fs);
        for (long i = 0; i < n; i++) {
            if (!all && fs_is_icon(&e[i])) continue;
            shown++;
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
        from += (u64)n;
        if (n == 0 || from >= total) break;
    }
    if (shown == 0) note(t, "nothing here");
    put_s(l, "terminal: ls");
    if (all) put_s(l, " -a");
    if (arg[0]) { put_s(l, " "); put_s(l, arg); }
    put_s(l, " -> ");
    put_dec(l, (u64)shown);
    put_s(l, shown == 1 ? " file\n" : " files\n");
    flush(l);
}

/* The n bytes at `d`, line by line (long lines wrap in push()). A piece that does not end
   in '\n' goes on in the next one (joined) in a file or a pipe: they get the bytes as they are. */
COLD static void put_lines(struct term *t, const char *d, long n) {
    long start = 0;
    for (long i = 0; i <= n; i++)
        if (i == n || d[i] == '\n') {
            if (i > start || i < n) {
                t->joined = i == n;
                push(t, d + start, (u64)(i - start), 0);
            }
            start = i + 1;
        }
}

/* cat FILE; cat with no FILE after a |: what it was handed. */
COLD static void cmd_cat(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 size = 0, off = 0;
    if (!name[0] && t->piped) put_lines(t, pipe_buf(), (long)(off = t->inn));
    else for (;;) {
        long n = fs_read_at(&t->fs, path, off, &size);
        if (n < 0) { fail(t, "no such file"); fs_log(l, "cat", name, "no such file"); return; }
        put_lines(t, fs_data(&t->fs), n);
        off += (u64)n;
        if (n == 0 || off >= size) break;
    }
    put_s(l, "terminal: cat");
    if (name[0]) { put_s(l, " "); put_s(l, name); }
    put_s(l, " -> ");
    put_dec(l, off);
    put_s(l, " bytes\n");
    flush(l);
}

COLD static void cmd_write(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    const char *text = word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = fs_write(&t->fs, path, text, slen(text));
    say(t, st == FS_OK ? "saved" : fs_error(st));
    fs_log(l, "write", name, st == FS_OK ? "ok" : fs_error(st));
}

COLD static void cmd_rm(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = fs_delete(&t->fs, path);
    say(t, st == FS_OK ? "removed" : fs_error(st));
    fs_log(l, "rm", name, st == FS_OK ? "ok" : fs_error(st));
}

COLD static void cmd_mkdir(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = fs_mkdir(&t->fs, path);
    say(t, st == FS_OK ? "made" : fs_error(st));
    fs_log(l, "mkdir", name, st == FS_OK ? "ok" : fs_error(st));
}

/* TO, if it is a folder, becomes the name FROM has, in it: mv and cp keep the name. */
COLD static void into_folder(struct term *t, const char *from, char *to) {
    if (fs_stat(&t->fs, to, 0) != FS_DIR) return;
    const char *last = from;
    for (const char *p = from; *p; p++) if (*p == '/') last = p + 1;
    int n = (int)slen(to);
    if (n + 1 + (int)slen(last) <= FS_PATH_MAX) { to[n] = '/'; scopy(to + n + 1, last); }
}

/* PATH.part~, where fill, cp and > make a file before one rename puts it in place. The name
   is theirs alone: a file there is one they left when the power was cut in the middle, and
   they write over it (and remove it after a failure). So a PATH.tmp of yours is never
   touched, and a power cut never stops the next fill, cp or >. A folder there is refused
   and left alone, as is a name too long to take the ".part~". 0, or why not. */
COLD static const char *tmp_of(struct term *t, const char *path, char *tmp) {
    int n = scopy(tmp, path), at = n;
    while (at > 0 && path[at - 1] != '/') at--;
    if (n + 6 > FS_PATH_MAX || n - at + 6 > FS_NAME_MAX) return "the name is too long";
    scopy(tmp + n, ".part~");
    return fs_stat(&t->fs, tmp, 0) == FS_DIR ? "NAME.part~ is a folder: rename it first" : 0;
}

/* n bytes at `b` into the file at `path`: through `tmp` (PATH.part~) and one rename, or with
   `append`, at its end. What > and tee write. */
COLD static u64 save(struct term *t, const char *path, const char *tmp, const char *b, u64 n, int append) {
    u64 at = 0, off = 0, st = FS_OK;
    const char *dest = path;
    if (append) fs_stat(&t->fs, path, &at);
    else {
        dest = tmp;
        st = fs_write(&t->fs, tmp, "", 0);
    }
    int made = st == FS_OK;
    while (st == FS_OK) {
        u64 take = n - off < FS_CHUNK ? n - off : FS_CHUNK;
        st = fs_write_at(&t->fs, dest, at + off, b + off, take);
        off += take;
        if (off >= n) break;
    }
    if (!append && st == FS_OK) st = fs_rename(&t->fs, tmp, path);
    if (!append && st != FS_OK && made) fs_delete(&t->fs, tmp);
    return st;
}

COLD static void cmd_mv(struct term *t, struct line *l, const char *args) {
    char a[FS_PATH_MAX + 1], b[FS_PATH_MAX + 1], pa[FS_PATH_MAX + 1], pb[FS_PATH_MAX + 1];
    word_of(word_of(args, a, FS_PATH_MAX), b, FS_PATH_MAX);
    resolve(t, a, pa);
    resolve(t, b, pb);
    into_folder(t, a, pb);
    u64 st = fs_rename(&t->fs, pa, pb);
    say(t, st == FS_OK ? "moved" : fs_error(st));
    fs_log(l, "mv", a, st == FS_OK ? "ok" : fs_error(st));
}

COLD static void cmd_cd(struct term *t, struct line *l, const char *args) {
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
        int n = slen(path);
        while (n > 0 && path[n - 1] == '/') path[--n] = 0;   /* "docs/", as Tab completes it */
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

/* fill NAME KB CHAR: a file of KB kilobytes of CHAR, written in pieces to NAME.part~ and
   then put in place by one rename, which the file server does in one step: whatever
   happens, NAME is the old file or the new one, never half of each. */
COLD static void cmd_fill(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], num[12], ch[4], path[FS_PATH_MAX + 1], tmp[FS_PATH_MAX + 7];
    word_of(word_of(word_of(args, name, FS_PATH_MAX), num, 10), ch, 2);
    u64 kb = 0;
    for (int i = 0; num[i] >= '0' && num[i] <= '9'; i++) kb = kb * 10 + (u64)(num[i] - '0');
    resolve(t, name, path);
    const char *why = tmp_of(t, path, tmp);
    if (!why) {
        char *piece = (char *)PAGE(SPARE_PAGE + FILE_OFFSET);
        for (u64 i = 0; i < 16384; i++) piece[i] = ch[0] ? ch[0] : 'x';
        u64 st = fs_write(&t->fs, tmp, piece, 0);
        int made = st == FS_OK;
        for (u64 off = 0; st == FS_OK && off < kb * 1024; off += 16000) {
            u64 take = kb * 1024 - off < 16000 ? kb * 1024 - off : 16000;
            st = fs_write_at(&t->fs, tmp, off, piece, take);
        }
        if (st == FS_OK) st = fs_rename(&t->fs, tmp, path);
        if (st != FS_OK && made) fs_delete(&t->fs, tmp);
        why = st == FS_OK ? 0 : fs_error(st);
    }
    say(t, why ? why : "filled");
    fs_log(l, "fill", name, why ? why : "ok");
}

/* verify NAME: whether every byte of NAME is the same (what fill makes). */
COLD static void cmd_verify(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 size = 0, off = 0;
    char first = 0;
    int mixed = 0;
    for (;;) {
        long n = fs_read_at(&t->fs, path, off, &size);
        if (n < 0) { fail(t, "no such file"); fs_log(l, "verify", name, "no such file"); return; }
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

/* ---- more on files: cp, head, tail, wc, grep, find, df ---- */

#define LINE_MAX (16 * 4096 - 1)   /* a line as head, tail and grep take it: 64 KiB, at FILE_OFFSET */
#define FIND_DEPTH 16              /* find goes this many folders down */
#define FIND_SHOWN 100             /* and shows this many names at most */

/* Why `path` cannot be read as a file: it is a folder, or it is not there. */
COLD static const char *unreadable(struct term *t, const char *path) {
    return fs_stat(&t->fs, path, 0) == FS_DIR ? "a folder, not a file" : "no such file";
}

/* A number, from its digits; -1 if `s` is not one. */
COLD static long number(const char *s) {
    long v = 0;
    if (!*s) return -1;
    for (; *s; s++) {
        if (*s < '0' || *s > '9' || v > 100000000) return -1;
        v = v * 10 + (*s - '0');
    }
    return v;
}

static int lower(int c) { return c >= 'A' && c <= 'Z' ? c + 32 : c; }

/* Whether the n bytes at `s` hold `w` (ignoring case if `fold`). */
COLD static int contains(const char *s, long n, const char *w, int fold) {
    long m = (long)slen(w);
    for (long i = 0; i + m <= n; i++) {
        long j = 0;
        while (j < m && (fold ? lower(s[i + j]) == lower(w[j]) : s[i + j] == w[j])) j++;
        if (j == m) return 1;
    }
    return 0;
}

/* A file, line by line, a piece at a time through the file server's buffer; with no path,
   the input a | hands on. */
struct reader { const char *path; u64 off, size; long n, i; };

/* The next line into `line` (its first LINE_MAX bytes, and a 0), without its '\n': its
   length, -1 after the last, -2 if the file cannot be read. */
COLD static long next_line(struct term *t, struct reader *r, char *line) {
    long k = 0, any = 0;
    if (!r->path) {                     /* no file: the pipe's input, before what is written over it */
        const char *b = pipe_buf();
        if (r->off >= t->inn) return -1;
        while (r->off < t->inn) {
            char c = b[r->off++];
            if (c == '\n') break;
            if (k < LINE_MAX) line[k++] = c;
        }
        line[k] = 0;
        return k;
    }
    for (;;) {
        if (r->i >= r->n) {
            long n = r->n && r->off >= r->size ? 0 : fs_read_at(&t->fs, r->path, r->off, &r->size);
            if (n < 0) return -2;
            if (n == 0) { line[k] = 0; return any ? k : -1; }
            r->off += (u64)n;
            r->n = n;
            r->i = 0;
        }
        char c = fs_data(&t->fs)[r->i++];
        if (c == '\n') break;
        any = 1;
        if (k < LINE_MAX) line[k++] = c;
    }
    line[k] = 0;
    return k;
}

/* The line buffer: where a program's file is read for run, free while a command runs. */
static char *line_buf(void) { return (char *)PAGE(SPARE_PAGE + FILE_OFFSET); }

/* A line from next_line as head, tail and grep print it, after what `l` holds: on the
   screen, its first 200 bytes; into a file or a pipe, all of it (one that next_line cut
   short is more than the pipe buffer takes: over). */
COLD static void put_line(struct term *t, struct line *l, const char *s, long k) {
    if (!t->capture) { put_s(l, s); out(t, l); return; }
    t->joined = 1;
    push(t, l->b, l->n, 0);
    l->n = 0;
    push(t, s, (u64)k, 0);
    t->over |= k >= LINE_MAX;
}

/* cp FROM TO: a copy, made as fill makes a file: in pieces into TO.part~, then put in place
   by one rename, so TO is its old self or the whole copy. TO may be a folder, as for mv. */
COLD static void cmd_cp(struct term *t, struct line *l, const char *args) {
    char a[FS_PATH_MAX + 1], b[FS_PATH_MAX + 1], pa[FS_PATH_MAX + 1], pb[FS_PATH_MAX + 1], tmp[FS_PATH_MAX + 7];
    word_of(word_of(args, a, FS_PATH_MAX), b, FS_PATH_MAX);
    resolve(t, a, pa);
    resolve(t, b, pb);
    into_folder(t, a, pb);
    const char *in_way = tmp_of(t, pb, tmp);
    u64 size = 0, off = 0, kind = fs_stat(&t->fs, pa, &size), st = FS_OK;
    const char *why = !a[0] || !b[0] ? "cp FROM TO" : kind == FS_DIR ? "cp copies files, not folders"
                    : !kind ? "no such file" : same(tmp, pa) ? "FROM is where the copy is made: rename it first"
                    : in_way;
    if (!why) {
        st = fs_write(&t->fs, tmp, "", 0);
        int made = st == FS_OK;
        while (st == FS_OK && off < size) {
            long n = fs_read_at(&t->fs, pa, off, &size);
            if (n <= 0) { st = n < 0 ? FS_NOT_FOUND : FS_OK; break; }
            /* the piece is in the buffer's data area already: written from where it is */
            st = fs_write_at(&t->fs, tmp, off, fs_data(&t->fs), (u64)n);
            off += (u64)n;
        }
        if (st == FS_OK) st = fs_rename(&t->fs, tmp, pb);
        if (st != FS_OK && made) fs_delete(&t->fs, tmp);
        why = st == FS_OK ? 0 : fs_error(st);
    }
    if (why) say(t, why);
    else {
        put_s(l, "copied ");
        put_dec(l, off);
        put_s(l, " bytes");
        out(t, l);
    }
    put_s(l, "terminal: cp ");
    put_s(l, a);
    if (b[0]) { put_s(l, " "); put_s(l, b); }
    put_s(l, " -> ");
    if (why) put_s(l, why);
    else { put_dec(l, off); put_s(l, " bytes"); }
    put_s(l, "\n");
    flush(l);
}

/* head [-n N] FILE, tail [-n N] FILE: its first or last N lines (10 if not said); after a |,
   with no FILE, of what it was handed. tail reads the file twice, counting its lines and then
   showing the last, so it keeps none. */
COLD static void cmd_ends(struct term *t, struct line *l, const char *args, int tail) {
    char w[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    const char *cmd = tail ? "tail" : "head";
    const char *rest = word_of(args, w, FS_PATH_MAX);
    long want = 10;
    if (same(w, "-n")) {
        rest = word_of(rest, w, 12);
        want = number(w);
        word_of(rest, w, FS_PATH_MAX);
    }
    if (want < 0 || (!w[0] && !t->piped)) { fail(t, tail ? "tail [-n N] FILE" : "head [-n N] FILE"); fs_log(l, cmd, 0, "not understood"); return; }
    resolve(t, w, path);
    const char *from_file = w[0] ? path : 0;
    char *line = line_buf();
    struct reader r = {.path = from_file};
    long k = 0, total = 0, from = 0, shown = 0;
    if (tail) {
        while ((k = next_line(t, &r, line)) >= 0) total++;
        from = total > want ? total - want : 0;
        r = (struct reader){.path = from_file};
    }
    for (long i = 0; k != -2 && shown < want && (k = next_line(t, &r, line)) >= 0; i++)
        if (i >= from) {
            put_line(t, l, line, k);  /* on the screen, its first 200 bytes, wrapped as cat wraps */
            shown++;
        }
    if (k == -2) { const char *why = unreadable(t, path); fail(t, why); fs_log(l, cmd, w, why); return; }
    put_s(l, "terminal: ");
    put_s(l, cmd);
    if (w[0]) { put_s(l, " "); put_s(l, w); }
    put_s(l, " -> ");
    put_dec(l, (u64)shown);
    put_s(l, shown == 1 ? " line" : " lines");
    if (tail) { put_s(l, " of "); put_dec(l, (u64)total); }
    put_s(l, "\n");
    flush(l);
}

/* wc FILE: its lines ('\n's), words (runs of anything but spaces and control bytes) and bytes;
   after a |, with no FILE, of what it was handed. */
COLD static void cmd_wc(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 size = 0, off = 0, lines = 0, words = 0;
    int in = 0, pipe = !name[0] && t->piped;
    for (;;) {
        long n = pipe ? (long)(t->inn - off) : fs_read_at(&t->fs, path, off, &size);
        if (pipe) size = t->inn;
        if (n < 0) { const char *why = unreadable(t, path); fail(t, why); fs_log(l, "wc", name, why); return; }
        const unsigned char *d = (const unsigned char *)(pipe ? pipe_buf() + off : fs_data(&t->fs));
        for (long i = 0; i < n; i++) {
            lines += d[i] == '\n';
            words += d[i] > ' ' && !in;
            in = d[i] > ' ';
        }
        off += (u64)n;
        if (n == 0 || off >= size) break;
    }
    struct line m = {.n = 0};
    put_dec(&m, lines);
    put_s(&m, lines == 1 ? " line, " : " lines, ");
    put_dec(&m, words);
    put_s(&m, words == 1 ? " word, " : " words, ");
    put_dec(&m, off);
    put_s(&m, off == 1 ? " byte" : " bytes");
    m.b[m.n] = 0;
    fs_log(l, "wc", name[0] ? name : 0, m.b);
    out(t, &m);
}

/* grep [-i] TEXT FILE...: the lines that hold TEXT (a word; -i: in capitals or not), each
   after its file's name and line number when there are several files; after a |, with no
   FILE, the lines it was handed. A line longer than 64 KiB is searched in its first 64 KiB. */
COLD static void cmd_grep(struct term *t, struct line *l, const char *args) {
    char text[64], name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    const char *files = word_of(args, text, 63);
    int fold = same(text, "-i");
    if (fold) files = word_of(files, text, 63);
    int pipe = !*files;
    if (!text[0] || (pipe && !t->piped)) { fail(t, "grep [-i] TEXT FILE..."); fs_log(l, "grep", 0, "not understood"); return; }
    int many = *word_of(files, name, FS_PATH_MAX) != 0;
    char *line = line_buf();
    u64 found = 0;
    do {
        files = word_of(files, name, FS_PATH_MAX);
        resolve(t, name, path);
        struct reader r = {.path = pipe ? 0 : path};
        long k;
        u64 no = 0;
        while ((k = next_line(t, &r, line)) >= 0) {
            no++;
            if (!contains(line, k, text, fold)) continue;
            found++;
            if (many) {
                put_s(l, name);
                put_s(l, ":");
                put_dec(l, no);
                put_s(l, ": ");
            }
            put_line(t, l, line, k);
        }
        if (k == -2) {
            put_s(l, name);
            put_s(l, ": ");
            put_s(l, unreadable(t, path));
            to_screen(t, l->b, l->n, 1);
            l->n = 0;
        }
    } while (*files);
    if (!found) note(t, "no match");
    put_s(l, "terminal: grep ");
    if (fold) put_s(l, "-i ");
    put_s(l, text);
    put_s(l, " -> ");
    put_dec(l, found);
    put_s(l, found == 1 ? " line\n" : " lines\n");
    flush(l);
}

/* A walk through a folder's tree, as find, du and tree take it: every file and folder under
   `path`, handed to visit() with its path (from `base`) in `path` and `depth` folders down
   from the first, until visit() says stop. No recursion: each folder down keeps where it is
   in its listing. It goes FIND_DEPTH folders down (`deep`: there were more); what it looks
   at is at most every name on the card (1024), each listed once, so no tree makes it run
   for long. Icons are left out, as by ls. visit() may not call the file server: the entry
   is in its buffer. */
struct walk {
    char path[FS_PATH_MAX + 1], name[FS_NAME_MAX + 1];
    const char *dir;
    int base, depth, deep;
    u64 found, files, bytes;
};
typedef int visit_fn(struct term *t, struct line *l, struct walk *w, const struct fs_entry *e);

/* 1 if visit() stopped it before the end. */
COLD static int walk(struct term *t, struct line *l, struct walk *w, visit_fn *visit) {
    u64 next[FIND_DEPTH];
    int len[FIND_DEPTH], stop = 0;
    char *path = w->path;
    w->base = (int)slen(path);
    w->depth = w->deep = 0;
    next[0] = 0;
    len[0] = w->base;
    while (w->depth >= 0 && !stop) {
        int d = w->depth;
        path[len[d]] = 0;
        u64 total = 0;
        long got = fs_list_dir(&t->fs, path, next[d], &total);
        const struct fs_entry *e = fs_entries(&t->fs);
        int down = 0;
        for (long i = 0; i < got && !down && !stop; i++) {
            next[d]++;
            if (fs_is_icon(&e[i])) continue;
            int at = len[d], n = at, isdir = e[i].kind == FS_DIR;
            int fits = at + 1 + (int)slen(e[i].name) <= FS_PATH_MAX;    /* else it is cut short */
            if (n) path[n++] = '/';
            for (int j = 0; j < FS_NAME_MAX && e[i].name[j] && n < FS_PATH_MAX; j++) path[n++] = e[i].name[j];
            path[n] = 0;
            stop = visit(t, l, w, &e[i]);
            if (isdir && fits && d + 1 < FIND_DEPTH) {
                w->depth = d + 1;
                next[d + 1] = 0;
                len[d + 1] = n;
                down = 1;
            } else w->deep |= isdir;
        }
        if (!down && (got <= 0 || next[d] >= total)) w->depth--;
    }
    return w->depth >= 0;
}

/* find: a name that holds NAME (or any, with no NAME), as FOLDER/PATH; FIND_SHOWN at most. */
COLD static int found_one(struct term *t, struct line *l, struct walk *w, const struct fs_entry *e) {
    if (w->name[0] && !contains(e->name, (long)slen(e->name), w->name, 0)) return 0;
    int dn = (int)slen(w->dir);
    put_s(l, w->dir);
    if (dn && w->dir[dn - 1] != '/') put_s(l, "/");
    put_s(l, w->path + w->base + (w->base > 0));
    if (e->kind == FS_DIR) put_s(l, "/");
    out(t, l);
    return ++w->found >= FIND_SHOWN;
}

/* find [FOLDER] [NAME]: every file and folder under FOLDER (this one if not said), or those
   whose names hold NAME, a folder with a '/'; one word that is not a folder is a NAME. It
   goes FIND_DEPTH folders down and stops after FIND_SHOWN names (walk). */
COLD static void cmd_find(struct term *t, struct line *l, const char *args) {
    char dir[FS_PATH_MAX + 1];
    struct walk w;
    word_of(word_of(args, dir, FS_PATH_MAX), w.name, FS_NAME_MAX);
    int dn = (int)slen(dir);
    while (dn > 1 && dir[dn - 1] == '/') dir[--dn] = 0;
    resolve(t, dir, w.path);
    int slash = 0;
    for (int i = 0; dir[i]; i++) slash |= dir[i] == '/';
    if (dir[0] && !w.name[0] && !slash && fs_stat(&t->fs, w.path, 0) != FS_DIR) {   /* one word: a name, here */
        for (int i = 0; i <= FS_NAME_MAX; i++) w.name[i] = i < FS_NAME_MAX ? dir[i] : 0;
        dir[0] = 0;
        resolve(t, dir, w.path);
    }
    if (fs_stat(&t->fs, w.path, 0) != FS_DIR) { fail(t, "no such folder"); fs_log(l, "find", dir, "no such folder"); return; }
    w.dir = dir;
    w.found = 0;
    int cut = walk(t, l, &w, found_one);
    if (!w.found) note(t, "nothing found");
    if (cut) note(t, "(stopped: find shows 100 names at most)");
    if (w.deep) note(t, "(folders more than 16 down were not searched)");
    put_s(l, "terminal: find");
    if (dir[0]) { put_s(l, " "); put_s(l, dir); }
    if (w.name[0]) { put_s(l, " "); put_s(l, w.name); }
    put_s(l, " -> ");
    put_dec(l, w.found);
    put_s(l, " found");
    if (cut) put_s(l, ", stopped");
    if (w.deep) put_s(l, ", not below 16 folders");
    put_s(l, "\n");
    flush(l);
}

/* df: the card's size, and what is used and free, from the file server's totals. */
COLD static void cmd_df(struct term *t, struct line *l) {
    struct fs_space s;
    u64 st = fs_space(&t->fs, &s);
    if (st != FS_OK) { fail(t, fs_error(st)); fs_log(l, "df", 0, fs_error(st)); return; }
    u64 kb = s.cluster / 1024, size = s.clusters * kb, free = s.free * kb;
    put_s(l, "size ");
    put_dec(l, size);
    put_s(l, " KiB, used ");
    put_dec(l, size - free);
    put_s(l, " KiB, free ");
    put_dec(l, free);
    put_s(l, " KiB");
    out(t, l);
    put_dec(l, s.files);
    put_s(l, s.files == 1 ? " file, " : " files, ");
    put_dec(l, s.folders);
    put_s(l, s.folders == 1 ? " folder; room for " : " folders; room for ");
    put_dec(l, s.names - s.files - s.folders);
    put_s(l, " more");
    out(t, l);
    put_s(l, "terminal: df -> ");
    put_dec(l, free);
    put_s(l, " KiB free of ");
    put_dec(l, size);
    put_s(l, ", ");
    put_dec(l, s.files);
    put_s(l, " files, ");
    put_dec(l, s.folders);
    put_s(l, " folders\n");
    flush(l);
}

/* history: the commands Up and Down recall, oldest first. */
COLD static void cmd_history(struct term *t, struct line *l) {
    for (int i = 0; i < t->hn; i++) {
        put_dec(l, (u64)i + 1);
        pad_to(l, 4);
        put_s(l, t->hist[i]);
        out(t, l);
    }
    put_s(l, "terminal: history -> ");
    put_dec(l, (u64)t->hn);
    put_s(l, t->hn == 1 ? " command\n" : " commands\n");
    flush(l);
}

/* ---- the network (the USB driver serves it) ---- */

static const char *net_error(u64 code) {
    return code == NET_NO_DEVICE ? "no network adapter" : code == NET_NO_ADDRESS ? "no address from the network"
         : code == NET_NO_HOST ? "no such host" : code == NET_NO_ANSWER ? "no answer"
         : code == NET_UNSUPPORTED ? "only http:// (no https yet)" : code == NET_NO_SERVICE ? "the network service did not answer"
         : code == NET_DENIED ? "not allowed"
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

/* The time in the time zone chosen in Settings, and in UTC beside it if that is not UTC:
   "2026-09-26 08:52:24 UTC+2 (06:52:24 UTC)". */
COLD static void put_date_in(struct line *l, u64 secs, long zone) {
    put_date(l, local_of(secs, zone));
    if (!zone) return;
    l->n -= 3;                           /* "UTC": the zone's name instead */
    put_zone(l, zone);
    struct line u = {.n = 0};
    put_date(&u, secs);
    u.b[u.n] = 0;
    const char *time = u.b;
    while (*time && *time++ != ' ') {}   /* the time of day, after the date */
    put_s(l, " (");
    put_s(l, time);
    put_s(l, ")");
}

/* date: the time of day the kernel keeps (set from the network, in UTC), in the time zone
   the display keeps (asked as Clock asks it, app_zone). */
COLD static void cmd_date(struct term *t, struct line *l) {
    u64 secs = sys0(SYS_TIME).x[6];
    if (!secs) {
        fail(t, "the time is not known: no time server has answered (try ntp)");
        put_s(l, "terminal: date -> not known\n");
        flush(l);
        return;
    }
    long zone = app_zone();
    put_date_in(l, secs, zone);
    out(t, l);
    put_s(l, "terminal: date -> ");
    put_date_in(l, secs, zone);
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

/* ---- text: sort, uniq, rev, tr, cut, nl, tee, seq; files: touch, stat, du, tree; cal,
   sleep, time, calc ---- */

#define TEXT_MAX (16 * 4096)   /* what a filter takes: the line buffer's 64 KiB */
#define SORT_OFFSET 187        /* sort's index of lines: pages 187-191 of the spare run */
#define SORT_LINES (5 * 4096 / 2)
_Static_assert(APP_WIN_OFFSET + (TW * TH * 4 + 4095) / 4096 <= SORT_OFFSET, "sort's index is under the window's pixels");
_Static_assert(SORT_OFFSET + 5 <= IMAGE_OFFSET, "sort's index is over the pipe buffer");

/* "terminal: CMD -> N THING(s)", the log line most of these end with. */
COLD static void log_count(struct line *l, const char *cmd, u64 n, const char *thing) {
    put_s(l, "terminal: ");
    put_s(l, cmd);
    put_s(l, " -> ");
    put_dec(l, n);
    put_s(l, " ");
    put_s(l, thing);
    put_s(l, n == 1 ? "\n" : "s\n");
    flush(l);
}

/* v, right-aligned in `width` columns. */
COLD static void put_num(struct line *l, u64 v, int width) {
    int d = 1;
    for (u64 x = v; x >= 10; x /= 10) d++;
    while (width-- > d) put_s(l, " ");
    put_dec(l, v);
}

COLD static void usage(struct term *t, struct line *l, const char *cmd, const char *how) {
    fail(t, how);
    fs_log(l, cmd, 0, "not understood");
}

/* Leading options, such as -r -n or -rn, each a letter of `letters`: their bits (1 << where
   in `letters`) into *set. The first word that is not one is left in `w`; returns the rest. */
COLD static const char *options(const char *args, const char *letters, int *set, char *w) {
    for (;;) {
        const char *rest = word_of(args, w, FS_PATH_MAX);
        int bits = 0;
        for (int i = 1; w[0] == '-' && w[i]; i++) {
            const char *p = letters;
            while (*p && *p != w[i]) p++;
            bits = *p ? bits | 1 << (p - letters) : -1;
        }
        if (w[0] != '-' || bits <= 0) return rest;
        *set |= bits;
        args = rest;
    }
}

/* The text a filter works on: the file `name`, or with no name after a |, what it was
   handed; all of it (TEXT_MAX at most) in the line buffer, each line ending in a 0 in place
   of its '\n' (so a 0 byte in it ends a line early). Its length, 0s and all; -1 if there is
   none (said, and logged). The output goes to the pipe buffer, never over it. */
COLD static long text_in(struct term *t, struct line *l, const char *cmd, const char *name, const char *how) {
    char path[FS_PATH_MAX + 1], *d = line_buf();
    u64 n = 0, size = 0;
    const char *why = 0;
    if (!name[0]) {
        if (!t->piped) { usage(t, l, cmd, how); return -1; }
        for (const char *p = pipe_buf(); n < t->inn; n++) d[n] = p[n];
    } else {
        resolve(t, name, path);
        for (;;) {
            long k = fs_read_at(&t->fs, path, n, &size);
            if (k < 0) { why = unreadable(t, path); break; }
            if (n + (u64)k > TEXT_MAX) { why = "more than 64 KiB"; break; }
            for (long i = 0; i < k; i++) d[n++] = fs_data(&t->fs)[i];
            if (k == 0 || n >= size) break;
        }
    }
    if (!why && n && d[n - 1] != '\n') {
        if (n == TEXT_MAX) why = "more than 64 KiB";
        else d[n++] = '\n';
    }
    if (why) { fail(t, why); fs_log(l, cmd, name, why); return -1; }
    for (u64 i = 0; i < n; i++) if (d[i] == '\n') d[i] = 0;
    return (long)n;
}

/* A number at the start of `s` (after spaces, a '-' first if negative), as sort -n reads it. */
COLD static long leading(const char *s) {
    while (*s == ' ') s++;
    int neg = *s == '-';
    long v = 0;
    for (s += neg; *s >= '0' && *s <= '9' && v < 100000000000000L; s++) v = v * 10 + (*s - '0');
    return neg ? -v : v;
}

/* sort's order: by the number each line starts with (-n) and then byte by byte. */
COLD static int order(const char *a, const char *b, int opts) {
    int c = 0;
    if (opts & 2) {
        long x = leading(a), y = leading(b);
        if (x != y) c = x < y ? -1 : 1;
    }
    while (!c && *a && *a == *b) a++, b++;
    if (!c) c = (unsigned char)*a - (unsigned char)*b;
    return opts & 1 ? -c : c;
}

/* sort [-r] [-n] [FILE]: the lines in order (-r: backward; -n: by the number they start
   with), sorted by a Shell sort of an index of where each begins (SORT_LINES at most). */
COLD static void cmd_sort(struct term *t, struct line *l, const char *args) {
    char w[FS_PATH_MAX + 1];
    int opts = 0;
    options(args, "rn", &opts, w);
    long n = text_in(t, l, "sort", w, "sort [-r] [-n] FILE"), k = 0;
    if (n < 0) return;
    char *d = line_buf();
    unsigned short *at = (unsigned short *)PAGE(SPARE_PAGE + SORT_OFFSET);
    for (long i = 0; i < n; i += (long)slen(d + i) + 1) {
        if (k == SORT_LINES) { fail(t, "more than 10240 lines"); fs_log(l, "sort", w, "more than 10240 lines"); return; }
        at[k++] = (unsigned short)i;
    }
    for (long gap = k / 2; gap > 0; gap /= 2)
        for (long i = gap; i < k; i++)
            for (long j = i; j >= gap && order(d + at[j - gap], d + at[j], opts) > 0; j -= gap) {
                unsigned short s = at[j];
                at[j] = at[j - gap];
                at[j - gap] = s;
            }
    for (long i = 0; i < k; i++) put_line(t, l, d + at[i], (long)slen(d + at[i]));
    log_count(l, "sort", (u64)k, "line");
}

/* uniq [-c] [FILE]: each run of the same line once (-c: after how many times it came). */
COLD static void cmd_uniq(struct term *t, struct line *l, const char *args) {
    char w[FS_PATH_MAX + 1];
    int count = 0;
    options(args, "c", &count, w);
    long n = text_in(t, l, "uniq", w, "uniq [-c] FILE");
    if (n < 0) return;
    const char *d = line_buf(), *prev = 0;
    u64 times = 0, shown = 0;
    for (long i = 0;; ) {
        const char *s = i < n ? d + i : 0;
        if (prev && (!s || !same(prev, s))) {
            if (count) { put_num(l, times, 4); put_s(l, " "); }
            put_line(t, l, prev, (long)slen(prev));
            shown++;
            times = 0;
        }
        if (!s) break;
        prev = s;
        times++;
        i += (long)slen(s) + 1;
    }
    log_count(l, "uniq", shown, "line");
}

/* rev, tr, cut and nl: each line of the text changed where it is, or numbered, one at a time. */
enum { REV, TR, CUT, NL };

/* A set as tr takes it: letters, and ranges such as a-z; its length. */
COLD static int set_of(const char *s, unsigned char *set) {
    int n = 0;
    for (; *s && n < 256; s++) {
        unsigned char c = (unsigned char)*s, to = c;
        if (s[1] == '-' && s[2] && (unsigned char)s[2] >= c) to = (unsigned char)s[2], s += 2;
        for (unsigned v = c; v <= to && n < 256; v++) set[n++] = (unsigned char)v;
    }
    return n;
}

/* rev [FILE]: each line backward. tr A B [FILE]: each letter of set A as the one at its place
   in B (B's last if B is shorter). cut [-d C] -f N [FILE]: the Nth field of each line, split
   at C (a space if not said; no quotes, so -d cannot be a space), a line with no C whole.
   nl [FILE]: each line after its number. */
COLD static void cmd_lines(struct term *t, struct line *l, const char *args, int what) {
    static const char *const names[] = {"rev", "tr", "cut", "nl"};
    static const char *const hows[] = {"rev FILE", "tr SET1 SET2 FILE (sets such as a-z)", "cut [-d C] -f N FILE", "nl FILE"};
    char w[FS_PATH_MAX + 1], a[64];
    unsigned char map[256], from[256], to[256];
    const char *cmd = names[what], *how = hows[what];
    int bad = 0;
    long field = 1;
    char delim = ' ';
    for (int i = 0; i < 256; i++) map[i] = (unsigned char)i;
    if (what == TR) {
        args = word_of(word_of(args, a, 63), w, 63);
        int m = set_of(a, from), k = set_of(w, to);
        bad = !m || !k;
        for (int i = 0; i < m && !bad; i++) map[from[i]] = to[i < k ? i : k - 1];
        map[0] = 0;
    }
    if (what == CUT) {
        field = -1;
        for (;;) {
            const char *rest = word_of(args, w, FS_PATH_MAX);
            int d = same(w, "-d") || (w[0] == '-' && w[1] == 'd' && w[2] && !w[3]);
            if (!d && !(w[0] == '-' && w[1] == 'f')) break;
            if (!w[2]) rest = word_of(rest, w + 2, 12);
            if (d) delim = w[2];
            else field = number(w + 2);
            args = rest;
        }
        bad = field < 1 || !delim;
    }
    word_of(args, w, FS_PATH_MAX);
    if (bad) { usage(t, l, cmd, how); return; }
    long n = text_in(t, l, cmd, w, how);
    if (n < 0) return;
    char *d = line_buf();
    u64 lines = 0;
    for (long i = 0; i < n; lines++) {
        char *s = d + i;
        long k = (long)slen(s);
        i += k + 1;
        if (what == REV)
            for (long j = 0; j < k / 2; j++) { char c = s[j]; s[j] = s[k - 1 - j]; s[k - 1 - j] = c; }
        if (what == TR)
            for (long j = 0; j < k; j++) s[j] = (char)map[(unsigned char)s[j]];
        if (what == CUT) {
            char *f = s, *e;
            int any = 0;
            for (char *p = s; *p; p++) any |= *p == delim;
            for (long left = field; --left > 0 && *f; f += *f == delim)
                while (*f && *f != delim) f++;
            if (any) {                         /* a line with no C at all stays whole */
                for (e = f; *e && *e != delim; e++) {}
                *e = 0;
                s = f;
                k = (long)slen(s);
            }
        }
        if (what == NL) { put_num(l, lines + 1, 4); put_s(l, "  "); }
        put_line(t, l, s, k);
    }
    log_count(l, cmd, lines, "line");
}

/* CMD | tee FILE: what it is handed, into FILE (as > writes one) and on to the screen or the
   next command. */
COLD static void cmd_tee(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1], tmp[FS_PATH_MAX + 7];
    word_of(args, name, FS_PATH_MAX);
    if (!name[0] || !t->piped) { usage(t, l, "tee", "CMD | tee FILE"); return; }
    resolve(t, name, path);
    const char *why = fs_stat(&t->fs, path, 0) == FS_DIR ? "a folder, not a file" : tmp_of(t, path, tmp);
    if (!why) {
        u64 st = save(t, path, tmp, pipe_buf(), t->inn, 0);
        why = st == FS_OK ? 0 : fs_error(st);
    }
    if (why) { fail(t, why); fs_log(l, "tee", name, why); return; }
    put_lines(t, pipe_buf(), (long)t->inn);
    put_s(l, "terminal: tee ");
    put_s(l, name);
    put_s(l, " -> ");
    put_dec(l, t->inn);
    put_s(l, t->inn == 1 ? " byte\n" : " bytes\n");
    flush(l);
}

/* seq [FIRST] LAST: the numbers FIRST (1 if not said) to LAST, 100000 at most. */
COLD static void cmd_seq(struct term *t, struct line *l, const char *args) {
    char a[12], b[12];
    word_of(word_of(args, a, 11), b, 11);
    long from = 1, to = number(a);
    if (b[0]) from = to, to = number(b);
    if (from < 0 || to < 0 || to - from >= 100000) { usage(t, l, "seq", "seq [FIRST] LAST, 100000 numbers at most"); return; }
    for (long i = from; i <= to && !t->over; i++) {
        put_dec(l, (u64)i);
        out(t, l);
    }
    log_count(l, "seq", (u64)(to >= from ? to - from + 1 : 0), "number");
}

/* touch FILE: an empty file, if there is none of that name. */
COLD static void cmd_touch(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 st = !name[0] ? FS_BAD : fs_stat(&t->fs, path, 0) ? FS_EXISTS : fs_write(&t->fs, path, "", 0);
    const char *what = st == FS_OK ? "made" : st == FS_EXISTS ? "already there" : fs_error(st);
    if (st == FS_OK || st == FS_EXISTS) say(t, what);
    else fail(t, what);
    fs_log(l, "touch", name, st == FS_OK ? "ok" : what);
}

/* stat FILE: a file and its size, or a folder and how many names it holds. */
COLD static void cmd_stat(struct term *t, struct line *l, const char *args) {
    char name[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    word_of(args, name, FS_PATH_MAX);
    resolve(t, name, path);
    u64 size = 0, kind = name[0] ? fs_stat(&t->fs, path, &size) : 0;
    if (!kind) { fail(t, "no such file"); fs_log(l, "stat", name, "no such file"); return; }
    if (kind == FS_DIR) fs_list_dir(&t->fs, path, 0, &size);
    struct line m = {.n = 0};
    put_s(&m, kind == FS_DIR ? "folder, " : "file, ");
    put_dec(&m, size);
    put_s(&m, kind == FS_DIR ? (size == 1 ? " name" : " names") : (size == 1 ? " byte" : " bytes"));
    m.b[m.n] = 0;
    put_s(l, name);
    put_s(l, ": ");
    put_s(l, m.b);
    out(t, l);
    fs_log(l, "stat", name, m.b);
}

COLD static int du_one(struct term *t, struct line *l, struct walk *w, const struct fs_entry *e) {
    if (e->kind == FS_DIR) w->found++;
    else w->files++, w->bytes += e->size;
    return 0;
}

COLD static int tree_one(struct term *t, struct line *l, struct walk *w, const struct fs_entry *e) {
    for (int i = 0; i <= w->depth; i++) put_s(l, "  ");
    put_s(l, e->name);
    if (e->kind == FS_DIR) put_s(l, "/");
    out(t, l);
    return du_one(t, l, w, e);
}

/* du [FOLDER]: the bytes in the files under FOLDER (this one if not said), and how many
   files and folders. tree [FOLDER]: FOLDER, then what is under it, each folder's names two
   spaces further in. Both walk the tree as find does, FIND_DEPTH folders down. */
COLD static void cmd_du(struct term *t, struct line *l, const char *args, int tree) {
    char dir[FS_PATH_MAX + 1];
    const char *cmd = tree ? "tree" : "du";
    struct walk w = {.found = 0};
    word_of(args, dir, FS_PATH_MAX);
    resolve(t, dir, w.path);
    if (fs_stat(&t->fs, w.path, 0) != FS_DIR) { fail(t, "no such folder"); fs_log(l, cmd, dir, "no such folder"); return; }
    if (tree) { put_s(l, dir[0] ? dir : "."); out(t, l); }
    walk(t, l, &w, tree ? tree_one : du_one);
    struct line m = {.n = 0};
    if (!tree) { put_dec(&m, w.bytes); put_s(&m, w.bytes == 1 ? " byte in " : " bytes in "); }
    put_dec(&m, w.files);
    put_s(&m, w.files == 1 ? " file, " : " files, ");
    put_dec(&m, w.found);
    put_s(&m, w.found == 1 ? " folder" : " folders");
    m.b[m.n] = 0;
    if (!tree) out(t, &m);
    if (w.deep) note(t, "(folders more than 16 down were not counted)");
    fs_log(l, cmd, dir[0] ? dir : 0, m.b);
}

/* cal [MONTH YEAR]: a month, Monday first, today in [ ] when the date is known (this month
   if not said: it must be known). */
COLD static void cmd_cal(struct term *t, struct line *l, const char *args) {
    char a[12], b[12], r[24];
    word_of(word_of(args, a, 11), b, 11);
    u64 secs = sys0(SYS_TIME).x[6];
    struct date now = date_of(local_of(secs, secs ? app_zone() : 0));
    long m = a[0] ? number(a) : now.month, y = a[0] ? number(b) : now.year;
    if ((!a[0] && !secs) || m < 1 || m > 12 || y < 1 || y > 9999) {
        usage(t, l, "cal", secs ? "cal [MONTH YEAR]" : "cal MONTH YEAR (the date is not known: try ntp)");
        return;
    }
    struct line title = {.n = 0};
    put_s(&title, month_names[m - 1]);
    put_s(&title, " ");
    put_dec(&title, (u64)y);
    title.b[title.n] = 0;
    pad_to(l, (21 - title.n) / 2);
    put_s(l, title.b);
    out(t, l);
    say(t, " Mo Tu We Th Fr Sa Su");
    int first = (weekday_of(days_of(y, (int)m, 1)) + 6) % 7, days = month_days(y, (int)m);
    int today = secs && now.year == y && now.month == m ? now.day : 0;
    for (int week = 1 - first; week <= days; week += 7) {
        int end = 0;
        for (int i = 0; i < 23; i++) r[i] = ' ';
        for (int i = 0; i < 7; i++) {
            int day = week + i;
            if (day < 1 || day > days) continue;
            r[3 * i + 1] = day < 10 ? ' ' : (char)('0' + day / 10);
            r[3 * i + 2] = (char)('0' + day % 10);
            end = 3 * i + 3;
            if (day == today) r[3 * i] = '[', r[end++] = ']';
        }
        r[end] = 0;
        say(t, r);
    }
    fs_log(l, "cal", 0, title.b);
}

/* sleep N: wait N seconds (60 at most); Terminal answers nothing meanwhile. */
COLD static void cmd_sleep(struct term *t, struct line *l, const char *args) {
    char a[12];
    word_of(args, a, 11);
    long s = number(a);
    if (s < 0 || s > 60) { usage(t, l, "sleep", "sleep N, 0 to 60 seconds"); return; }
    sleep_ms((u64)s * 1000);
    log_count(l, "sleep", (u64)s, "second");
}

/* calc EXPR: whole numbers with + - * / % and ( ), as C has them (64 bits, wrapping). */
struct expr { const char *p; const char *why; };

COLD static long ex_sum(struct expr *e);

COLD static char ex_peek(struct expr *e) {
    while (*e->p == ' ') e->p++;
    return *e->p;
}

COLD static long ex_atom(struct expr *e) {
    char c = ex_peek(e);
    u64 v = 0;
    e->p++;
    if (c == '-') return (long)(0 - (u64)ex_atom(e));
    if (c == '+') return ex_atom(e);
    if (c == '(') {
        long r = ex_sum(e);
        if (ex_peek(e) != ')') e->why = "a ( without its )";
        else e->p++;
        return r;
    }
    if (c < '0' || c > '9') { e->why = "not understood"; e->p--; return 0; }
    for (e->p--; *e->p >= '0' && *e->p <= '9'; e->p++) v = v * 10 + (u64)(*e->p - '0');
    return (long)v;
}

COLD static long ex_product(struct expr *e) {
    long v = ex_atom(e);
    for (char c; !e->why && ((c = ex_peek(e)) == '*' || c == '/' || c == '%');) {
        e->p++;
        long r = ex_atom(e);
        if (c == '*') v = (long)((u64)v * (u64)r);
        else if (!r) e->why = "division by zero";
        else if (r == -1) v = c == '/' ? (long)(0 - (u64)v) : 0;
        else v = c == '/' ? v / r : v % r;
    }
    return v;
}

COLD static long ex_sum(struct expr *e) {
    long v = ex_product(e);
    for (char c; !e->why && ((c = ex_peek(e)) == '+' || c == '-');) {
        e->p++;
        long r = ex_product(e);
        v = (long)(c == '+' ? (u64)v + (u64)r : (u64)v - (u64)r);
    }
    return v;
}

COLD static void cmd_calc(struct term *t, struct line *l, const char *args) {
    while (*args == ' ') args++;
    struct expr e = {args, 0};
    long v = ex_sum(&e);
    if (!e.why && ex_peek(&e)) e.why = ex_peek(&e) == ')' ? "a ) without its (" : "not understood";
    if (!*args) e.why = "calc EXPR, such as (2+3)*4";
    if (e.why) { fail(t, e.why); fs_log(l, "calc", *args ? args : 0, e.why); return; }
    if (v < 0) put_s(l, "-");
    put_dec(l, v < 0 ? 0 - (u64)v : (u64)v);
    struct line m = *l;
    m.b[m.n] = 0;
    out(t, l);
    fs_log(l, "calc", args, m.b);
}

COLD static void exec(struct term *t, struct line *l, const char *c);

/* time CMD: CMD, and how long it took, on the screen (not into a file or a pipe). */
COLD static void cmd_time(struct term *t, struct line *l, const char *c) {
    while (*c == ' ') c++;
    if (!*c) { usage(t, l, "time", "time CMD"); return; }
    u64 t0 = millis();
    exec(t, l, c);
    u64 ms = millis() - t0;
    put_s(l, "took ");
    put_dec(l, ms);
    put_s(l, " ms");
    to_screen(t, l->b, l->n, 0);
    l->n = 0;
    put_s(l, "terminal: time ");
    put_s(l, c);
    put_s(l, " -> ");
    put_dec(l, ms);
    put_s(l, " ms\n");
    flush(l);
}

/* kill SLOT: stop the program from the card in open slot SLOT (10 to 15), answering or not.
   Terminal holds those slots' launch capabilities; the kernel lets nothing else stop them
   (`only_launchers_stop`). What the file server gave the slot is taken back too, whether a
   program was still running there or had ended by itself. */
COLD static void cmd_kill(struct term *t, struct line *l, const char *args) {
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
    fs_unshare(&t->fs, k);
    say(t, r.status == OK ? "stopped" : "nothing running there");
    fs_log(l, "kill", num, r.status == OK ? "stopped" : "nothing running");
}

/* Every program slot and what the kernel says about it. */
COLD static void cmd_ps(struct term *t, struct line *l) {
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
   it on the command line (FS_GRANTS_PER_SLOT - 1 at most: cmd_run checks), read-write;
   nothing else. Whatever the slot's last program was given is taken back first. */
COLD static void give(struct term *t, struct line *l, u64 slot, const char *name, const char *files) {
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

COLD static void cmd_run(struct term *t, struct line *l, const char *args) {
    char name[FS_NAME_MAX + 1];
    /* -net: let it use the network (the USB driver answers only the program allowed) */
    while (*args == ' ') args++;
    int net = args[0] == '-' && args[1] == 'n' && args[2] == 'e' && args[3] == 't' && (args[4] == ' ' || !args[4]);
    if (net) args += 4;
    const char *files = word_of(args, name, FS_NAME_MAX);
    /* the file server keeps FS_GRANTS_PER_SLOT paths for each slot: its folder, and 7 files */
    int named = 0;
    char word[FS_PATH_MAX + 1];
    for (const char *w = files; w = word_of(w, word, FS_PATH_MAX), word[0];) named++;
    if (named > FS_GRANTS_PER_SLOT - 1) {                               /* 7 */
        say(t, "a program can be given 7 files at most");
        fs_log(l, "run", name, "more than 7 files");
        return;
    }
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
        app_before_start();
        struct res r = sys(SYS_EXEC, LAUNCH_OPEN + (u64)i, (u64)image, len, 0, 0);
        if (r.status != OK) continue;
        /* the network: allowed for this program, or taken from whatever ran here before */
        u64 slot = OPEN_FIRST + (u64)i;
        int netok = net_call(&t->net, NET_ALLOW, slot | (u64)net << 8, 0).x[1] == NET_OK && net;
        put_s(l, "started ");
        put_s(l, name);
        put_s(l, " in slot ");
        put_dec(l, slot);
        if (net) put_s(l, netok ? ", with the network" : ", but the network service did not answer");
        out(t, l);
        put_s(l, "terminal: run ");
        put_s(l, name);
        put_s(l, " -> slot ");
        put_dec(l, slot);
        if (netok) put_s(l, ", with the network");
        put_s(l, "\n");
        flush(l);
        return;
    }
    say(t, "no free slot: close a program first");
    fs_log(l, "run", name, "no free slot");
}

/* One command: its name, then what follows it. */
COLD static void exec(struct term *t, struct line *l, const char *c) {
    while (*c == ' ') c++;
    if (!*c) return;
    if (starts(c, "help")) {
        say(t, "whoami caps boot ps uptime echo clear exit history");
        say(t, "ls [-a] [DIR], cat, write FILE TEXT, rm, touch, stat");
        say(t, "mkdir, cd, pwd, mv FROM TO, cp FROM TO, du, tree, df");
        say(t, "head, tail [-n N], wc, grep [-i] TEXT, calc EXPR");
        say(t, "sort [-r] [-n], uniq [-c], rev, nl, tr A B, tee FILE");
        say(t, "cut [-d C] -f N, seq [A] B, cal [M Y], sleep N");
        say(t, "CMD > FILE (>> adds), CMD | CMD2: filters read a |");
        say(t, "find [DIR] [NAME], time CMD, !! and !N: history");
        say(t, "run [-net] PROGRAM [FILE...], kill SLOT, date, ntp");
        say(t, "fill FILE KB CHAR, verify FILE, ip, ping, get URL");
        say(t, "tour: why leanos is harder to attack than Linux");
        say(t, "Up, Down: earlier commands; Tab completes names");
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
    } else if (starts(c, "cp")) {
        cmd_cp(t, l, c + 2);
    } else if (starts(c, "head")) {
        cmd_ends(t, l, c + 4, 0);
    } else if (starts(c, "tail")) {
        cmd_ends(t, l, c + 4, 1);
    } else if (starts(c, "wc")) {
        cmd_wc(t, l, c + 2);
    } else if (starts(c, "grep")) {
        cmd_grep(t, l, c + 4);
    } else if (starts(c, "find")) {
        cmd_find(t, l, c + 4);
    } else if (starts(c, "df")) {
        cmd_df(t, l);
    } else if (starts(c, "history")) {
        cmd_history(t, l);
    } else if (starts(c, "sort")) {
        cmd_sort(t, l, c + 4);
    } else if (starts(c, "uniq")) {
        cmd_uniq(t, l, c + 4);
    } else if (starts(c, "rev")) {
        cmd_lines(t, l, c + 3, REV);
    } else if (starts(c, "tr")) {
        cmd_lines(t, l, c + 2, TR);
    } else if (starts(c, "cut")) {
        cmd_lines(t, l, c + 3, CUT);
    } else if (starts(c, "nl")) {
        cmd_lines(t, l, c + 2, NL);
    } else if (starts(c, "tee")) {
        cmd_tee(t, l, c + 3);
    } else if (starts(c, "seq")) {
        cmd_seq(t, l, c + 3);
    } else if (starts(c, "touch")) {
        cmd_touch(t, l, c + 5);
    } else if (starts(c, "stat")) {
        cmd_stat(t, l, c + 4);
    } else if (starts(c, "du")) {
        cmd_du(t, l, c + 2, 0);
    } else if (starts(c, "tree")) {
        cmd_du(t, l, c + 4, 1);
    } else if (starts(c, "cal")) {
        cmd_cal(t, l, c + 3);
    } else if (starts(c, "calc")) {
        cmd_calc(t, l, c + 4);
    } else if (starts(c, "sleep")) {
        cmd_sleep(t, l, c + 5);
    } else if (starts(c, "time")) {
        cmd_time(t, l, c + 4);
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

/* The commands Tab completes: every one help lists. */
static const char COMMANDS[] = "boot cal calc caps cat cd clear cp cut date df du echo exit fill find get "
                               "grep head help history ip kill ls mkdir mv nl ntp ping ps pwd rev rm run "
                               "seq sleep sort stat tail tee time touch tour tr tree uniq uptime verify "
                               "wc whoami write";
/* What > and | refuse: commands that start or stop programs, or change Terminal itself. */
static const char UNPIPED[] = "cd clear exit kill run tour";

/* Whether `w` is one of the words in `list`. */
COLD static int listed(const char *list, const char *w) {
    char c[8];
    while (*list) { list = word_of(list, c, 7); if (same(c, w)) return 1; }
    return 0;
}

/* The command line: one command, or several joined by | (each one's output the next one's
   input), the last one's output going to the screen or, after > or >>, into a file. */
COLD static void run(struct term *t, struct line *l) {
    char s[CMD_MAX + 1], file[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1], tmp[FS_PATH_MAX + 7], w[16], bad[48];
    int len = scopy(s, t->cmd), ns = 1, to = 0;     /* to: 1 after >, 2 after >> */
    char *stage[CMD_MAX + 1], *target = 0;
    const char *why = 0;
    stage[0] = s;
    for (int i = 0; i < len; i++) {
        char c = s[i];
        if (c != '|' && c != '>') continue;
        s[i] = 0;
        if (target) why = "> FILE goes at the end, once";
        else if (c == '|') stage[ns++] = s + i + 1;
        else {
            to = s[i + 1] == '>' ? 2 : 1;
            if (to == 2) s[++i] = 0;
            target = s + i + 1;
        }
    }
    if (ns == 1 && !to) { exec(t, l, s); return; }
    if (to && (*word_of(target, file, FS_PATH_MAX) || !file[0]) && !why) why = "> needs one file name";
    for (int i = 0; i < ns && !why; i++) {
        for (int n = (int)slen(stage[i]); n > 0 && stage[i][n - 1] == ' ';) stage[i][--n] = 0;
        const char *rest = word_of(stage[i], w, 15);
        while (same(w, "time")) rest = word_of(rest, w, 15);   /* time CMD: CMD is what is checked */
        if (!w[0]) why = ns > 1 ? "| needs a command on both sides" : "> needs a command before it";
        else if (!listed(COMMANDS, w)) scopy(bad + scopy(bad, "not a command: "), w), why = bad;
        else if (listed(UNPIPED, w)) scopy(bad + scopy(bad, w), " cannot be piped or redirected"), why = bad;
    }
    const char *op = to == 2 ? ">>" : to ? ">" : "|";
    if (!why && to) {
        resolve(t, file, path);
        const char *in_way = tmp_of(t, path, tmp);
        if (fs_stat(&t->fs, path, 0) == FS_DIR) why = "a folder, not a file";
        else if (to == 1) why = in_way;
    }
    if (why) {
        say(t, why);
        const char *c = t->cmd;
        while (*c == ' ') c++;
        fs_log(l, c, 0, why);
        return;
    }
    /* each command in turn, its output captured for the next (or the file) */
    t->inn = 0;
    int stop = 0;
    for (int i = 0; i < ns && !stop; i++) {
        t->capture = i < ns - 1 || to;
        t->capn = 0;
        t->over = t->failed = t->joined = 0;
        t->piped = i > 0;
        exec(t, l, stage[i]);
        t->inn = t->capn;
        stop = t->over || t->failed;
    }
    t->capture = t->piped = 0;
    if (stop) {
        if (t->over) say(t, "more than 64 KiB of output: stopped");
        if (to) say(t, "nothing written");
        fs_log(l, op, to ? file : 0, t->over ? "stopped, more than 64 KiB of output" : "stopped, the command failed");
        return;
    }
    if (!to) return;
    /* into the file: > through FILE.part~ and one rename, >> at its end */
    u64 n = t->capn, st = save(t, path, tmp, pipe_buf(), n, to == 2);
    if (st != FS_OK) {
        put_s(l, "not written: ");
        put_s(l, fs_error(st));
        out(t, l);
    }
    struct line m = {.n = 0};
    if (st == FS_OK) { put_dec(&m, n); put_s(&m, n == 1 ? " byte" : " bytes"); }
    else { put_s(&m, "not written: "); put_s(&m, fs_error(st)); }
    m.b[m.n] = 0;
    fs_log(l, op, file, m.b);
}

/* !! and !N on the command line, as a shell has them: the last command, and command N of
   the list history shows. The line, with them in its place, is what shows, runs and is kept
   for Up. 0, or why it cannot be. */
COLD static const char *bang(struct term *t, struct line *l) {
    char s[CMD_MAX + 1];
    int n = 0, any = 0;
    for (const char *c = t->cmd; *c; c++) {
        const char *h = 0;
        if (c[0] == '!' && c[1] == '!') {
            if (!t->hn) return "!!: no command before";
            h = t->hist[t->hn - 1];
            c++;
        } else if (c[0] == '!' && c[1] >= '0' && c[1] <= '9') {
            int k = 0;
            while (c[1] >= '0' && c[1] <= '9')
                if (*++c && k <= HIST) k = k * 10 + (*c - '0');
            if (k < 1 || k > t->hn) return "!N: no command N in history";
            h = t->hist[k - 1];
        }
        if (!h) h = (char[2]){*c, 0};
        else any = 1;
        while (*h) {
            if (n == CMD_MAX) return "too long with !! or !N in it";
            s[n++] = *h++;
        }
    }
    if (!any) return 0;
    s[n] = 0;
    fs_log(l, t->cmd, 0, s);
    t->len = t->cur = scopy(t->cmd, s);
    return 0;
}

/* Return: the line into the scrollback and history, and run. */
COLD static void enter(struct term *t, struct line *l) {
    t->cmd[t->len] = 0;
    const char *why = bang(t, l);
    push(t, t->cmd, (u64)t->len, 1);
    if (why) {
        say(t, why);
        fs_log(l, t->cmd, 0, why);
        return;
    }
    remember(t);
    run(t, l);
}

/* ---- Tab completion ---- */

/* The name before the cursor (`pre`), and the names that start with it: how many, and what
   they all share (a folder's name ends in '/'). On the listing pass, the names themselves,
   as rows of the scrollback and on the log line. */
struct comp {
    char pre[FS_NAME_MAX + 1];
    int pn, count, cn, listing;
    char common[FS_NAME_MAX + 2];
    struct line row, *log;
};

COLD static void consider(struct term *t, struct comp *c, const char *name, int dir) {
    for (int i = 0; i < c->pn; i++) if (name[i] != c->pre[i]) return;
    char full[FS_NAME_MAX + 2];
    int n = scopy(full, name);
    if (dir) full[n++] = '/';
    full[n] = 0;
    if (c->listing) {
        if (c->row.n && c->row.n + 2 + (u64)n > COLS) out(t, &c->row);
        if (c->row.n) put_s(&c->row, "  ");
        put_s(&c->row, full);
        if (c->log->n + (u64)n < 180) { put_s(c->log, " "); put_s(c->log, full); }
        return;
    }
    if (!c->count++) c->cn = scopy(c->common, full);
    else { int k = 0; while (k < c->cn && c->common[k] == full[k]) k++; c->cn = k; }
}

/* Every command name, or every name in the folder `dir`, through consider(). */
COLD static void scan(struct term *t, struct comp *c, int command, const char *dir) {
    if (command) {
        char w[8];
        for (const char *p = COMMANDS; *p;) { p = word_of(p, w, 7); consider(t, c, w, 0); }
        return;
    }
    u64 total = 0, from = 0;
    for (;;) {
        long n = fs_list_dir(&t->fs, dir, from, &total);
        if (n <= 0) return;
        const struct fs_entry *e = fs_entries(&t->fs);
        for (long i = 0; i < n; i++) consider(t, c, e[i].name, e[i].kind == FS_DIR);
        from += (u64)n;
        if (from >= total) return;
    }
}

/* Tab: complete the word before the cursor, a command's name if it is the first on the
   line or after a |, else a name in the folder it names (the current one if none). `again`:
   the key before was Tab too, so if nothing more can be completed, list what matches. Tab
   is rare and Terminal's code run is nearly full (64 KiB), so these are built for size. */
COLD static void complete(struct term *t, struct line *l, int again) {
    t->cmd[t->len] = 0;
    int start = t->cur;
    while (start > 0 && t->cmd[start - 1] != ' ' && t->cmd[start - 1] != '|' && t->cmd[start - 1] != '>') start--;
    /* a command's name: first on the line, or after a | */
    int before = start;
    while (before > 0 && t->cmd[before - 1] == ' ') before--;
    int command = !before || t->cmd[before - 1] == '|';
    int base = t->cur;
    while (base > start && t->cmd[base - 1] != '/') base--;
    command &= base == start;          /* a path is never a command's name */
    struct comp c = {.pn = t->cur - base};
    if (c.pn > FS_NAME_MAX) return;
    for (int i = 0; i < c.pn; i++) c.pre[i] = t->cmd[base + i];
    c.pre[c.pn] = 0;
    /* the folder: the word up to its last '/', without it (unless that is all: the top) */
    char dir[FS_PATH_MAX + 1], path[FS_PATH_MAX + 1];
    int dn = base - start > FS_PATH_MAX ? FS_PATH_MAX : base - start;
    for (int i = 0; i < dn; i++) dir[i] = t->cmd[start + i];
    dir[dn > 1 ? dn - 1 : dn] = 0;
    resolve(t, dir, path);
    scan(t, &c, command, path);
    const char *name = c.pn ? c.pre : 0;
    if (!c.count) { fs_log(l, "completed", name, "no match"); return; }
    c.common[c.cn] = 0;
    int add = c.cn - c.pn;
    for (int i = c.pn; i < c.cn; i++) insert(t, c.common[i]);
    /* one file or command: a space after it, as a shell does */
    if (c.count == 1 && c.common[c.cn - 1] != '/' && (t->cur == t->len || t->cmd[t->cur] != ' ')) {
        insert(t, ' ');
        add++;
    }
    if (add) { fs_log(l, "completed", name, c.common); return; }
    if (c.count == 1 || !again) return;
    /* like a shell: the line as typed, then every name that matches */
    push(t, t->cmd, (u64)t->len, 1);
    put_s(l, "terminal: completions");
    if (name) { put_s(l, " for "); put_s(l, name); }
    put_s(l, " -> ");
    put_dec(l, (u64)c.count);
    put_s(l, ":");
    c.listing = 1;
    c.log = l;
    scan(t, &c, command, path);
    if (c.row.n) out(t, &c.row);
    put_s(l, "\n");
    flush(l);
}

/* Ctrl+C: the command line, if something is typed on it, else what the last command printed. */
COLD static void copy_out(struct term *t, struct line *l) {
    char buf[ROWS * (COLS + 1)];
    u64 n = 0;
    const char *what = "the command line";
    if (t->len) {
        for (int i = 0; i < t->len; i++) buf[n++] = t->cmd[i];
    } else {
        int from = t->n;
        while (from > 0 && !t->kind[from - 1]) from--;
        for (int i = from; i < t->n; i++) {
            if (i > from && !t->cont[i]) buf[n++] = '\n';
            for (int j = 0; t->text[i][j]; j++) buf[n++] = t->text[i][j];
        }
        what = "the last command's output";
    }
    u64 st = app_copy(buf, n);
    put_s(l, "terminal: copied ");
    put_s(l, what);
    put_s(l, ", ");
    put_dec(l, n);
    put_s(l, " bytes");
    put_s(l, outcome(st));
    put_s(l, "\n");
    flush(l);
}

/* Ctrl+V: a piece of the paste onto the command line; when it ends, say what arrived. */
COLD static int paste_in(struct term *t, struct line *l, struct event e) {
    char piece[16];
    int k = paste_text(e, piece);
    if (t->paste_from < 0) { t->paste_from = t->cur; t->dropped = 0; }
    for (int i = 0; i < k; i++) {
        char c = piece[i] == '\n' || piece[i] == '\r' || piece[i] == '\t' ? ' ' : piece[i];
        if (c < 32 || c > 126) continue;
        if (t->len < CMD_MAX) insert(t, c);
        else t->dropped++;
    }
    if (k == 16) return 0;
    /* what arrived: from where the paste began to the cursor */
    char after = t->cmd[t->cur];
    t->cmd[t->cur] = 0;
    put_s(l, "terminal: pasted ");
    put_dec(l, (u64)(t->cur - t->paste_from));
    put_s(l, " bytes: ");
    put_s(l, t->cmd + t->paste_from);
    t->cmd[t->cur] = after;
    put_s(l, "\n");
    flush(l);
    if (t->dropped) {
        put_s(l, "terminal: ");
        put_dec(l, (u64)t->dropped);
        put_s(l, " more bytes did not fit on the command line\n");
        flush(l);
    }
    t->paste_from = -1;
    return 1;
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
    t->n = t->len = t->cur = t->hn = t->hpos = t->tabbed = 0;
    t->paste_from = -1;
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
        if (e.kind == EV_COPY) {
            copy_out(t, &l);
            continue;
        }
        if (e.kind == EV_PASTE) {
            if (paste_in(t, &l, e)) {        /* drawn once, when the last piece is in */
                draw(t);
                dirty = 1;
            }
            continue;
        }
        if (e.kind != EV_KEY) continue;
        u64 k = e.a;
        if (k == '\t') complete(t, &l, t->tabbed);
        else if (k == KEY_UP || k == KEY_DOWN) recall(t, t->hpos + (k == KEY_UP ? -1 : 1));
        else if (k == KEY_LEFT) t->cur -= t->cur > 0;
        else if (k == KEY_RIGHT) t->cur += t->cur < t->len;
        else if (k == KEY_HOME) t->cur = 0;
        else if (k == KEY_END) t->cur = t->len;
        else if (k == KEY_DELETE) {
            if (t->cur < t->len) {
                for (int i = t->cur + 1; i < t->len; i++) t->cmd[i - 1] = t->cmd[i];
                t->len--;
            }
        } else if (k == 8 || k == 127) {
            if (t->cur > 0) {
                for (int i = t->cur; i < t->len; i++) t->cmd[i - 1] = t->cmd[i];
                t->cur--;
                t->len--;
            }
        } else if (k == '\r' || k == '\n') {
            enter(t, &l);
            t->len = t->cur = 0;
        } else if (k >= 32 && k < 127) insert(t, (char)k);
        else continue;
        t->tabbed = k == '\t';
        draw(t);
        dirty = 1;
    }
}
