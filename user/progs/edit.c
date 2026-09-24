/* edit: a text editor, from the SD card. It edits the file it was given (`run edit
   notes.txt` in Terminal gives it notes.txt), or, given none, apps/edit/untitled.txt in its
   own folder; the file server lets it reach nothing else, and says so if it tries.

   Type to insert, Backspace deletes, Enter starts a line, the arrow keys move. It saves by
   itself a moment after you stop typing, the whole file in one request, which the file
   server writes as one journaled change: after a power cut the file is the last save or
   the one before, never half of each. A file holds up to 16 KiB (one request). */
#include "../ui.h"
#include "../fs.h"

#define EW 520
#define EH 300               /* 152 pages of pixels */
#define PAD 12
#define STATUS_H 24
#define LINE_H 18
#define TEXT_MAX FS_CHUNK
#define SAVE_AFTER 800       /* ms without typing */

struct edit {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    char path[FS_PATH_MAX + 1];
    char text[TEXT_MAX + 1];
    long len, cur, top;      /* the text, the cursor, the first line shown */
    int cw;                  /* a character's width in the monospaced font */
    int dirty, full;
    u64 changed;             /* when the text last changed (ms) */
    u64 saves;
    char status[96];
};

static void set_status(struct edit *e, const char *a, const char *b) {
    int n = 0;
    for (int i = 0; a[i] && n < 95; i++) e->status[n++] = a[i];
    for (int i = 0; b && b[i] && n < 95; i++) e->status[n++] = b[i];
    e->status[n] = 0;
}

static long line_start(struct edit *e, long at) {
    while (at > 0 && e->text[at - 1] != '\n') at--;
    return at;
}
static long line_end(struct edit *e, long at) {
    while (at < e->len && e->text[at] != '\n') at++;
    return at;
}
static long line_of(struct edit *e, long at) {
    long n = 0;
    for (long i = 0; i < at; i++) n += e->text[i] == '\n';
    return n;
}

static void draw(struct edit *e) {
    struct surface *s = &e->win;
    fill(s, 0, 0, EW, EH, rgb(252, 252, 250));
    int rows = (EH - STATUS_H - PAD) / LINE_H;
    long cl = line_of(e, e->cur);
    if (cl < e->top) e->top = cl;
    if (cl >= e->top + rows) e->top = cl - rows + 1;
    long line = 0, i = 0;
    while (line < e->top && i < e->len) { if (e->text[i] == '\n') line++; i++; }
    int cols = (EW - 2 * PAD) / e->cw;
    for (int r = 0; r < rows && i <= e->len; r++) {
        int y = PAD + LINE_H * r + 13, x = PAD;
        long end = line_end(e, i);
        for (long k = i; k <= end; k++) {
            if (k == e->cur) fill(s, x, y - 13, 2, LINE_H - 2, rgb(58, 110, 230));
            if (k == end) break;
            if ((k - i) < cols) {
                char c[2] = {e->text[k] >= 32 && e->text[k] < 127 ? e->text[k] : '?', 0};
                font_text(s, &e->ui.mono, x, y, c, rgb(36, 38, 46));
                x += e->cw;
            }
        }
        i = end + 1;
        if (end >= e->len) break;
    }
    fill(s, 0, EH - STATUS_H, EW, STATUS_H, rgb(238, 239, 243));
    font_text(s, &e->ui.small_bold, PAD, EH - 8, e->path, rgb(60, 62, 74));
    font_text(s, &e->ui.small, EW - PAD - font_width(&e->ui.small, e->status), EH - 8, e->status, rgb(120, 122, 134));
}

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static void save(struct edit *e, struct line *l) {
    u64 st = fs_write(&e->fs, e->path, e->text, (u64)e->len);
    e->dirty = 0;
    e->saves++;
    set_status(e, st == FS_OK ? "saved" : st == FS_DENIED ? "not given to edit: not saved" : "could not save", 0);
    put_s(l, "edit: saved ");
    put_s(l, e->path);
    put_s(l, " (");
    put_dec(l, (u64)e->len);
    put_s(l, st == FS_OK ? " bytes)" : " bytes) -> refused");
    say(l);
}

static void insert(struct edit *e, char c) {
    if (e->len >= TEXT_MAX) { set_status(e, "full: 16 KiB", 0); e->full = 1; return; }
    for (long i = e->len; i > e->cur; i--) e->text[i] = e->text[i - 1];
    e->text[e->cur++] = c;
    e->len++;
}

static void key(struct edit *e, u64 k) {
    long ls = line_start(e, e->cur), col = e->cur - ls;
    if (k == 127 || k == 8) {
        if (e->cur == 0) return;
        for (long i = e->cur - 1; i < e->len - 1; i++) e->text[i] = e->text[i + 1];
        e->cur--;
        e->len--;
    } else if (k == '\r' || k == '\n') {
        insert(e, '\n');
    } else if (k == KEY_LEFT) {
        if (e->cur > 0) e->cur--;
        return;
    } else if (k == KEY_RIGHT) {
        if (e->cur < e->len) e->cur++;
        return;
    } else if (k == KEY_UP) {
        if (ls == 0) return;
        long ps = line_start(e, ls - 1), pe = ls - 1;
        e->cur = ps + col < pe ? ps + col : pe;
        return;
    } else if (k == KEY_DOWN) {
        long le = line_end(e, e->cur);
        if (le >= e->len) return;
        long ne = line_end(e, le + 1);
        e->cur = le + 1 + col < ne ? le + 1 + col : ne;
        return;
    } else if (k >= 32 && k < 127) {
        insert(e, (char)k);
    } else return;
    e->dirty = 1;
    e->changed = millis();
    set_status(e, "editing", 0);
}

/* The file it was given: the first file among its grants that is not in its own folder,
   else untitled.txt in its folder. */
static void choose(struct edit *e) {
    char list[2048];
    long n = fs_grants(&e->fs);
    const char *g = fs_data(&e->fs);
    for (int k = 0; k < (int)sizeof list; k++) list[k] = g[k];     /* the buffer is about to be reused */
    const char *p = list;
    for (long i = 0; i < n && p < list + sizeof list - 1; i++) {
        const char *path = p + 1;                                  /* after the rights byte */
        int len = 0;
        while (path[len]) len++;
        int own = len >= 5 && path[0] == 'a' && path[1] == 'p' && path[2] == 'p' && path[3] == 's' && path[4] == '/';
        if (!own && fs_stat(&e->fs, path, 0) != FS_DIR) {
            for (int k = 0; k <= len; k++) e->path[k] = path[k];
            return;
        }
        p = path + len + 1;
    }
    const char *d = "apps/edit/untitled.txt";
    int k = 0;
    for (; d[k]; k++) e->path[k] = d[k];
    e->path[k] = 0;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct edit *e = (struct edit *)DATA;
    struct line l = {.n = 0};
    ui_load(&e->ui, app_assets());
    e->win = app_surface(EW, EH);
    fs_init(&e->fs, SPARE_PAGE);
    e->cw = font_width(&e->ui.mono, "M");
    e->len = e->cur = e->top = 0;
    e->dirty = e->full = 0;
    e->saves = 0;
    choose(e);
    long n = fs_read_all(&e->fs, e->path, e->text, TEXT_MAX);
    if (n >= 0) {
        e->len = n;
        set_status(e, "opened", 0);
    } else {
        u64 size = 0;
        set_status(e, fs_stat(&e->fs, e->path, &size) ? "too large to edit here" : "new file", 0);
    }
    put_s(&l, "edit: opened ");
    put_s(&l, e->path);
    put_s(&l, " (");
    put_dec(&l, (u64)e->len);
    put_s(&l, " bytes)");
    say(&l);
    draw(e);
    u64 opened = app_open(EW, EH, "Edit");
    put_s(&l, "edit: opened a window");
    put_s(&l, outcome(opened));
    say(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        struct event ev = app_poll(dirty);
        dirty = 0;
        if (ev.kind == EV_CLOSE) {
            if (e->dirty) save(e, &l);
            put_s(&l, "edit: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (ev.kind == EV_KEY) {
            key(e, ev.a);
            draw(e);
            dirty = 1;
            continue;
        }
        if (ev.kind == EV_NONE) {
            if (e->dirty && millis() - e->changed >= SAVE_AFTER) {
                save(e, &l);
                draw(e);
                dirty = 1;
            } else sleep_ms(30);
        }
    }
}
