/* Files. Lists a folder of what the file server holds and shows the selected file, and
   changes what is there. Click a file, or use the up and down arrows (the list scrolls), to
   show it; click a folder, or press Enter or the right arrow on it, to open it; the left
   arrow goes back up; click anywhere else to look again. The keys (either case):

     N       a new folder, "untitled folder" (or "untitled folder 2", ...), named at once
             (the + Folder button too)
     R       rename the selected file or folder, in its row: type, Left and Right move the
             cursor, Return keeps the name, Escape (or a click elsewhere) cancels. The name
             starts selected (a file's without its extension): typing replaces it.
     C, X    mark the selected file to copy, or the file or folder to move (the same key
             again forgets it; Escape too)
     V       put what is marked in the folder shown: a copy (in pieces into NAME.part~, then
             one rename, as Terminal's cp makes one; "NAME copy" if the name is taken), or
             the file or folder itself (one rename in the file server: a folder takes all
             in it along)
     Delete  (or Backspace) removes the selected file or empty folder; a folder with things
             in it asks first, and Delete again removes it and all in it

   The mark is Files' own, not the clipboard. While a name is edited, Ctrl+V pastes text
   into it and Ctrl+C copies it, as in any text field. The status line at the bottom says
   what the keys do, what is marked, and how much of the card is free (the file server's
   totals). Programs' icons (NAME.icon, fs.h) are not listed. Files reaches the files only
   by asking the file server, one request at a time, and lists the folder again after every
   change. */
#include "ui.h"
#include "fs.h"

#define COLD __attribute__((cold, minsize))

#define FW 460
#define FH 340
#define LIST_W 184
#define ROW_H 22
#define ROW_Y 40
#define MAX_SHOWN 12
#define PREVIEW_MAX 4096
#define STATUS_Y (FH - 26)           /* the status line, across the window's foot */
#define EDIT_MAX 80                  /* what the name field holds: more than a name may have */
#define BTN_W 66                     /* the + Folder button, right of the list's heading */
#define BTN_X (LIST_W - 8 - BTN_W)
#define BTN_Y 11
#define BTN_H 20
enum { F_UI = 1, F_BOLD = 2, F_SMALL = 3, F_MONO = 4 };

struct files {
    struct font ui, bold, small, mono;
    struct surface win;
    struct fs_client fs;
    struct fs_entry list[128];
    long count;
    char dir[FS_PATH_MAX + 1];      /* the folder shown: "" is the top */
    char path[FS_PATH_MAX + 1];     /* scratch: dir + '/' + a name */
    char from[FS_PATH_MAX + 1], to[FS_PATH_MAX + 1], tmp[FS_PATH_MAX + 1];   /* scratch */
    int selected;                   /* -1: none */
    int top;                        /* the first file the list shows */
    char preview[PREVIEW_MAX + 1];
    long size;                      /* of the selected file, -1 if it could not be read */
    /* the selected entry's name, being edited in its row: the text, its length, the cursor,
       and how much of its start is selected (0: none) */
    int editing;
    char edit[EDIT_MAX + 1];
    int elen, cur, sel;
    int mark;                       /* 'c' or 'x': `marked` is to be copied or moved; 0: none */
    char marked[FS_PATH_MAX + 1];
    int confirm;                    /* Delete once more removes the selected folder and all in it */
    char msg[120];                  /* the status line's news, until the next key or click */
    int msg_bad;
    struct fs_space space;
    int space_ok;
    unsigned free_said;             /* the free KiB last logged */
};

static int same(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == *b;
}

static void scopy(char *d, const char *s) { while ((*d++ = *s++)) {} }

/* dir + '/' + name (name alone at the top) into out; 0 if it is too long for a path. */
static int join(char *out, const char *dir, const char *name) {
    int n = 0;
    for (; dir[n]; n++) out[n] = dir[n];
    if (n) out[n++] = '/';
    for (int k = 0; name[k]; k++) {
        if (n >= FS_PATH_MAX) { out[n] = 0; return 0; }
        out[n++] = name[k];
    }
    out[n] = 0;
    return 1;
}

static const char *last_name(const char *p) {
    const char *last = p;
    for (; *p; p++) if (*p == '/') last = p + 1;
    return last;
}

/* The path of entry i in the folder shown. */
static const char *path_of(struct files *st, int i) {
    join(st->path, st->dir, st->list[i].name);
    return st->path;
}

static void size_text(char *out, unsigned n) {
    char t[12];
    int i = 0;
    do { t[i++] = (char)('0' + n % 10); n /= 10; } while (n);
    int k = 0;
    while (i) out[k++] = t[--i];
    out[k++] = ' ';
    out[k++] = 'B';
    out[k] = 0;
}

/* The parts that are there, after what the line holds already, as one line of the log. */
static void say(struct line *l, const char *a, const char *b, const char *c, const char *d) {
    const char *parts[4] = {a, b, c, d};
    for (int i = 0; i < 4; i++) if (parts[i]) put_s(l, parts[i]);
    put_s(l, "\n");
    flush(l);
}

/* News for the status line (bad: in red). */
static void tell(struct files *st, int bad, const char *a, const char *b, const char *c) {
    const char *parts[3] = {a, b, c};
    int n = 0;
    for (int i = 0; i < 3; i++)
        for (const char *p = parts[i]; p && *p && n < (int)sizeof st->msg - 1; p++) st->msg[n++] = *p;
    st->msg[n] = 0;
    st->msg_bad = bad;
}

COLD static const char *why(u64 code) {
    return code == FS_NOT_FOUND ? "not found" : code == FS_FULL ? "the card is full"
         : code == FS_EXISTS ? "that name is taken" : code == FS_NOT_EMPTY ? "the folder is not empty"
         : code == FS_IO ? "the card failed" : code == FS_NO_SERVER ? "the file server did not answer"
         : code == FS_BAD ? "a folder cannot go inside itself" : "not allowed";
}

/* The width of the first n bytes of str. */
static int width_of(const struct font *f, const char *str, int n) {
    char t[EDIT_MAX + 1];
    int k = 0;
    for (; k < n && k < EDIT_MAX && str[k]; k++) t[k] = str[k];
    t[k] = 0;
    return font_width(f, t);
}

/* A key's name, dark, then what it does, gray: the status line's hints. Returns the x after. */
static int hint(struct files *st, int x, const char *key, const char *does) {
    struct surface *s = &st->win;
    x = font_text(s, &st->small, x, FH - 9, key, rgb(40, 40, 48));
    x = font_text(s, &st->small, x + 4, FH - 9, does, rgb(130, 130, 140));
    return x + 12;
}

static void draw_status(struct files *st) {
    struct surface *s = &st->win;
    fill(s, 0, STATUS_Y, FW, FH - STATUS_Y, rgb(236, 236, 240));
    fill(s, 0, STATUS_Y, FW, 1, rgb(220, 220, 226));
    int right = FW - 12;
    if (st->space_ok) {
        struct line t = {.n = 0};
        u64 kib = (u64)st->space.free * st->space.cluster / 1024;
        if (kib >= 10240) put_dec(&t, kib / 1024);
        else if (kib >= 1024) { put_dec(&t, kib / 1024); put_s(&t, "."); put_dec(&t, kib % 1024 * 10 / 1024); }
        else put_dec(&t, kib);
        put_s(&t, kib >= 1024 ? " MiB free" : " KiB free");
        t.b[t.n] = 0;
        right -= font_width(&st->small, t.b);
        font_text(s, &st->small, right, FH - 9, t.b, rgb(130, 130, 140));
        right -= 12;
    }
    clip_to(s, 0, STATUS_Y, right, FH - STATUS_Y);
    int x = 12;
    if (st->confirm) {
        font_text(s, &st->small, x, FH - 9, "Not empty. Delete again deletes it and all in it.",
                  rgb(200, 60, 50));
    } else if (st->msg[0]) {
        font_text(s, &st->small, x, FH - 9, st->msg, st->msg_bad ? rgb(200, 60, 50) : rgb(40, 110, 60));
    } else if (st->editing) {
        x = hint(st, x, "Return", "keeps the name");
        hint(st, x, "Esc", "or a click elsewhere cancels");
    } else if (st->mark) {
        const char *what = st->mark == 'x' ? "Move" : "Copy";
        int w = font_width(&st->small, what) + 12;
        round_rect(s, x, STATUS_Y + 5, w, 17, 8, rgb(58, 110, 230), 255);
        font_text(s, &st->small, x + 6, FH - 9, what, rgb(255, 255, 255));
        x = font_text(s, &st->small, x + w + 6, FH - 9, last_name(st->marked), rgb(40, 40, 48)) + 12;
        x = hint(st, x, "V", st->mark == 'x' ? "moves it here" : "puts a copy here");
        hint(st, x, st->mark == 'x' ? "X" : "C", "again forgets it");
    } else {
        x = hint(st, x, "N", "new folder");
        x = hint(st, x, "R", "rename");
        x = hint(st, x, "C", "copy");
        x = hint(st, x, "X", "move");
        x = hint(st, x, "Del", "delete");
        if (st->dir[0]) hint(st, x, "Left", "up");
    }
    clip_all(s);
}

/* The name being edited, in a white field where the row is, with the cursor or the
   selection; the text slides left when the cursor would be past the field's end. */
static void draw_field(struct files *st, int y) {
    struct surface *s = &st->win;
    round_rect(s, 8, y, LIST_W - 16, ROW_H - 2, 6, rgb(58, 110, 230), 255);
    round_rect(s, 10, y + 2, LIST_W - 20, ROW_H - 6, 4, rgb(255, 255, 255), 255);
    int fx = 14, fw = LIST_W - 30;
    clip_to(s, fx - 1, y + 2, fw + 2, ROW_H - 6);
    st->edit[st->elen] = 0;
    int wc = width_of(&st->ui, st->edit, st->cur), scroll = wc > fw - 2 ? wc - (fw - 2) : 0;
    int x0 = fx - scroll;
    if (st->sel) fill(s, x0, y + 3, width_of(&st->ui, st->edit, st->sel), ROW_H - 8, rgb(179, 206, 252));
    font_text(s, &st->ui, x0, y + 15, st->edit, rgb(30, 30, 36));
    if (!st->sel) fill(s, x0 + wc, y + 4, 1, ROW_H - 10, rgb(30, 30, 36));
    clip_all(s);
}

static void draw(struct files *st) {
    struct surface *s = &st->win;
    fill(s, 0, 0, FW, FH, rgb(255, 255, 255));
    fill(s, 0, 0, LIST_W, STATUS_Y, rgb(243, 243, 246));
    fill(s, LIST_W, 0, 1, STATUS_Y, rgb(224, 224, 230));
    struct line head = {.n = 0};
    if (st->dir[0]) {
        put_s(&head, last_name(st->dir));
        put_s(&head, ": ");
    }
    put_dec(&head, (u64)(st->count < 0 ? 0 : st->count));
    put_s(&head, st->count == 1 ? " file" : " files");
    head.b[head.n < sizeof head.b ? head.n : sizeof head.b - 1] = 0;
    clip_to(s, 0, 0, BTN_X - 4, ROW_Y);
    font_text(s, &st->bold, 16, 26, head.b, rgb(30, 30, 36));
    clip_all(s);
    round_rect(s, BTN_X, BTN_Y, BTN_W, BTN_H, 6, rgb(226, 227, 234), 255);
    font_text(s, &st->small, BTN_X + (BTN_W - font_width(&st->small, "+ Folder")) / 2, BTN_Y + 14, "+ Folder",
              rgb(50, 50, 60));
    if (st->selected >= 0 && st->selected < st->top) st->top = st->selected;
    if (st->selected >= st->top + MAX_SHOWN) st->top = st->selected - MAX_SHOWN + 1;
    for (int r = 0; r < MAX_SHOWN && st->top + r < st->count; r++) {
        int i = st->top + r;
        int y = ROW_Y + r * ROW_H, sel = i == st->selected;
        if (sel && st->editing) { draw_field(st, y); continue; }
        if (sel) round_rect(s, 8, y, LIST_W - 16, ROW_H - 2, 6, rgb(58, 110, 230), 255);
        int folder = st->list[i].kind == FS_DIR, marked = st->mark && same(path_of(st, i), st->marked);
        char n[16];
        const char *right = n;
        if (marked) right = st->mark == 'x' ? "move" : "copy";
        else if (folder) right = "folder";
        else size_text(n, st->list[i].size);
        int rw = font_width(&st->small, right);
        clip_to(s, 0, y, LIST_W - 22 - rw, ROW_H);
        int nx = font_text(s, &st->ui, 16, y + 15, st->list[i].name, sel ? rgb(255, 255, 255) : rgb(40, 40, 48));
        if (folder) font_text(s, &st->ui, nx, y + 15, "/", sel ? rgb(255, 255, 255) : rgb(40, 40, 48));
        clip_all(s);
        font_text(s, &st->small, LIST_W - 16 - rw, y + 14, right,
                  marked ? (sel ? rgb(255, 255, 255) : rgb(58, 110, 230)) : sel ? rgb(220, 230, 255) : rgb(130, 130, 140));
    }
    if (st->count < 0) font_text(s, &st->small, 16, ROW_Y + 16, "The file server did not answer.", rgb(200, 60, 50));
    draw_status(st);

    int x0 = LIST_W + 16, right = FW - 16, bottom = STATUS_Y - 8;
    if (st->selected < 0) {
        font_text(s, &st->ui, x0, 40, "Nothing selected", rgb(150, 150, 160));
        return;
    }
    clip_to(s, 0, 0, FW - 8, STATUS_Y);
    font_text(s, &st->bold, x0, 26, st->list[st->selected].name, rgb(30, 30, 36));
    clip_all(s);
    if (st->list[st->selected].kind == FS_DIR) {
        text_wrap(s, &st->ui, x0, 52, right - x0, 18, "A folder. Press Enter, or click it, to open it.", rgb(110, 110, 120));
        return;
    }
    if (st->size < 0) {
        font_text(s, &st->ui, x0, 52, "Could not read this file.", rgb(200, 60, 50));
        return;
    }
    /* the text, wrapped at word boundaries where it can be, above the status line */
    int x = x0, y = 52;
    const char *p = st->preview;
    while (*p && y < bottom) {
        if (*p == '\n') { x = x0; y += 16; p++; continue; }
        int wl = 0, ww = 0;
        while (p[wl] && p[wl] != ' ' && p[wl] != '\n') {
            char c[2] = {p[wl], 0};
            ww += font_width(&st->mono, c);
            wl++;
        }
        if (x + ww > right && x > x0) { x = x0; y += 16; if (y >= bottom) break; }
        for (int i = 0; i < wl; i++) {
            char c[2] = {p[i], 0};
            if (x + font_width(&st->mono, c) > right) { x = x0; y += 16; }
            if (y >= bottom) break;
            x = font_text(s, &st->mono, x, y, c, rgb(50, 50, 60));
        }
        p += wl;
        if (*p == ' ') {
            x += font_width(&st->mono, " ");
            p++;
        }
    }
}

static void show(struct files *st, struct line *l, int i) {
    st->selected = i;
    if (i < 0) return;
    if (st->list[i].kind == FS_DIR) {
        st->size = 0;
        put_s(l, "files: showing ");
        put_s(l, st->list[i].name);
        put_s(l, "/ (folder)\n");
        flush(l);
        return;
    }
    st->size = fs_read(&st->fs, path_of(st, i));
    long n = st->size < 0 ? 0 : st->size > PREVIEW_MAX ? PREVIEW_MAX : st->size;
    const char *d = fs_data(&st->fs);
    for (long k = 0; k < n; k++) st->preview[k] = d[k] >= 32 || d[k] == '\n' ? d[k] : '.';
    st->preview[n] = 0;
    put_s(l, "files: showing ");
    put_s(l, st->list[i].name);
    put_s(l, " (");
    put_dec(l, (u64)(st->size < 0 ? 0 : st->size));
    put_s(l, " bytes)\n");
    flush(l);
}

static void refresh(struct files *st, struct line *l) {
    long n = fs_list_dir(&st->fs, st->dir, 0, 0);
    if (n > 128) n = 128;
    const struct fs_entry *e = fs_entries(&st->fs);
    st->count = n < 0 ? n : 0;
    for (long i = 0; i < n; i++)
        if (!fs_is_icon(&e[i])) st->list[st->count++] = e[i];   /* how programs look (fs.h) */
    if (st->selected >= st->count) st->selected = st->count > 0 ? st->count - 1 : -1;
    put_s(l, "files: listed ");
    put_dec(l, (u64)(st->count < 0 ? 0 : st->count));
    put_s(l, st->count == 1 ? " file\n" : " files\n");
    flush(l);
    /* the card's totals, for the status line; the log hears when what is free changes */
    st->space_ok = fs_space(&st->fs, &st->space) == FS_OK;
    unsigned kib = st->space_ok ? (unsigned)((u64)st->space.free * st->space.cluster / 1024) : 0;
    if (st->space_ok && kib != st->free_said) {
        st->free_said = kib;
        put_s(l, "files: ");
        put_dec(l, kib);
        put_s(l, " KiB free\n");
        flush(l);
    }
}

/* List the folder again and show the entry called `name` in it (if it is there). */
static void refresh_to(struct files *st, struct line *l, const char *name) {
    refresh(st, l);
    int at = st->selected;
    for (int i = 0; i < st->count; i++) if (same(st->list[i].name, name)) at = i;
    show(st, l, at);
}

static void open_folder(struct files *st, struct line *l, int i) {
    const char *p = path_of(st, i);
    int n = 0;
    for (; p[n]; n++) st->dir[n] = p[n];
    st->dir[n] = 0;
    st->selected = 0;
    st->top = 0;
    refresh(st, l);
    put_s(l, "files: opened ");
    put_s(l, st->dir);
    put_s(l, "\n");
    flush(l);
    show(st, l, st->count > 0 ? 0 : -1);
}

/* ---- changes ---- */

/* NAME with WORD, and from the second on a number, before its extension (at `ext`): the
   first of those not taken in the folder shown, into out (the name) and st->to (its path).
   "untitled folder 2", "notes copy.txt". 0 if the first 99 are taken or too long. */
COLD static int free_name(struct files *st, const char *name, int ext, const char *word, char *out) {
    for (int k = 1; k < 100; k++) {
        int n = 0;
        for (int i = 0; i < ext && n < EDIT_MAX; i++) out[n++] = name[i];
        for (const char *w = word; *w && n < EDIT_MAX; w++) out[n++] = *w;
        if (k > 1 && n < EDIT_MAX - 3) {
            out[n++] = ' ';
            if (k >= 10) out[n++] = (char)('0' + k / 10);
            out[n++] = (char)('0' + k % 10);
        }
        for (const char *e = name + ext; *e && n < EDIT_MAX; e++) out[n++] = *e;
        out[n] = 0;
        if (n > FS_NAME_MAX || !join(st->to, st->dir, out)) return 0;
        if (!fs_stat(&st->fs, st->to, 0)) return 1;
    }
    return 0;
}

/* Where a file's extension starts (its last '.', not a leading one), or its end. */
static int ext_of(const char *name, int kind) {
    int n = (int)slen(name), at = n;
    if (kind == FS_DIR) return n;
    for (int i = 1; i < n; i++) if (name[i] == '.') at = i;
    return at;
}

COLD static void start_edit(struct files *st, struct line *l) {
    if (st->selected < 0) { tell(st, 1, "Select a file or folder first.", 0, 0); return; }
    const struct fs_entry *e = &st->list[st->selected];
    int n = 0;
    for (; e->name[n] && n < FS_NAME_MAX; n++) st->edit[n] = e->name[n];
    st->edit[n] = 0;
    st->elen = n;
    st->sel = ext_of(st->edit, (int)e->kind);
    st->cur = st->sel;
    st->editing = 1;
    say(l, "files: renaming ", path_of(st, st->selected), 0, 0);
}

COLD static void new_folder(struct files *st, struct line *l) {
    char name[EDIT_MAX + 1];
    const char *base = "untitled folder";
    if (!free_name(st, base, (int)slen(base), "", name)) {
        tell(st, 1, "No new folder: too many untitled ones here.", 0, 0);
        return;
    }
    u64 r = fs_mkdir(&st->fs, st->to);
    say(l, "files: made folder ", st->to, " -> ", r == FS_OK ? "ok" : why(r));
    if (r != FS_OK) { tell(st, 1, "No new folder: ", why(r), "."); return; }
    refresh_to(st, l, name);
    if (st->selected >= 0 && same(st->list[st->selected].name, name)) start_edit(st, l);
}

/* What is wrong with a name, or 0. */
COLD static const char *bad_name(const char *name, int n, int file) {
    if (!n) return "a name is needed";
    if (n > FS_NAME_MAX) return "a name has 55 characters at most";
    for (int i = 0; i < n; i++) if (name[i] == '/') return "a name cannot hold /";
    if (same(name, ".") || same(name, "..")) return ". and .. are not names";
    if (file && n > 5 && same(name + n - 5, ".icon")) return "NAME.icon is a program's icon";
    return 0;
}

COLD static void commit(struct files *st, struct line *l) {
    st->edit[st->elen] = 0;
    const struct fs_entry *e = &st->list[st->selected];
    scopy(st->from, path_of(st, st->selected));
    const char *bad = bad_name(st->edit, st->elen, e->kind == FS_FILE);
    if (!bad && !join(st->to, st->dir, st->edit)) bad = "the path would be too long";
    if (!bad && same(st->from, st->to)) {
        st->editing = 0;
        say(l, "files: kept the name ", st->from, 0, 0);
        return;
    }
    if (!bad && fs_stat(&st->fs, st->to, 0)) bad = "that name is taken here";
    u64 r = bad ? FS_BAD : fs_rename(&st->fs, st->from, st->to);
    if (!bad && r != FS_OK) bad = why(r);
    put_s(l, "files: renamed ");
    put_s(l, st->from);
    put_s(l, " to ");
    if (st->dir[0]) { put_s(l, st->dir); put_s(l, "/"); }
    say(l, st->edit, bad ? " -> refused, " : " -> ok", bad, 0);
    if (bad) { tell(st, 1, "Not renamed: ", bad, "."); return; }
    st->editing = 0;
    if (st->mark && same(st->from, st->marked)) scopy(st->marked, st->to);   /* the mark goes along */
    tell(st, 0, "Renamed to ", st->edit, ".");
    refresh_to(st, l, st->edit);
}

static void cut(struct files *st, int a, int b) {
    for (int i = b; i <= st->elen; i++) st->edit[a + i - b] = st->edit[i];
    st->elen -= b - a;
    st->cur = a;
    st->sel = 0;
}

static void insert(struct files *st, char c) {
    if (st->sel) cut(st, 0, st->sel);
    if (st->elen >= EDIT_MAX) return;
    for (int i = st->elen; i > st->cur; i--) st->edit[i] = st->edit[i - 1];
    st->edit[st->cur++] = c;
    st->edit[++st->elen] = 0;
}

static void cancel_edit(struct files *st, struct line *l) {
    st->editing = 0;
    say(l, "files: rename of ", path_of(st, st->selected), " cancelled", 0);
}

/* A key while a name is edited. */
COLD static void edit_key(struct files *st, struct line *l, u64 k) {
    if (k == '\r' || k == '\n') commit(st, l);
    else if (k == 27) cancel_edit(st, l);
    else if (k == 127 || k == 8) {
        if (st->sel) cut(st, 0, st->sel);
        else if (st->cur > 0) cut(st, st->cur - 1, st->cur);
    } else if (k == KEY_DELETE) {                    /* forward: the letter after the cursor */
        if (st->sel) cut(st, 0, st->sel);
        else if (st->cur < st->elen) cut(st, st->cur, st->cur + 1);
    } else if (k == KEY_HOME || k == KEY_END) {
        st->cur = k == KEY_HOME ? 0 : st->elen;
        st->sel = 0;
    } else if (k == KEY_LEFT) {
        st->cur = st->sel ? 0 : st->cur - (st->cur > 0);
        st->sel = 0;
    } else if (k == KEY_RIGHT) {
        st->cur = st->sel ? st->sel : st->cur + (st->cur < st->elen);
        st->sel = 0;
    } else if (k >= 32 && k < 127) insert(st, (char)k);
}

COLD static void mark_key(struct files *st, struct line *l, int how) {
    if (st->selected < 0) { tell(st, 1, "Select a file first.", 0, 0); return; }
    const char *p = path_of(st, st->selected);
    if (how == 'c' && st->list[st->selected].kind == FS_DIR) {
        say(l, "files: copy ", p, " -> refused, copies files, not folders", 0);
        tell(st, 1, "Files copies files, not folders.", 0, 0);
        return;
    }
    if (st->mark == how && same(p, st->marked)) {
        st->mark = 0;
        say(l, "files: forgot ", p, 0, 0);
        return;
    }
    st->mark = how;
    scopy(st->marked, p);
    say(l, "files: marked ", p, how == 'x' ? " to move" : " to copy", 0);
}

/* A copy of the file `from` at `to`, made as Terminal's cp makes one: in pieces into TO.part~,
   then put in place by one rename, so no half copy is ever at `to`. TO.part~ is the copy's
   alone, as it is cp's: a file there is one a power cut left, written over (and removed after
   a failure); a folder there is refused and left alone, as is a name too long to take the
   ".part~". A TO.tmp of yours is never touched. *bytes: how many. 0, or why not. */
COLD static const char *copy_file(struct files *st, const char *from, const char *to, u64 *bytes) {
    scopy(st->tmp, to);
    int n = (int)slen(st->tmp), name = (int)(last_name(st->tmp) - st->tmp);
    if (n + 6 > FS_PATH_MAX || n - name + 6 > FS_NAME_MAX) return "the name is too long";
    scopy(st->tmp + n, ".part~");
    if (fs_stat(&st->fs, st->tmp, 0) == FS_DIR) return "NAME.part~ is a folder: rename it first";
    u64 size = 0, off = 0, r = fs_write(&st->fs, st->tmp, "", 0);
    int made = r == FS_OK;
    if (!fs_stat(&st->fs, from, &size)) r = FS_NOT_FOUND;
    while (r == FS_OK && off < size) {
        long got = fs_read_at(&st->fs, from, off, &size);
        if (got <= 0) { r = got < 0 ? FS_NOT_FOUND : FS_OK; break; }
        /* the piece is in the buffer's data area already: written from where it is */
        r = fs_write_at(&st->fs, st->tmp, off, fs_data(&st->fs), (u64)got);
        off += (u64)got;
    }
    if (r == FS_OK) r = fs_rename(&st->fs, st->tmp, to);
    if (r != FS_OK && made) fs_delete(&st->fs, st->tmp);
    *bytes = off;
    return r == FS_OK ? 0 : why(r);
}

/* V: what is marked, into the folder shown. */
COLD static void put_here(struct files *st, struct line *l) {
    if (!st->mark) { tell(st, 1, "Nothing is marked: C marks a file to copy, X one to move.", 0, 0); return; }
    const char *name = last_name(st->marked), *bad = 0;
    char made[EDIT_MAX + 1];
    if (!fs_stat(&st->fs, st->marked, 0)) {
        say(l, "files: ", st->marked, " is gone", 0);
        tell(st, 1, name, " is not there any more.", 0);
        st->mark = 0;
        return;
    }
    int moving = st->mark == 'x';
    if (!join(st->to, st->dir, name)) bad = "the path would be too long";
    else if (moving && same(st->to, st->marked)) bad = "it is here already";
    else if (fs_stat(&st->fs, st->to, 0)) {
        if (moving) bad = "that name is taken here";
        else if (!free_name(st, name, ext_of(name, FS_FILE), " copy", made)) bad = "no free name for the copy";
    }
    u64 bytes = 0, r = bad || !moving ? FS_OK : fs_rename(&st->fs, st->marked, st->to);
    if (!bad) bad = moving ? (r == FS_OK ? 0 : why(r)) : copy_file(st, st->marked, st->to, &bytes);
    put_s(l, moving ? "files: moved " : "files: copied ");
    put_s(l, st->marked);
    put_s(l, " to ");
    put_s(l, st->to);
    if (!bad && !moving) {
        put_s(l, " -> ok, ");
        put_dec(l, bytes);
        say(l, " bytes", 0, 0, 0);
    } else say(l, bad ? " -> refused, " : " -> ok", bad, 0, 0);
    if (bad) { tell(st, 1, moving ? "Not moved: " : "Not copied: ", bad, "."); return; }
    tell(st, 0, moving ? "Moved " : "Copied ", name, " here.");
    if (moving) st->mark = 0;
    refresh_to(st, l, last_name(st->to));
}

/* The folder `top` and everything in it, deepest first. *count: how many things were in it. */
COLD static u64 delete_all(struct files *st, const char *top, u64 *count) {
    char *p = st->tmp;
    scopy(p, top);
    int base = (int)slen(top);
    for (;;) {
        long n = fs_list_dir(&st->fs, p, 0, 0);
        if (n < 0) return FS_NOT_FOUND;
        int len = (int)slen(p);
        if (n > 0) {                            /* its first entry: a folder to go into, or a file */
            const struct fs_entry *e = fs_entries(&st->fs);
            int folder = e[0].kind == FS_DIR, k = 0;
            while (k < FS_NAME_MAX && e[0].name[k]) k++;
            if (len + 1 + k > FS_PATH_MAX) return FS_BAD;
            p[len] = '/';
            for (int i = 0; i < k; i++) p[len + 1 + i] = e[0].name[i];
            p[len + 1 + k] = 0;
            if (folder) continue;
        }
        u64 r = fs_delete(&st->fs, p);
        if (r != FS_OK) return r;
        int k = (int)slen(p);
        if (k == base) return FS_OK;
        ++*count;
        while (k > base && p[k] != '/') k--;
        p[k] = 0;                               /* back to the folder it was in */
    }
}

COLD static void delete_key(struct files *st, struct line *l) {
    int confirmed = st->confirm;
    st->confirm = 0;
    if (st->selected < 0) return;
    const char *p = path_of(st, st->selected);
    u64 inside = 0, r;
    if (st->list[st->selected].kind == FS_DIR && fs_list_dir(&st->fs, p, 0, &inside) >= 0 && inside) {
        if (!confirmed) {
            /* the file server deletes only empty folders (FS_NOT_EMPTY): ask, then empty it */
            st->confirm = 1;
            put_s(l, "files: ");
            put_s(l, p);
            put_s(l, " is not empty (");
            put_dec(l, inside);
            say(l, " in it): asked before deleting it", 0, 0, 0);
            return;
        }
        u64 n = 0;
        r = delete_all(st, p, &n);
        put_s(l, "files: deleted ");
        put_s(l, p);
        put_s(l, " and the ");
        put_dec(l, n);
        put_s(l, " things in it");
    } else {
        r = fs_delete(&st->fs, p);
        put_s(l, "files: deleted ");
        put_s(l, p);
    }
    say(l, r == FS_OK ? " -> ok" : " -> refused, ", r == FS_OK ? 0 : why(r), 0, 0);
    int n = (int)slen(p), k = 0;                 /* a mark on what went, or inside it, goes too */
    while (k < n && p[k] == st->marked[k]) k++;
    if (k == n && (!st->marked[n] || st->marked[n] == '/')) st->mark = 0;
    if (r != FS_OK) tell(st, 1, "Not deleted: ", why(r), ".");
    refresh(st, l);
    show(st, l, st->selected);
}

/* A key with no name being edited. */
COLD static void key(struct files *st, struct line *l, u64 k) {
    if (k == 127 || k == 8 || k == KEY_DELETE) { delete_key(st, l); return; }
    int was = st->confirm;
    st->confirm = 0;
    if (k >= 'A' && k <= 'Z') k += 'a' - 'A';
    if (k == 'n') new_folder(st, l);
    else if (k == 'r') start_edit(st, l);
    else if (k == 'c' || k == 'x') mark_key(st, l, (int)k);
    else if (k == 'v') put_here(st, l);
    else if (k == 27) {
        if (!was && st->mark) { say(l, "files: forgot ", st->marked, 0, 0); st->mark = 0; }
    } else if ((k == '\r' || k == KEY_RIGHT) && st->selected >= 0 && st->list[st->selected].kind == FS_DIR) {
        open_folder(st, l, st->selected);
    } else if (k == KEY_LEFT && st->dir[0]) {
        int n = 0;
        while (st->dir[n]) n++;
        while (n > 0 && st->dir[n - 1] != '/') n--;
        st->dir[n > 0 ? n - 1 : 0] = 0;
        st->selected = 0;
        st->top = 0;
        refresh(st, l);
        show(st, l, st->count > 0 ? 0 : -1);
    } else if ((k == KEY_UP || k == KEY_DOWN) && st->count > 0) {
        int to = st->selected + (k == KEY_DOWN ? 1 : -1);
        if (to >= 0 && to < st->count) show(st, l, to);
    }
}

static void click(struct files *st, struct line *l, int x, int y) {
    int row = (y - ROW_Y) / ROW_H;
    st->confirm = 0;
    if (x >= BTN_X && x < BTN_X + BTN_W && y >= BTN_Y && y < BTN_Y + BTN_H) { new_folder(st, l); return; }
    refresh(st, l);
    if (x < LIST_W && y >= ROW_Y && row < MAX_SHOWN && st->top + row < st->count) {
        int i = st->top + row;
        if (st->list[i].kind == FS_DIR && i == st->selected) open_folder(st, l, i);
        else show(st, l, i);
    } else show(st, l, st->selected);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct files *st = (struct files *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->bold = font_of(assets, F_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->mono = font_of(assets, F_MONO);
    st->win = app_surface(FW, FH);
    fs_init(&st->fs, SPARE_PAGE);
    st->selected = -1;
    st->top = 0;
    st->dir[0] = 0;
    refresh(st, &l);
    show(st, &l, st->count > 0 ? 0 : -1);
    draw(st);
    u64 opened = app_open(FW, FH, "Files");
    put_s(&l, "files: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "files: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind == EV_DOWN || e.kind == EV_KEY) st->msg[0] = 0;
        if (st->editing && e.kind == EV_KEY) {
            edit_key(st, &l, e.a);
        } else if (st->editing && e.kind == EV_PASTE) {
            char t[16];
            int n = paste_text(e, t);
            for (int i = 0; i < n; i++) if (t[i] >= 32 && t[i] < 127) insert(st, t[i]);
            st->edit[st->elen] = 0;
            if (n < 16) say(&l, "files: pasted into the name: ", st->edit, 0, 0);
        } else if (st->editing && e.kind == EV_COPY) {
            app_copy(st->edit, (u64)st->elen);
            continue;
        } else if (e.kind == EV_DOWN) {
            int x = (int)e.a, y = (int)e.b, row = (y - ROW_Y) / ROW_H;
            if (st->editing) {
                /* a click in the field leaves it be; anywhere else cancels the rename */
                if (x < LIST_W && y >= ROW_Y && row < MAX_SHOWN && st->top + row == st->selected) continue;
                cancel_edit(st, &l);
            }
            click(st, &l, x, y);
        } else if (e.kind == EV_KEY) {
            key(st, &l, e.a);
        } else continue;
        draw(st);
        dirty = 1;
    }
}
