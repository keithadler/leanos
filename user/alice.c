/* alice's Notes. She draws a window in her own memory, hands the display server a
   read-only capability to exactly those pages, and then asks it, over and over, for her
   next event. She also keeps a secret in her data pages and checks that nobody changes it.

   Notes: a list of notes on the left, the open one on the right. Each note is a file in
   her folder, notes/1.txt, notes/2.txt and so on, of up to 32 KiB (a longer file is shown,
   its first 32 KiB, and never changed); a card from before there were several notes has
   one, notes.txt, which she moves to notes/1.txt, in one step, the first time she starts
   on it. The list shows each note's first line.

   The open note is edited at the cursor: the arrows move it (Up and Down by the lines as
   they are shown, wrapped at the window's width), Backspace deletes before it, Return
   starts a line, and the note scrolls to keep the cursor in view. A click puts the cursor
   there. Tab goes to the list, where Up and Down choose a note and Return (or Tab) goes
   back to it; a click in the list chooses one too. Ctrl+N (or the + button) makes a new
   note; Ctrl+D (or Delete, under the list) asks to delete the open one, and Ctrl+D again
   (or Delete again) deletes it: any other key keeps it. A note left empty disappears when
   another is chosen.

   A note is saved a moment after the typing stops (and before another is chosen, and when
   the window closes): written whole to notes/N.txt.tmp, then put in place by one rename,
   so after a power cut notes/N.txt is the last save or the one before, never a mix. A
   notes/N.txt.tmp that is there already is not hers to overwrite: she uses .tmp2 to .tmp9
   instead, and saves nothing if those are all taken. A note that could not be saved stays
   open (another is not shown in its place) and is tried again a little later.

   Copy (Ctrl+C) takes the whole note (its first 4 KiB: what the clipboard holds); a
   paste (Ctrl+V) goes in at the cursor. */
#include "app.h"
#include "fs.h"

/* The cold paths (starting, saving, the list) are compiled for size, as display.c's are;
   typing and drawing are not. */
#define COLD __attribute__((cold, minsize))

#define WIN_W 480
#define WIN_H 320
#define WIN_PAGES ((WIN_W * WIN_H * 4 + 4095) / 4096)
/* Her spare run, mapped at SPARE_PAGE: her assets (fonts) in its first 16 pages, then the
   window's pixels, then the open note and where each of its lines starts, then, in the
   last 4 pages, the buffer she lends the file server. Only the window's pages are lent to
   the display, read-only. */
#define WIN_OFFSET 16
#define NOTE_MAX 32768
#define TEXT_OFFSET (WIN_OFFSET + WIN_PAGES)
#define LINES_OFFSET (TEXT_OFFSET + NOTE_MAX / 4096)
#define LINES_MAX (NOTE_MAX + 2)              /* a line per byte at most, one more, and the end */
#define LINES_PAGES ((LINES_MAX * 2 + 4095) / 4096)
_Static_assert(WIN_PAGES <= APP_WIN_PAGES, "the window must fit a window's slot at the display");
_Static_assert(LINES_OFFSET + LINES_PAGES <= FS_BUF_OFFSET, "the note must end before the file server's buffer");
#define TEXT ((char *)PAGE(SPARE_PAGE + TEXT_OFFSET))
#define LINES ((unsigned short *)PAGE(SPARE_PAGE + LINES_OFFSET))

enum { F_HEAD = 5, F_TEXT = 6, F_SMALL = 3, F_BOLD = 7 };
enum { CTRL_D = 4, TAB = 9, CTRL_N = 14 };
#define SECRET 0x5ec12e7

/* Where things are in the window. */
#define SIDE_W 150                            /* the list */
#define HEAD_H 48
#define ROW_H 28
#define FOOT_H 26
#define ROWS ((WIN_H - HEAD_H - FOOT_H) / ROW_H)
#define PLUS_X (SIDE_W - 38)
#define PLUS_Y 12
#define PLUS_S 26
#define DELETE_X (SIDE_W - 60)                /* the list's Delete, in its footer */
#define PAD 14                                /* the note */
#define TEXT_X (SIDE_W + PAD)
#define TEXT_W (WIN_W - SIDE_W - 2 * PAD - 6)
#define TEXT_Y 10
#define LINE_H 20
#define TEXT_ROWS ((WIN_H - FOOT_H - TEXT_Y - 4) / LINE_H)

#define MAX_NOTES 64
#define TITLE_MAX 40
#define SAVE_AFTER 400                        /* ms without a change */
#define SAVE_AGAIN 10000                      /* ms after a save that failed */

struct note {
    int num;                                  /* its file: notes/NUM.txt */
    int on_card;                              /* that file is there */
    char title[TITLE_MAX];                    /* its first line */
};

struct notes {
    u64 secret;
    struct font head, body, small, bold;
    struct fs_client fs;
    struct surface win;
    struct note list[MAX_NOTES];
    int count, cur, list_top;                 /* the notes, the open one, the first row shown */
    int len, at, top, nlines, goal;           /* the open note: its length, the cursor, the first
                                                 line shown, its lines; the x (1/64 px) Up and
                                                 Down keep, -1 for none */
    int focus;                                /* 0: the note, 1: the list */
    int confirm;                              /* asked once to delete */
    int unsaved, stale, locked, pasted;       /* unsaved: changed since it was saved; locked:
                                                 shown, never changed (too large, or unreadable) */
    u64 save_at;                              /* when to save it (ms) */
    int adv[95];                              /* each character's advance, 1/64 px */
    char status[48];
};
_Static_assert(sizeof(struct notes) <= 8 * 4096, "alice's state must fit in her data pages");

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static void set_status(struct notes *n, const char *s) {
    int i = 0;
    for (; s[i] && i < (int)sizeof n->status - 1; i++) n->status[i] = s[i];
    n->status[i] = 0;
}

static int adv(const struct notes *n, char c) {
    unsigned u = (unsigned char)c;
    return n->adv[u >= 32 && u < 127 ? u - 32 : '?' - 32];
}

/* ---- lines: where each line of the open note starts, as it is shown ----

   LINES[k] is where line k starts; LINES[nlines] is one past the end. A line ends at a
   line break (the next starts after it) or where the next word would not fit: after the
   last space, or, in a word longer than the line, before the character that does not fit.
   Spaces may hang past the edge. */
static void layout(struct notes *n) {
    const char *t = TEXT;
    unsigned short *L = LINES;
    int s = 0, k = 0, max = TEXT_W * 64;
    for (;;) {
        L[k++] = (unsigned short)s;
        int w = 0, brk = 0, i = s, next;
        for (;; i++) {
            if (i >= n->len) {
                n->nlines = k;
                L[k] = (unsigned short)(n->len + 1);
                n->stale = 0;
                return;
            }
            char c = t[i];
            if (c == '\n') { next = i + 1; break; }
            int a = adv(n, c);
            if (i > s && c != ' ' && w + a > max) { next = brk > s ? brk : i; break; }
            w += a;
            if (c == ' ') brk = i + 1;
        }
        s = next;
    }
}

static void fresh(struct notes *n) { if (n->stale) layout(n); }

/* The line the cursor at `at` is on. */
static int line_of(struct notes *n, int at) {
    int lo = 0, hi = n->nlines - 1;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if (LINES[mid] <= at) lo = mid; else hi = mid - 1;
    }
    return lo;
}

/* The last place the cursor can be on line k: before its line break or the character that
   starts the next line; the end on the last line. */
static int line_last(struct notes *n, int k) { return k + 1 < n->nlines ? LINES[k + 1] - 1 : n->len; }

static int x_of(struct notes *n, int k, int at) {
    int w = 0;
    for (int i = LINES[k]; i < at; i++) w += adv(n, TEXT[i]);
    return w;
}

/* The place on line k nearest x (1/64 px). */
static int at_x(struct notes *n, int k, int x) {
    int w = 0, i = LINES[k], last = line_last(n, k);
    for (; i < last; i++) {
        int a = adv(n, TEXT[i]);
        if (x < w + a / 2) break;
        w += a;
    }
    return i;
}

/* Keep the cursor's line in view, and the open note's row in the list. */
static void follow(struct notes *n) {
    fresh(n);
    int k = line_of(n, n->at);
    if (k < n->top) n->top = k;
    if (k >= n->top + TEXT_ROWS) n->top = k - TEXT_ROWS + 1;
    int most = n->nlines > TEXT_ROWS ? n->nlines - TEXT_ROWS : 0;
    if (n->top > most) n->top = most;
    if (n->cur < n->list_top) n->list_top = n->cur;
    if (n->cur >= n->list_top + ROWS) n->list_top = n->cur - ROWS + 1;
    most = n->count > ROWS ? n->count - ROWS : 0;
    if (n->list_top > most) n->list_top = most;
}

/* ---- drawing ---- */

/* `s`, cut to `width` pixels with "..." if it is wider. */
static void fit(const struct font *f, const char *s, char *out, int width) {
    int k = 0;
    while (s[k] && k < TITLE_MAX - 1) { out[k] = s[k]; k++; }
    out[k] = 0;
    if (font_width(f, out) <= width) return;
    while (k > 0) {
        k--;
        out[k] = '.'; out[k + 1] = '.'; out[k + 2] = '.'; out[k + 3] = 0;
        if (font_width(f, out) <= width) return;
    }
}

static void draw(struct notes *n) {
    struct surface *s = &n->win;
    follow(n);
    unsigned ink = rgb(36, 38, 46), gray = rgb(150, 150, 160), blue = rgb(58, 110, 230), white = rgb(255, 255, 255);
    unsigned rule = rgb(226, 226, 232);

    /* the list */
    fill(s, 0, 0, SIDE_W, WIN_H, rgb(244, 244, 247));
    fill(s, SIDE_W, 0, 1, WIN_H, rule);
    font_text(s, &n->head, PAD, 32, "Notes", rgb(28, 28, 32));
    round_rect(s, PLUS_X, PLUS_Y, PLUS_S, PLUS_S, 7, blue, 255);
    fill(s, PLUS_X + 7, PLUS_Y + 12, 12, 2, white);
    fill(s, PLUS_X + 12, PLUS_Y + 7, 2, 12, white);
    for (int r = 0; r < ROWS && n->list_top + r < n->count; r++) {
        int i = n->list_top + r, y = HEAD_H + r * ROW_H;
        const struct note *e = &n->list[i];
        int sel = i == n->cur;
        if (sel) round_rect(s, 6, y + 1, SIDE_W - 12, ROW_H - 2, 6, n->focus ? blue : rgb(221, 228, 246), 255);
        char t[TITLE_MAX + 4];
        const struct font *f = sel ? &n->bold : &n->body;
        fit(f, e->title[0] ? e->title : "New note", t, SIDE_W - 2 * PAD);
        font_text(s, f, PAD, y + 19, t, sel && n->focus ? white : e->title[0] ? ink : gray);
    }
    if (n->list_top > 0) fill(s, 6, HEAD_H - 1, SIDE_W - 12, 1, rule);          /* more above */
    if (n->list_top + ROWS < n->count) fill(s, 6, HEAD_H + ROWS * ROW_H, SIDE_W - 12, 1, rule);
    fill(s, 0, WIN_H - FOOT_H, SIDE_W, 1, rule);
    struct line c = {.n = 0};
    put_dec(&c, (u64)n->count);
    put_s(&c, n->count == 1 ? " note" : " notes");
    c.b[c.n] = 0;
    font_text(s, &n->small, PAD, WIN_H - 9, c.b, gray);
    font_text(s, &n->small, DELETE_X + 14, WIN_H - 9, "Delete", n->confirm ? rgb(210, 50, 40) : gray);

    /* the note */
    fill(s, SIDE_W + 1, 0, WIN_W - SIDE_W - 1, WIN_H - FOOT_H, white);
    clip_to(s, SIDE_W + 1, 0, WIN_W - SIDE_W - 1, WIN_H - FOOT_H);
    const char *t = TEXT;
    int asc = (int)n->body.ascent;
    if (!n->len) font_text(s, &n->body, TEXT_X, TEXT_Y + asc, "Type your note here.", rgb(186, 186, 194));
    for (int r = 0; r < TEXT_ROWS && n->top + r < n->nlines; r++) {
        int k = n->top + r, y = TEXT_Y + r * LINE_H + asc;
        int from = LINES[k], to = k + 1 < n->nlines ? LINES[k + 1] : n->len;
        if (to > from && t[to - 1] == '\n') to--;
        char buf[160];
        int m = 0;
        for (int i = from; i < to && m < (int)sizeof buf - 1; i++) buf[m++] = t[i] >= 32 && t[i] < 127 ? t[i] : '?';
        buf[m] = 0;
        font_text(s, &n->body, TEXT_X, y, buf, ink);
    }
    if (!n->focus) {
        int k = line_of(n, n->at);
        if (k >= n->top && k < n->top + TEXT_ROWS)
            fill(s, TEXT_X + x_of(n, k, n->at) / 64, TEXT_Y + (k - n->top) * LINE_H + 1, 2, LINE_H - 2, blue);
    }
    clip_all(s);
    if (n->nlines > TEXT_ROWS) {           /* where the part shown is, in the whole note */
        int track = TEXT_ROWS * LINE_H, h = track * TEXT_ROWS / n->nlines;
        if (h < 16) h = 16;
        int y = TEXT_Y + (track - h) * n->top / (n->nlines - TEXT_ROWS);
        round_rect(s, WIN_W - 9, y, 5, h, 2, rgb(196, 198, 206), 255);
    }

    /* the note's footer: who can write this page, or the question, and where the cursor is */
    fill(s, SIDE_W + 1, WIN_H - FOOT_H, WIN_W - SIDE_W - 1, FOOT_H, rgb(250, 250, 251));
    fill(s, SIDE_W + 1, WIN_H - FOOT_H, WIN_W - SIDE_W - 1, 1, rule);
    if (n->confirm) {
        font_text(s, &n->small, TEXT_X, WIN_H - 9, "Delete this note? Ctrl+D again deletes it.", rgb(210, 50, 40));
        return;
    }
    c.n = 0;
    if (n->status[0]) put_s(&c, n->status);
    else {
        put_s(&c, "line ");
        put_dec(&c, (u64)line_of(n, n->at) + 1);
        put_s(&c, " of ");
        put_dec(&c, (u64)n->nlines);
    }
    c.b[c.n] = 0;
    const char *who = "Only alice can write this page.";
    int w = font_width(&n->small, c.b);
    if (TEXT_X + font_width(&n->small, who) + 12 <= WIN_W - PAD - w)   /* (a long status has it all) */
        font_text(s, &n->small, TEXT_X, WIN_H - 9, who, rgb(160, 160, 170));
    font_text(s, &n->small, WIN_W - PAD - w, WIN_H - 9, c.b, gray);
}

/* ---- the files ---- */

/* notes/NUM.txt, then `tail`. */
COLD static void path_of(char *p, int num, const char *tail) {
    const char *d = "notes/";
    int k = 0;
    for (; d[k]; k++) p[k] = d[k];
    char digits[12];
    int m = 0;
    do { digits[m++] = (char)('0' + num % 10); num /= 10; } while (num);
    while (m) p[k++] = digits[--m];
    for (const char *x = ".txt"; *x;) p[k++] = *x++;
    while (*tail) p[k++] = *tail++;
    p[k] = 0;
}

/* NUM from "NUM.txt", 0 if the name is not that. */
COLD static int num_of(const char *name) {
    int v = 0, k = 0;
    for (; name[k] >= '0' && name[k] <= '9' && k < 6; k++) v = v * 10 + (name[k] - '0');
    if (!k || name[0] == '0') return 0;
    const char *x = ".txt";
    for (int i = 0; i < 5; i++) if (name[k + i] != x[i]) return 0;   /* (and the 0 after it) */
    return v;
}

COLD static void title_from(struct note *e, const char *t, int len) {
    int i = 0, k = 0;
    while (i < len && (t[i] == '\n' || t[i] == ' ')) i++;
    while (i < len && t[i] != '\n' && k < TITLE_MAX - 1) {
        char c = t[i++];
        e->title[k++] = c >= 32 && c < 127 ? c : '?';
    }
    e->title[k] = 0;
}

COLD static void put_note(struct line *l, const char *what, int num) {
    put_s(l, "alice: ");
    put_s(l, what);
    put_s(l, " note ");
    put_dec(l, (u64)num);
}

COLD static void blank(struct note *e, int num) {
    e->num = num;
    e->on_card = 0;
    e->title[0] = 0;
}

/* Save the open note: whole into NAME.tmp (the first of .tmp, .tmp2 ... .tmp9 that is not
   there), then one rename puts it in place. If that fails, it stays unsaved, and she tries
   again a while later (or when it is closed). */
COLD static void save(struct notes *n, struct line *l) {
    struct note *e = &n->list[n->cur];
    n->unsaved = 0;
    if (n->locked) return;
    char path[32], tmp[40], tail[8] = ".tmp";
    path_of(path, e->num, "");
    int k = 1;
    for (; k <= 9; k++) {
        tail[4] = k > 1 ? (char)('0' + k) : 0;
        tail[5] = 0;
        path_of(tmp, e->num, tail);
        if (!fs_stat(&n->fs, tmp, 0)) break;
        put_s(l, "alice: ");
        put_s(l, tmp);
        put_s(l, " is there already: left alone");
        say(l);
    }
    u64 st = k > 9 ? FS_EXISTS : FS_OK;
    int made = 0;
    for (int off = 0; st == FS_OK && (off < n->len || !made); off += FS_CHUNK) {
        u64 take = (u64)(n->len - off < FS_CHUNK ? n->len - off : FS_CHUNK);
        st = made ? fs_write_at(&n->fs, tmp, (u64)off, TEXT + off, take) : fs_write(&n->fs, tmp, TEXT, take);
        if (st == FS_NOT_FOUND && !made) {          /* no folder yet: make it, and again */
            fs_mkdir(&n->fs, "notes");
            st = fs_write(&n->fs, tmp, TEXT, take);
        }
        made |= st == FS_OK;
    }
    if (st == FS_OK) st = fs_rename(&n->fs, tmp, path);
    if (st != FS_OK && made) fs_delete(&n->fs, tmp);
    if (st == FS_OK) {
        e->on_card = 1;
        set_status(n, "saved");
        put_note(l, "saved", e->num);
        put_s(l, " (");
        put_dec(l, (u64)n->len);
        put_s(l, " bytes)");
    } else {
        n->unsaved = 1;
        n->save_at = millis() + SAVE_AGAIN;
        set_status(n, k > 9 ? "not saved: its .tmp names are taken" : "could not save it");
        put_note(l, "could not save", e->num);
        if (k > 9) {
            put_s(l, ": ");
            put_s(l, path);
            put_s(l, ".tmp to .tmp9 are there already");
        }
    }
    say(l);
}

/* Read note i into the text, the cursor at its end. One too large (or that cannot be read)
   is shown and locked: saving it would cut it short. */
COLD static void load(struct notes *n, int i) {
    struct note *e = &n->list[i];
    n->cur = i;
    n->len = n->at = n->top = 0;
    n->goal = -1;
    n->locked = n->unsaved = n->confirm = 0;
    n->status[0] = 0;
    if (e->on_card) {
        char path[32];
        path_of(path, e->num, "");
        u64 size = 0;
        long got = 0;
        while (n->len < NOTE_MAX) {
            got = fs_read_at(&n->fs, path, (u64)n->len, &size);
            if (got <= 0) break;
            const char *d = fs_data(&n->fs);
            for (long k = 0; k < got && n->len < NOTE_MAX; k++) TEXT[n->len++] = d[k];
            if ((u64)n->len >= size) break;
        }
        if (got < 0 || size > NOTE_MAX) {
            n->locked = 1;
            set_status(n, got < 0 ? "could not read it: read-only" : "over 32 KiB: read-only");
        }
        title_from(e, TEXT, n->len);
    }
    n->at = n->len;
    n->stale = 1;
}

/* Take note `i` out of the list. */
COLD static void drop(struct notes *n, int i) {
    for (int k = i; k + 1 < n->count; k++) n->list[k] = n->list[k + 1];
    n->count--;
}

/* Save the open note before another is shown: whether it may be (it is saved, or it cannot
   be changed). One that could not be saved stays open, so what was typed is not lost. */
COLD static int saved(struct notes *n, struct line *l) {
    if (n->unsaved) save(n, l);
    return !n->unsaved;
}

/* Choose note i: the open one is saved first, or dropped if it is empty. */
COLD static void choose(struct notes *n, struct line *l, int i) {
    if (i == n->cur || i < 0 || i >= n->count) return;
    struct note *e = &n->list[n->cur];
    char path[32];
    path_of(path, e->num, "");
    if (!n->len && !n->locked && (!e->on_card || fs_delete(&n->fs, path) == FS_OK)) {
        put_note(l, "removed", e->num);
        put_s(l, ", which was empty");
        say(l);
        drop(n, n->cur);
        if (i > n->cur) i--;
    } else if (!saved(n, l)) return;
    load(n, i);
    put_note(l, "showing", n->list[i].num);
    put_s(l, " (");
    put_dec(l, (u64)n->len);
    put_s(l, n->locked ? " bytes, read-only)" : " bytes)");
    say(l);
}

COLD static void new_note(struct notes *n, struct line *l) {
    n->focus = 0;
    if (!n->len && !n->list[n->cur].on_card) return;       /* this one is new already */
    if (n->count >= MAX_NOTES) { set_status(n, "64 notes: delete one first"); return; }
    if (!saved(n, l)) return;
    int num = 0;
    for (int k = 0; k < n->count; k++) if (n->list[k].num > num) num = n->list[k].num;
    blank(&n->list[n->count++], num + 1);
    load(n, n->count - 1);
    put_note(l, "new", num + 1);
    say(l);
}

COLD static void ask_delete(struct notes *n, struct line *l) {
    n->confirm = 1;
    put_note(l, "asked before deleting", n->list[n->cur].num);
    say(l);
}

COLD static void keep(struct notes *n, struct line *l) {
    n->confirm = 0;
    put_note(l, "kept", n->list[n->cur].num);
    say(l);
}

COLD static void delete_note(struct notes *n, struct line *l) {
    struct note *e = &n->list[n->cur];
    n->confirm = 0;
    char path[32];
    path_of(path, e->num, "");
    if (e->on_card && fs_delete(&n->fs, path) != FS_OK) {
        set_status(n, "could not delete");
        put_note(l, "could not delete", e->num);
        say(l);
        return;
    }
    put_note(l, "deleted", e->num);
    say(l);
    drop(n, n->cur);
    if (!n->count) blank(&n->list[n->count++], 1);
    load(n, n->cur < n->count ? n->cur : n->count - 1);
}

/* The notes in notes/, in order of their numbers; the legacy notes.txt becomes notes/1.txt
   if there are none. */
COLD static void find_notes(struct notes *n, struct line *l) {
    n->count = 0;
    u64 total = 0;
    for (u64 from = 0; n->count < MAX_NOTES;) {
        long got = fs_list_dir(&n->fs, "notes", from, &total);
        if (got <= 0) break;
        const struct fs_entry *d = fs_entries(&n->fs);
        for (long k = 0; k < got && n->count < MAX_NOTES; k++) {
            int num = d[k].kind == FS_FILE ? num_of(d[k].name) : 0;
            if (!num) continue;
            int at = n->count++;
            while (at > 0 && n->list[at - 1].num > num) { n->list[at] = n->list[at - 1]; at--; }
            blank(&n->list[at], num);
            n->list[at].on_card = 1;
        }
        from += (u64)got;
        if (from >= total) break;
    }
    if (!n->count && fs_stat(&n->fs, "notes.txt", 0) == FS_FILE) {
        fs_mkdir(&n->fs, "notes");
        u64 st = fs_rename(&n->fs, "notes.txt", "notes/1.txt");
        put_s(l, st == FS_OK ? "alice: moved notes.txt to notes/1.txt" : "alice: could not move notes.txt to notes/1.txt");
        say(l);
        if (st == FS_OK) {
            blank(&n->list[n->count++], 1);
            n->list[0].on_card = 1;
        }
    }
    for (int i = 0; i < n->count; i++) {                /* each one's first line */
        char path[32];
        path_of(path, n->list[i].num, "");
        long got = fs_read(&n->fs, path);
        if (got >= 0) title_from(&n->list[i], fs_data(&n->fs), (int)got);
    }
    if (!n->count) {
        blank(&n->list[n->count++], 1);
        load(n, 0);
        put_s(l, "alice: no saved note yet");
    } else {
        load(n, 0);
        put_s(l, "alice: ");
        put_dec(l, (u64)n->count);
        put_s(l, n->count == 1 ? " note; loaded " : " notes; loaded ");
        char path[32];
        path_of(path, n->list[0].num, "");
        put_s(l, path);
        put_s(l, ", ");
        put_dec(l, (u64)n->len);
        put_s(l, n->locked ? " bytes, read-only" : " bytes");
    }
    say(l);
}

/* ---- editing ---- */

static void changed(struct notes *n) {
    n->unsaved = 1;
    n->save_at = millis() + SAVE_AFTER;
    n->stale = 1;
    n->goal = -1;
    n->status[0] = 0;
    title_from(&n->list[n->cur], TEXT, n->len);
}

/* `k` bytes at the cursor. */
static void insert(struct notes *n, const char *s, int k) {
    if (n->locked) return;
    if (k > NOTE_MAX - n->len) k = NOTE_MAX - n->len;
    if (k > 0) {
        char *t = TEXT;
        for (int i = n->len - 1; i >= n->at; i--) t[i + k] = t[i];
        for (int i = 0; i < k; i++) t[n->at + i] = s[i];
        n->at += k;
        n->len += k;
        changed(n);
    }
    if (n->len == NOTE_MAX) set_status(n, "full: 32 KiB");
}

static void key(struct notes *n, struct line *l, u64 c) {
    if (!n->locked) n->status[0] = 0;               /* "saved" and the like, until a key */
    if (n->focus) {                                 /* the list */
        if (c == KEY_UP) { choose(n, l, n->cur - 1); return; }
        if (c == KEY_DOWN) { choose(n, l, n->cur + 1); return; }
        if (c == TAB || c == '\r' || c == '\n' || c == KEY_RIGHT) { n->focus = 0; return; }
        if (c < 32 || c > 126) return;
        n->focus = 0;                               /* typing goes to the note */
    }
    fresh(n);
    int k = line_of(n, n->at);
    if (c == TAB) n->focus = 1;
    else if (c == KEY_LEFT) { if (n->at > 0) n->at--; n->goal = -1; }
    else if (c == KEY_RIGHT) { if (n->at < n->len) n->at++; n->goal = -1; }
    else if (c == KEY_UP || c == KEY_DOWN) {
        if (n->goal < 0) n->goal = x_of(n, k, n->at);
        if (c == KEY_UP) n->at = k > 0 ? at_x(n, k - 1, n->goal) : 0;
        else n->at = k + 1 < n->nlines ? at_x(n, k + 1, n->goal) : n->len;
    } else if (c == 8 || c == 127) {
        if (n->at == 0 || n->locked) return;
        char *t = TEXT;
        for (int i = n->at; i < n->len; i++) t[i - 1] = t[i];
        n->at--;
        n->len--;
        changed(n);
    } else if (c == '\r' || c == '\n') insert(n, "\n", 1);
    else if (c >= 32 && c < 127) { char ch = (char)c; insert(n, &ch, 1); }
}

static int on_delete(int x, int y) { return x >= DELETE_X && x < SIDE_W && y >= WIN_H - FOOT_H; }

/* A click at (x, y) in the window. */
COLD static void click(struct notes *n, struct line *l, int x, int y) {
    if (n->confirm && !on_delete(x, y)) keep(n, l);   /* a click anywhere else keeps it */
    if (x < SIDE_W) {
        if (x >= PLUS_X && x < PLUS_X + PLUS_S && y >= PLUS_Y && y < PLUS_Y + PLUS_S) new_note(n, l);
        else if (on_delete(x, y)) {
            if (n->confirm) delete_note(n, l);
            else ask_delete(n, l);
        } else if (y >= HEAD_H && y < HEAD_H + ROWS * ROW_H) {
            int i = n->list_top + (y - HEAD_H) / ROW_H;
            if (i < n->count) { choose(n, l, i); n->focus = 0; }
        }
        return;
    }
    if (y >= WIN_H - FOOT_H) return;
    fresh(n);
    int k = n->top + (y < TEXT_Y ? 0 : (y - TEXT_Y) / LINE_H);
    if (k >= n->nlines) k = n->nlines - 1;
    n->at = at_x(n, k, (x - TEXT_X) * 64);
    n->goal = -1;
    n->focus = 0;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct notes *n = (struct notes *)DATA;
    n->secret = SECRET;
    struct line l = {.n = 0};
    put_s(&l, "alice: wrote secret ");
    put_hex(&l, n->secret);
    put_s(&l, " to my data page\n");
    flush(&l);

    sys2(SYS_MAP, SPARE, SPARE_PAGE);
    const unsigned char *assets = (const unsigned char *)PAGE(SPARE_PAGE);
    n->head = font_of(assets, F_HEAD);
    n->body = font_of(assets, F_TEXT);
    n->small = font_of(assets, F_SMALL);
    n->bold = font_of(assets, F_BOLD);
    for (int c = 32; c < 127; c++) n->adv[c - 32] = n->body.glyphs ? glyph_of(&n->body, (unsigned)c)->advance : 64 * 8;
    n->focus = n->pasted = n->list_top = 0;
    fs_init(&n->fs, SPARE_PAGE);
    find_notes(n, &l);
    n->win = surface_of((unsigned *)PAGE(SPARE_PAGE + WIN_OFFSET), WIN_W, WIN_H);
    draw(n);

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
    say(&l);

    u64 dirty = 0;
    for (;;) {
        /* With a change not saved yet, she asks without waiting, to save when it is time. */
        struct res e = sys(SYS_CALL, ENDPOINT, n->unsaved ? OP_POLL : OP_WAIT, dirty, 0, 0);
        dirty = 0;
        if (n->secret != SECRET) {
            put_s(&l, "alice: SECRET CHANGED\n");
            flush(&l);
        }
        u64 kind = e.status == OK ? e.x[1] : EV_NONE;
        if (kind == EV_NONE) {            /* no event: ask again in a moment (app_wait) */
            if (n->unsaved && millis() >= n->save_at) {
                save(n, &l);
                draw(n);
                dirty = 1;
            } else sleep_ms(n->unsaved ? 20 : WAIT_AGAIN_MS);
            continue;
        }
        if (kind == EV_CLOSE) {
            if (n->unsaved) save(n, &l);
            put_s(&l, "alice: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (kind == EV_COPY) {
            u64 st = app_copy(TEXT, (u64)n->len);
            put_s(&l, "alice: copied ");
            put_dec(&l, (u64)(n->len < CLIP_MAX ? n->len : CLIP_MAX));
            put_s(&l, " bytes");
            put_s(&l, outcome(st));
            say(&l);
            continue;
        }
        if (kind == EV_PASTE) {
            /* a run of events: each piece goes in at the cursor, and the note is drawn when
               the last is in */
            struct event ev = {EV_PASTE, e.x[2], e.x[3]};
            char piece[16], take[16];
            int k = paste_text(ev, piece), m = 0;
            for (int i = 0; i < k; i++) {
                char c = piece[i] == '\r' ? '\n' : piece[i];
                if (c == '\n' || (c >= 32 && c < 127)) take[m++] = c;
            }
            if (n->confirm) keep(n, &l);
            n->focus = 0;
            int before = n->len;
            insert(n, take, m);
            n->pasted += n->len - before;
            if (k == 16) {                /* saved when it is all in (or if the rest is long in coming) */
                n->save_at = millis() + 5 * SAVE_AFTER;
                continue;
            }
            n->save_at = millis() + SAVE_AFTER;
            put_s(&l, "alice: pasted ");
            put_dec(&l, (u64)n->pasted);
            put_s(&l, " bytes");
            say(&l);
            n->pasted = 0;
        } else if (kind == EV_KEY) {
            u64 c = e.x[2];
            if (n->confirm) {             /* Ctrl+D again deletes; any other key keeps it */
                if (c == CTRL_D) delete_note(n, &l);
                else keep(n, &l);
            } else if (c == CTRL_D) ask_delete(n, &l);
            else if (c == CTRL_N) new_note(n, &l);
            else key(n, &l, c);
        } else if (kind == EV_DOWN) click(n, &l, (int)e.x[2], (int)e.x[3]);
        else continue;
        draw(n);
        dirty = 1;
    }
}
