/* edit: a text editor, from the SD card. It edits the file it was given (`run edit
   notes.txt` in Terminal gives it notes.txt), or, given none, apps/edit/untitled.txt in its
   own folder; the file server lets it reach nothing else, and says so if it tries.

   Type to insert (Tab too), Backspace deletes, Delete deletes the letter after the cursor,
   Enter starts a line, the arrow keys move, Home and End go to the line's start and end,
   and Page Up and Page Down a window of lines (and scroll as many). A tab shows as the
   spaces to the next column of four. Lines are not wrapped: the view scrolls sideways to
   the cursor. The status line shows the line and the column (from 1) and, with a
   selection, how many bytes it holds.

   The mouse: a click puts the cursor there, a drag selects, a double-click selects a word.
   The window hears the whole drag (app_open_drag); a drag past the top or bottom scrolls.

   The keyboard: Ctrl+A selects all, and Shift with an arrow, Home, End, Page Up or Page
   Down moves the cursor and selects from where it was (or grows the selection there is,
   from its other end). A serial terminal sends these as ESC [ 1 ; 2 C and the like, which
   the input driver turns into keys of their own (user/app.h), and so does the USB driver.
   A selection can also be made as Emacs makes one, for a terminal that sends no Shift:
   Ctrl+B sets a mark at the cursor, and the keys that move the cursor then select from the
   mark to it; Ctrl+B again, or Escape, drops it. Any other move drops a selection. Typing,
   a paste, Backspace or Delete replaces or deletes what is selected.

     Ctrl+A  select all          Ctrl+B  mark (select by moving)
     Ctrl+Z  undo                Ctrl+Y  redo
     Ctrl+F  find                F3      find the next
     Ctrl+G  go to a line        Ctrl+S  save now

   Copy (Ctrl+C) takes the selection, or, with nothing selected, the whole text; either way
   its first 4 KiB (what the clipboard holds), tabs as spaces (the clipboard keeps no tabs).
   Cut (Ctrl+X) copies the same way and then deletes the selection (one step, for undo), but
   only if the display took the copy; with nothing selected it copies as Ctrl+C does and
   deletes nothing; a selection larger than the clipboard (4 KiB) is copied in part, and not
   deleted. The display asks for either only after the user's key (user/display.c); edit
   never asks. A paste (Ctrl+V) goes in at the cursor, in place of the selection.

   Undo takes back a step at a time, as many as its memory holds (below): a run of typing
   is one step, until the cursor moves or a line ends; so is a run of Backspace or of
   Delete, a paste, a deletion of a selection, and typing over one. When a step needs room,
   the oldest go. Text that undo brings back comes back selected.

   Find: Ctrl+F opens a field in the status line. What you type is found as you type it,
   forward from where the search began, round past the end, letters in either case, and
   selected; Return finds the next; Escape (or Ctrl+F again, or any move) closes the field,
   leaving the match selected. A serial line cannot send Escape by itself: Ctrl+F closes it
   there. F3 finds the next, the field open or not (with nothing looked for yet, it opens
   the field). Ctrl+G opens "Go to line" the same way: digits, then Return.

   It saves by itself a moment after you stop typing (Ctrl+S saves at once), and when its
   window closes. A file holds up to 64 KiB. One up to 16 KiB is written in one request,
   which the file server makes one journaled change; a larger one goes into
   apps/edit/save.part~ in pieces (a request moves at most 16 KiB) and is then renamed over
   the file in one journaled step. Either way, after a power cut the file is the last save
   or the one before, never half of each. A file larger than 64 KiB, or a folder, is not
   opened, and never saved over.

   Memory. A program has 8 data pages (struct edit) and a spare run of 228 pages
   (user/app.h), which holds, in order: the fonts (36 pages today), the text (16 pages,
   64 KiB), undo (what is left before the window: 19 pages, 77,824 bytes, while the fonts
   are what they are), the window (520 x 300 pixels, 153 pages) and the file server's
   buffer (4 pages). Undo holds more than the text: a step as large as the whole text
   (deleting it all, say, or typing over all of it) fits. A step that does not fit (if
   the fonts grew, or 64 KiB is typed over 64 KiB selected) empties undo, and the steps
   after it are kept again. */
#include "../ui.h"
#include "../fs.h"

#define EW 520
#define EH 300
#define PAD 12
#define STATUS_H 24
#define LINE_H 18
#define TAB 4                     /* a tab reaches the next column of four */
#define TEXT_PAGES 16
#define TEXT_MAX (TEXT_PAGES * 4096L)   /* 64 KiB */
#define WIN_PAGES ((EW * EH * 4 + 4095) / 4096)
#define WIN_OFF (FS_BUF_OFFSET - WIN_PAGES)   /* the window's pixels end where the file buffer begins */
#define SAVE_AFTER 800            /* ms without typing */
#define SAVE_AGAIN 10000          /* ms after a save that failed */
#define DOUBLE_MS 500             /* a second press this soon, in the same place: a double-click */
#define FIELD_MAX 40
#define ROWS ((EH - STATUS_H - PAD) / LINE_H)   /* the lines a window shows */
#define TMP "apps/edit/save.part~"

/* Undo's steps, for the log, and the runs of keys that join one step. */
enum { K_TYPE, K_DELETE, K_PASTE };
static const char *const kind_name[] = {"typing", "a deletion", "a paste"};
enum { G_NONE, G_TYPE, G_BACK, G_DEL, G_PASTE };
enum { P_NONE, P_FIND, P_GOTO };

/* Undo's memory: records, one after another. A record is a header of three words (where,
   how many bytes, and bit 0 an insertion (else a deletion), bit 1 the first record of a
   step, bits 4-7 the step's kind), the bytes inserted or deleted, padded to 4, and its whole
   size again as a trailer, so the records can be walked either way. Records [0, now) are
   done and can be undone; [now, top) were undone and can be redone. */
#define START 2u
struct undo {
    unsigned char *m;
    u64 size, now, top;
    u64 start;                 /* where the step being made begins */
    long nundo, nredo;         /* whole steps each way */
    int open, fresh;           /* a step is being made; its first record is still to come */
    int kind, group;           /* its kind, and the run of keys it takes more of */
    int lost;                  /* the step being made did not fit: undo was emptied */
};

struct edit {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    char path[FS_PATH_MAX + 1];
    char *text;                /* in the spare run, TEXT_MAX bytes */
    long len, cur, top, left;  /* the text, the cursor, the first line and column shown */
    long mark;                 /* the selection's other end (the cursor is one), or -1 */
    int marking;               /* Ctrl+B: moves select from the mark */
    int cw;                    /* a character's width in the monospaced font */
    int dirty, locked;         /* changed since the last save; not opened, never saved over */
    u64 save_at;
    int drag;                  /* a drag selects (1), or a double-click chose a word (2) */
    u64 click_at;
    int click_x, click_y;
    long pasted;               /* bytes of the paste now arriving */
    int paste_short;           /* some of it did not fit */
    int prompt, flen;          /* the field in the status line (P_FIND, P_GOTO), and its text */
    int last;                  /* the field opened last (its text is what F3 finds) */
    char field[FIELD_MAX + 1];
    long origin;               /* where the match found last begins (where finding began) */
    struct undo u;
    char status[96];
    char clip[CLIP_MAX];       /* a copy, its tabs as spaces */
};

static void set_status(struct edit *e, const char *a, const char *b) {
    int n = 0;
    for (int i = 0; a[i] && n < 95; i++) e->status[n++] = a[i];
    for (int i = 0; b && b[i] && n < 95; i++) e->status[n++] = b[i];
    e->status[n] = 0;
}

static int cat(char *b, int n, int max, const char *s) {
    while (*s && n < max) b[n++] = *s++;
    b[n] = 0;
    return n;
}
static int cat_dec(char *b, int n, int max, u64 v) {
    char t[20];
    int i = 0;
    do t[i++] = (char)('0' + v % 10); while (v /= 10);
    while (i && n < max) b[n++] = t[--i];
    b[n] = 0;
    return n;
}

/* ---- the text ---- */

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
/* The start of line n (from 0), or of the last line. */
static long nth_line(struct edit *e, long n) {
    long i = 0;
    for (long k = 0; k < e->len && n > 0; k++)
        if (e->text[k] == '\n') {
            n--;
            i = k + 1;
        }
    return i;
}
/* How many columns the byte at k takes, at column vc: a tab reaches the next column of four. */
static int width_at(struct edit *e, long k, long vc) { return e->text[k] == '\t' ? TAB - (int)(vc % TAB) : 1; }
/* The column `at` is shown at, tabs counted as they show. */
static long vcol(struct edit *e, long at) {
    long vc = 0;
    for (long k = line_start(e, at); k < at; k++) vc += width_at(e, k, vc);
    return vc;
}
/* In the line that begins at ls: the last place at column `want` or before it. */
static long at_col(struct edit *e, long ls, long want) {
    long k = ls, vc = 0, end = line_end(e, ls);
    while (k < end) {
        int w = width_at(e, k, vc);
        if (vc + w > want) break;
        vc += w;
        k++;
    }
    return k;
}

static int has_sel(struct edit *e) { return e->mark >= 0 && e->mark != e->cur; }
static long sel_lo(struct edit *e) { return e->mark < e->cur ? e->mark : e->cur; }
static long sel_hi(struct edit *e) { return e->mark < e->cur ? e->cur : e->mark; }

/* The text itself, with nothing recorded. */
static void t_ins(struct edit *e, long pos, const char *s, long n) {
    for (long i = e->len - 1; i >= pos; i--) e->text[i + n] = e->text[i];
    for (long i = 0; i < n; i++) e->text[pos + i] = s[i];
    e->len += n;
}
static void t_del(struct edit *e, long pos, long n) {
    for (long i = pos; i + n < e->len; i++) e->text[i] = e->text[i + n];
    e->len -= n;
}

/* ---- undo ---- */

static u64 rsize(u64 n) { return 12 + ((n + 3) & ~3UL) + 4; }
static unsigned *rec(struct undo *u, u64 at) { return (unsigned *)(u->m + at); }
static u64 before(struct undo *u, u64 at) { return at - *(unsigned *)(u->m + at - 4); }   /* the record ending at `at` */
static void seal(struct undo *u, u64 at) {
    u64 sz = rsize(rec(u, at)[1]);
    *(unsigned *)(u->m + at + sz - 4) = (unsigned)sz;
}

static void u_clear(struct undo *u) {
    u->now = u->top = u->start = 0;
    u->nundo = u->nredo = 0;
    u->fresh = 1;
}

/* Room for `need` more bytes after the last record: the oldest steps go, never the one being
   made. 0 if even that is not enough. */
static int u_room(struct undo *u, u64 need) {
    while (u->top + need > u->size) {
        if (u->start == 0) return 0;         /* only the step being made is left */
        u64 at = 0;
        do at += rsize(rec(u, at)[1]);
        while (at < u->top && !(rec(u, at)[2] & START));
        for (u64 i = at; i < u->top; i++) u->m[i - at] = u->m[i];
        u->top -= at;
        u->now -= at;
        u->start -= at;
        u->nundo--;
    }
    return 1;
}

/* A step too large for undo's memory: nothing before it can be undone either (the text no
   longer is what those steps left), so undo forgets everything, and records nothing more
   of this step (undo would stop in the middle of it); the next step is kept again. */
static void u_lose(struct undo *u) {
    u_clear(u);
    u->lost = 1;
}

static void u_begin(struct edit *e, int kind, int group) {
    struct undo *u = &e->u;
    u->top = u->now;                         /* what was undone can no longer be redone */
    u->nredo = 0;
    u->start = u->top;
    u->open = u->fresh = 1;
    u->lost = 0;
    u->kind = kind;
    u->group = group;
}
static void u_close(struct edit *e) {
    e->u.open = 0;
    e->u.group = G_NONE;
}
/* A change of this kind: it joins the step being made if that is the same run of keys. */
static void step(struct edit *e, int kind, int group) {
    if (group == G_NONE || !e->u.open || e->u.group != group) u_begin(e, kind, group);
}

/* Record that n bytes s were inserted (ins) or deleted at pos: into the step's last record
   if they continue it (typing on, a paste's next piece, Backspace or Delete again), else
   as a record of their own. */
static void u_add(struct edit *e, unsigned ins, long pos, const char *s, long n) {
    struct undo *u = &e->u;
    if (!u->open || u->lost) return;
    if (u->top > u->start) {
        u64 at = before(u, u->top);
        unsigned *h = rec(u, at);
        long hp = h[0], hn = h[1];
        int back = !ins && pos + n == hp;    /* Backspace: just before the last deletion */
        if ((h[2] & 1) == ins && (ins ? pos == hp + hn : pos == hp || back)) {
            u64 extra = rsize((u64)(hn + n)) - rsize((u64)hn);
            if (u_room(u, extra)) {
                at = before(u, u->top);      /* older steps may have gone: it moved */
                h = rec(u, at);
                unsigned char *b = u->m + at + 12;
                if (back) {
                    for (long i = hn - 1; i >= 0; i--) b[i + n] = b[i];
                    for (long i = 0; i < n; i++) b[i] = (unsigned char)s[i];
                    h[0] = (unsigned)pos;
                } else {
                    for (long i = 0; i < n; i++) b[hn + i] = (unsigned char)s[i];
                }
                h[1] = (unsigned)(hn + n);
                u->top += extra;
                u->now = u->top;
                seal(u, at);
                return;
            }
            u_lose(u);
            return;
        }
    }
    u64 need = rsize((u64)n);
    if (!u_room(u, need)) {
        u_lose(u);
        return;
    }
    unsigned *h = rec(u, u->top);
    h[0] = (unsigned)pos;
    h[1] = (unsigned)n;
    h[2] = ins | (u->fresh ? START | (unsigned)u->kind << 4 : 0);
    if (u->fresh) u->nundo++;
    u->fresh = 0;
    for (long i = 0; i < n; i++) u->m[u->top + 12 + (u64)i] = (unsigned char)s[i];
    seal(u, u->top);
    u->top += need;
    u->now = u->top;
}

/* Do a record (forward) or take it back. Text that comes back with an undo is selected. */
static void apply(struct edit *e, const unsigned *h, int forward) {
    long pos = h[0], n = h[1];
    int in = (int)(h[2] & 1) == forward;     /* an insertion done, or a deletion undone */
    if (in) t_ins(e, pos, (const char *)(h + 3), n);
    else t_del(e, pos, n);
    e->cur = in ? pos + n : pos;
    e->mark = in && !forward ? pos : -1;
}

/* Undo or redo a step: its kind, or -1 if there is none. */
static int undo(struct edit *e, int redo) {
    struct undo *u = &e->u;
    u_close(e);
    e->marking = 0;
    if (redo ? !u->nredo : !u->nundo) return -1;
    const unsigned *h;
    if (!redo) {
        do {
            u64 at = before(u, u->now);
            h = rec(u, at);
            apply(e, h, 0);
            u->now = at;
        } while (!(h[2] & START));
        u->nundo--;
        u->nredo++;
        return (int)(h[2] >> 4 & 15);
    }
    h = rec(u, u->now);
    int kind = (int)(h[2] >> 4 & 15);
    for (;;) {
        apply(e, h, 1);
        u->now += rsize(h[1]);
        if (u->now >= u->top) break;
        h = rec(u, u->now);
        if (h[2] & START) break;
    }
    u->nredo--;
    u->nundo++;
    return kind;
}

/* ---- the log ---- */

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static void put_where(struct line *l, struct edit *e, long at) {
    put_s(l, "line ");
    put_dec(l, (u64)line_of(e, at) + 1);
    put_s(l, ", column ");
    put_dec(l, (u64)vcol(e, at) + 1);
}

/* Up to 40 bytes of the text from `at`, line breaks as \n. */
static void put_text(struct line *l, struct edit *e, long at, long n) {
    char c[2] = {0, 0};
    for (long k = at; k < at + n && k < at + 40; k++) {
        c[0] = e->text[k] >= 32 && e->text[k] < 127 ? e->text[k] : '?';
        put_s(l, e->text[k] == '\n' ? "\\n" : c);
    }
    if (n > 40) put_s(l, "...");
}

static void say_selected(struct edit *e, struct line *l) {
    long a = sel_lo(e), n = sel_hi(e) - a;
    put_s(l, "edit: selected ");
    put_dec(l, (u64)n);
    put_s(l, n == 1 ? " byte at " : " bytes at ");
    put_where(l, e, a);
    put_s(l, ": ");
    put_text(l, e, a, n);
    say(l);
}

/* ---- saving ---- */

static void save(struct edit *e, struct line *l) {
    if (e->locked) {
        e->dirty = 0;
        return;
    }
    struct fs_client *c = &e->fs;
    u64 n = (u64)e->len, st;
    if (n <= FS_CHUNK) {
        st = fs_write(c, e->path, e->text, n);      /* one request: one journaled change */
    } else {
        st = fs_write(c, TMP, e->text, FS_CHUNK);   /* in pieces, then one rename */
        for (u64 at = FS_CHUNK; at < n && st == FS_OK; at += FS_CHUNK)
            st = fs_write_at(c, TMP, at, e->text + at, n - at < FS_CHUNK ? n - at : FS_CHUNK);
        if (st == FS_OK) st = fs_rename(c, TMP, e->path);
        if (st != FS_OK) fs_delete(c, TMP);
    }
    if (st == FS_OK) e->dirty = 0;
    else e->save_at = millis() + SAVE_AGAIN;
    set_status(e, st == FS_OK ? "saved" : st == FS_DENIED ? "not given to edit: not saved"
                : st == FS_FULL ? "the card is full: not saved" : "could not save", 0);
    put_s(l, "edit: saved ");
    put_s(l, e->path);
    put_s(l, " (");
    put_dec(l, n);
    put_s(l, st == FS_OK ? " bytes)" : " bytes) -> refused");
    say(l);
}

/* ---- editing ---- */

static int editable(struct edit *e) {
    if (e->locked) set_status(e, "not opened, so not edited", 0);
    return !e->locked;
}

static void changed(struct edit *e, const char *what) {
    e->dirty = 1;
    e->save_at = millis() + SAVE_AFTER;
    e->mark = -1;
    e->marking = 0;
    set_status(e, e->u.lost ? "too large to undo" : what, 0);
}

/* n bytes at the cursor, as many as fit: how many went in. */
static long put_in(struct edit *e, const char *s, long n) {
    if (n > TEXT_MAX - e->len) n = TEXT_MAX - e->len;
    if (n <= 0) return 0;
    t_ins(e, e->cur, s, n);
    u_add(e, 1, e->cur, s, n);
    e->cur += n;
    return n;
}

/* The selection goes. */
static void delete_sel(struct edit *e) {
    long a = sel_lo(e), n = sel_hi(e) - a;
    u_add(e, 0, a, e->text + a, n);
    t_del(e, a, n);
    e->cur = a;
    e->mark = -1;
}

static void type(struct edit *e, char c) {
    if (!editable(e)) return;
    int had = has_sel(e);
    if (had) {
        u_begin(e, K_TYPE, G_TYPE);          /* typing over a selection: one step with it */
        delete_sel(e);
    } else step(e, K_TYPE, G_TYPE);
    long in = put_in(e, &c, 1);
    if (in || had) changed(e, "editing");
    if (!in) set_status(e, "full: 64 KiB", 0);
    if (c == '\n') u_close(e);               /* a line ends a run of typing */
}

static void erase(struct edit *e, int forward) {
    if (!editable(e)) return;
    if (has_sel(e)) {
        u_begin(e, K_DELETE, G_NONE);
        delete_sel(e);
    } else {
        long at = forward ? e->cur : e->cur - 1;
        e->mark = -1;
        if (at < 0 || at >= e->len) return;
        step(e, K_DELETE, forward ? G_DEL : G_BACK);
        u_add(e, 0, at, e->text + at, 1);
        t_del(e, at, 1);
        e->cur = at;
    }
    changed(e, "editing");
}

/* The cursor goes to `to`: selecting from the mark (from where the cursor was, if there is
   none) with Shift held (`select`) or while marking, else dropping a selection. */
static void move(struct edit *e, long to, int select) {
    u_close(e);
    if (select || e->marking) {
        if (e->mark < 0) e->mark = e->cur;
    } else e->mark = -1;
    e->cur = to;
}

static void undo_key(struct edit *e, struct line *l, int redo) {
    if (!editable(e)) return;
    int kind = undo(e, redo);
    if (kind < 0) {
        set_status(e, redo ? "nothing to redo" : "nothing to undo", 0);
        return;
    }
    long mark = e->mark;
    changed(e, redo ? "redone" : "undone");
    e->mark = mark;                          /* what came back stays selected */
    put_s(l, redo ? "edit: redid " : "edit: undid ");
    put_s(l, kind_name[kind]);
    put_s(l, "; ");
    put_dec(l, (u64)e->u.nundo);
    put_s(l, e->u.nundo == 1 ? " step to undo, " : " steps to undo, ");
    put_dec(l, (u64)e->u.nredo);
    put_s(l, " to redo");
    say(l);
}

/* ---- find, and go to a line ---- */

static char lower(char c) { return c >= 'A' && c <= 'Z' ? (char)(c + 32) : c; }

/* Where the field's text is next, from `from` round past the end, in either case; -1 if
   nowhere. */
static long search(struct edit *e, long from) {
    long n = e->flen;
    for (long i = 0; i < e->len; i++) {
        long at = (from + i) % e->len;
        if (at + n > e->len) continue;
        long k = 0;
        while (k < n && lower(e->text[at + k]) == lower(e->field[k])) k++;
        if (k == n) return at;
    }
    return -1;
}

static void find(struct edit *e, struct line *l, long from) {
    if (!e->flen) {
        e->mark = -1;
        e->cur = e->origin;
        set_status(e, "", 0);
        return;
    }
    long at = search(e, from);
    put_s(l, "edit: find \"");
    put_s(l, e->field);
    if (at < 0) {
        set_status(e, "not found", 0);
        put_s(l, "\": not found");
        say(l);
        return;
    }
    e->origin = at;
    e->mark = at;
    e->cur = at + e->flen;
    set_status(e, "found", 0);
    put_s(l, "\": at ");
    put_where(l, e, at);
    say(l);
}

static void go_to(struct edit *e, struct line *l) {
    long n = 0;
    for (int i = 0; i < e->flen; i++) n = n * 10 + (e->field[i] - '0');
    e->prompt = P_NONE;
    set_status(e, "", 0);
    if (!e->flen) return;
    move(e, nth_line(e, n > 0 ? n - 1 : 0), 0);
    put_s(l, "edit: went to line ");
    put_dec(l, (u64)line_of(e, e->cur) + 1);
    say(l);
}

static void open_prompt(struct edit *e, int which) {
    u_close(e);
    e->marking = 0;
    e->prompt = e->last = which;
    e->flen = 0;
    e->field[0] = 0;
    e->origin = has_sel(e) ? sel_lo(e) : e->cur;
    set_status(e, which == P_FIND ? "Return: next, Escape: close" : "Return: go, Escape: close", 0);
}

static void close_prompt(struct edit *e) {
    e->prompt = P_NONE;
    set_status(e, "", 0);
}

/* A key while the field is open: 1 if the field took it. Any other key closes the field, and
   does what it does. */
static int prompt_key(struct edit *e, struct line *l, u64 k) {
    if (k == 27 || (k == 6 && e->prompt == P_FIND) || (k == 7 && e->prompt == P_GOTO)) {
        close_prompt(e);
        return 1;
    }
    if (k == 127 || k == 8) {
        if (e->flen) e->field[--e->flen] = 0;
    } else if (k == '\r' || k == '\n' || (k == KEY_F(3) && e->prompt == P_FIND)) {
        if (e->prompt == P_GOTO) go_to(e, l);
        else if (e->flen) find(e, l, e->origin + 1);
        return 1;
    } else if (k >= 32 && k < 127) {
        if (e->prompt == P_GOTO && (k < '0' || k > '9')) return 1;
        if (e->flen < FIELD_MAX) {
            e->field[e->flen++] = (char)k;
            e->field[e->flen] = 0;
        }
    } else {
        close_prompt(e);
        return 0;
    }
    if (e->prompt == P_FIND) find(e, l, e->origin);
    return 1;
}

/* F3: the next match of what was looked for last, after the selection (a match found last)
   or from the cursor; with nothing looked for yet, the find field. */
static void find_next(struct edit *e, struct line *l) {
    if (e->last != P_FIND || !e->flen) {
        open_prompt(e, P_FIND);
        return;
    }
    u_close(e);
    e->marking = 0;
    find(e, l, has_sel(e) ? sel_lo(e) + 1 : e->cur);
}

/* ---- keys ---- */

static void key(struct edit *e, struct line *l, u64 k) {
    if (e->prompt && prompt_key(e, l, k)) return;
    long ls = line_start(e, e->cur), col = vcol(e, e->cur);
    int shift = KEY_IS_SHIFTED(k);               /* Shift and a move: select as it moves */
    k = KEY_UNSHIFTED(k);
    if (k == 127 || k == 8) erase(e, 0);
    else if (k == KEY_DELETE) erase(e, 1);
    else if (k == '\r' || k == '\n') type(e, '\n');
    else if (k == '\t' || (k >= 32 && k < 127)) type(e, (char)k);
    else if (k == KEY_HOME) move(e, ls, shift);
    else if (k == KEY_END) move(e, line_end(e, e->cur), shift);
    else if (k == KEY_LEFT) move(e, e->cur > 0 ? e->cur - 1 : 0, shift);
    else if (k == KEY_RIGHT) move(e, e->cur < e->len ? e->cur + 1 : e->len, shift);
    else if (k == KEY_UP) move(e, ls > 0 ? at_col(e, line_start(e, ls - 1), col) : e->cur, shift);
    else if (k == KEY_DOWN) {
        long le = line_end(e, e->cur);
        move(e, le < e->len ? at_col(e, le + 1, col) : e->cur, shift);
    } else if (k == KEY_PGUP || k == KEY_PGDN) {
        /* ROWS lines up or down (fewer at the first or last), at the same column if the line
           is that long, and the text scrolls as many, not past its last line */
        long at = ls;
        for (int r = 0; r < ROWS; r++) {
            if (k == KEY_PGUP) {
                if (at == 0) break;
                at = line_start(e, at - 1);
            } else {
                long le = line_end(e, at);
                if (le >= e->len) break;
                at = le + 1;
            }
        }
        long most = line_of(e, e->len) + 1 - ROWS;
        move(e, at_col(e, at, col), shift);
        e->top += k == KEY_PGUP ? -ROWS : ROWS;
        if (e->top > most) e->top = most;
        if (e->top < 0) e->top = 0;
    } else if (k == 1) {                                      /* Ctrl+A */
        u_close(e);
        e->marking = 0;
        e->mark = 0;
        e->cur = e->len;
        set_status(e, "all selected", 0);
        say_selected(e, l);
    } else if (k == 2) {                                      /* Ctrl+B */
        u_close(e);
        e->marking = !e->marking;
        e->mark = e->marking ? e->cur : -1;
        set_status(e, e->marking ? "mark set: move to select" : "", 0);
        put_s(l, e->marking ? "edit: mark set at " : "edit: mark dropped at ");
        put_where(l, e, e->cur);
        say(l);
    } else if (k == 27) {                                     /* Escape */
        e->marking = 0;
        e->mark = -1;
        set_status(e, "", 0);
    } else if (k == 6) open_prompt(e, P_FIND);                /* Ctrl+F */
    else if (k == 7) open_prompt(e, P_GOTO);                  /* Ctrl+G */
    else if (k == 19) save(e, l);                             /* Ctrl+S */
    else if (k == KEY_F(3)) find_next(e, l);
    else if (k == 26 || k == 25) undo_key(e, l, k == 25);    /* Ctrl+Z, Ctrl+Y */
}

/* ---- the mouse ---- */

/* The place nearest (x, y) in the window; above or below the lines shown, on the line before
   or after them (so a drag there scrolls). */
static long hit(struct edit *e, int x, int y) {
    long row = y < PAD ? -1 : (y - PAD) / LINE_H;
    long line = e->top + row;
    long ls = nth_line(e, line < 0 ? 0 : line), end = line_end(e, ls), k = ls, vc = 0;
    long px = x - PAD + e->left * e->cw;
    while (k < end) {
        int w = width_at(e, k, vc);
        if ((2 * vc + w) * e->cw > 2 * px) break;
        vc += w;
        k++;
    }
    return k;
}

/* What a double-click takes a run of: a word's letters, digits and _ (1), or blanks (2);
   anything else (0) alone. */
static int kind_of(char c) {
    if ((c >= '0' && c <= '9') || (lower(c) >= 'a' && lower(c) <= 'z') || c == '_') return 1;
    return c == ' ' || c == '\t' ? 2 : 0;
}

static void press(struct edit *e, struct line *l, int x, int y) {
    if (e->prompt) close_prompt(e);
    if (y >= EH - STATUS_H) return;
    u_close(e);
    e->marking = 0;
    long at = hit(e, x, y);
    u64 t = millis();
    int dx = x - e->click_x, dy = y - e->click_y;
    int twice = e->click_at && t - e->click_at < DOUBLE_MS && dx >= -4 && dx <= 4 && dy >= -4 && dy <= 4;
    e->click_at = twice ? 0 : t;             /* a third press begins again */
    e->click_x = x;
    e->click_y = y;
    e->cur = e->mark = at;
    e->drag = 1;
    if (!twice) return;
    e->drag = 2;
    long a = at;
    if (a == line_end(e, a) && a > line_start(e, a)) a--;        /* after a line's end: its last word */
    if (a >= e->len || e->text[a] == '\n') return;
    int c = kind_of(e->text[a]);
    long s = a, z = a + 1;
    if (c) {
        while (s > 0 && kind_of(e->text[s - 1]) == c) s--;
        while (z < e->len && kind_of(e->text[z]) == c) z++;
    }
    e->mark = s;
    e->cur = z;
    say_selected(e, l);
}

static void release(struct edit *e, struct line *l, int x, int y) {
    if (e->drag == 1) {
        e->cur = hit(e, x, y);
        if (has_sel(e)) say_selected(e, l);
        else {
            e->mark = -1;
            put_s(l, "edit: cursor at ");
            put_where(l, e, e->cur);
            say(l);
        }
    }
    e->drag = 0;
}

/* ---- copy and paste ---- */

/* EV_COPY: the selection (or all the text) to the display. A cut (`cut`) then deletes the
   selection, once the display has taken all of it; with nothing selected, nothing. */
static void copy(struct edit *e, struct line *l, int cut) {
    int sel = has_sel(e);
    long a = sel ? sel_lo(e) : 0, b = sel ? sel_hi(e) : e->len, n = 0, vc = vcol(e, a), k = a;
    for (; k < b && n < CLIP_MAX; k++) {
        char c = e->text[k];
        if (c == '\t') {
            for (int w = width_at(e, k, vc); w > 0 && n < CLIP_MAX; w--, vc++) e->clip[n++] = ' ';
        } else {
            e->clip[n++] = c;
            vc = c == '\n' ? 0 : vc + 1;
        }
    }
    u64 st = app_copy(e->clip, (u64)n);
    cut = cut && sel && k == b;                  /* a cut: all of a selection, or nothing */
    put_s(l, cut ? "edit: cut " : "edit: copied ");
    put_dec(l, (u64)n);
    put_s(l, " bytes");
    put_s(l, outcome(st));
    say(l);
    if (st != OK) set_status(e, "not copied", 0);
    else if (!cut) set_status(e, k < b ? "only its first 4 KiB copied, nothing cut" : sel ? "copied the selection" : "copied", 0);
    else if (editable(e)) {
        u_close(e);
        e->marking = 0;
        u_begin(e, K_DELETE, G_NONE);
        delete_sel(e);
        changed(e, "cut");
    }
}

/* A piece of a paste, at the cursor (in place of the selection, with the first piece); after
   the last piece, say what arrived. */
static int paste_in(struct edit *e, struct line *l, struct event ev) {
    char piece[16], ok[16];
    int k = paste_text(ev, piece), m = 0;
    for (int i = 0; i < k; i++) {
        char c = piece[i] == '\r' ? '\n' : piece[i];
        if (c == '\n' || c == '\t' || (c >= 32 && c < 127)) ok[m++] = c;
    }
    if (!e->locked) {
        int first = e->pasted == 0 && e->u.group != G_PASTE;
        if (first && has_sel(e)) {
            u_begin(e, K_PASTE, G_PASTE);
            delete_sel(e);
        } else step(e, K_PASTE, G_PASTE);
        long in = put_in(e, ok, m);
        e->pasted += in;
        e->paste_short |= in < m;
        changed(e, "editing");
    }
    if (k == 16) return 0;
    u_close(e);
    if (!e->locked && !e->u.lost) set_status(e, e->paste_short ? "full: 64 KiB, the rest not pasted" : "pasted", 0);
    put_s(l, "edit: pasted ");
    put_dec(l, (u64)e->pasted);
    put_s(l, " bytes");
    say(l);
    e->pasted = 0;
    e->paste_short = 0;
    return 1;
}

/* ---- drawing ---- */

static void draw(struct edit *e) {
    struct surface *s = &e->win;
    int cw = e->cw, cols = (EW - 2 * PAD) / cw;
    fill(s, 0, 0, EW, EH - STATUS_H, rgb(252, 252, 250));
    long cl = line_of(e, e->cur), cc = vcol(e, e->cur);
    if (cl < e->top) e->top = cl;
    if (cl >= e->top + ROWS) e->top = cl - ROWS + 1;
    if (cc < e->left) e->left = cc > cols / 2 ? cc - cols / 2 : 0;
    if (cc > e->left + cols) e->left = cc - cols / 2;
    long lo = has_sel(e) ? sel_lo(e) : -1, hi = has_sel(e) ? sel_hi(e) : -1;
    long i = nth_line(e, e->top);
    for (int r = 0; r < ROWS; r++) {
        int y0 = PAD + LINE_H * r;
        long end = line_end(e, i), vc = 0;
        for (long k = i;; k++) {
            long sc = vc - e->left;
            int x = PAD + (int)sc * cw, w = k < end ? width_at(e, k, vc) : 1;
            if (k >= lo && k < hi && sc + w > 0 && sc < cols) {       /* selected (a line break: half a cell) */
                int x0 = sc < 0 ? PAD : x, x1 = k < end ? PAD + (int)(sc + w > cols ? cols : sc + w) * cw : x + cw / 2;
                fill(s, x0, y0, x1 - x0, LINE_H, rgb(191, 213, 250));
            }
            if (k == e->cur && sc >= 0 && sc <= cols) fill(s, x, y0, 2, LINE_H - 2, rgb(58, 110, 230));
            if (k == end) break;
            char ch = e->text[k];
            if (ch != '\t' && sc >= 0 && sc < cols) {
                char c[2] = {ch >= 32 && ch < 127 ? ch : '?', 0};
                font_text(s, &e->ui.mono, x, y0 + 13, c, rgb(36, 38, 46));
            }
            vc += w;
        }
        if (end >= e->len) break;
        i = end + 1;
    }

    /* the status line: the file (or the field); what happened, and where the cursor is */
    fill(s, 0, EH - STATUS_H, EW, STATUS_H, rgb(238, 239, 243));
    char right[160];
    int n = cat(right, 0, 150, e->status);
    if (n) n = cat(right, n, 150, "    ");
    if (has_sel(e)) {
        n = cat_dec(right, n, 150, (u64)(sel_hi(e) - sel_lo(e)));
        n = cat(right, n, 150, " selected    ");
    }
    n = cat(right, n, 150, "Ln ");
    n = cat_dec(right, n, 150, (u64)cl + 1);
    n = cat(right, n, 150, ", Col ");
    cat_dec(right, n, 150, (u64)cc + 1);
    font_text(s, &e->ui.small, EW - PAD - font_width(&e->ui.small, right), EH - 8, right, rgb(120, 122, 134));
    if (e->prompt) {
        const char *label = e->prompt == P_FIND ? "Find: " : "Go to line: ";
        int x = PAD + font_width(&e->ui.small_bold, label);
        font_text(s, &e->ui.small_bold, PAD, EH - 8, label, rgb(60, 62, 74));
        font_text(s, &e->ui.small, x, EH - 8, e->field, rgb(36, 38, 46));
        fill(s, x + font_width(&e->ui.small, e->field) + 1, EH - STATUS_H + 5, 2, STATUS_H - 10, rgb(58, 110, 230));
    } else {
        font_text(s, &e->ui.small_bold, PAD, EH - 8, e->path, rgb(60, 62, 74));
    }
}

/* ---- starting ---- */

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

/* Where the fonts end in the spare run: the first page after the last asset (as paint). */
static u64 assets_end(const unsigned char *blob) {
    const unsigned *h = (const unsigned *)blob;
    u64 end = 0;
    for (unsigned i = 0; h[0] == 0x53414e4c && i < h[2]; i++) {
        const unsigned *a = h + 3 + 4 * i;
        if (a[2] + a[3] > end) end = a[2] + a[3];
    }
    return (end + 4095) / 4096;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct edit *e = (struct edit *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    ui_load(&e->ui, assets);
    e->win = app_surface_at(WIN_OFF, EW, EH);
    fs_init(&e->fs, SPARE_PAGE);
    u64 first = assets_end(assets);
    if (first + TEXT_PAGES >= WIN_OFF) {
        put_s(&l, "edit: no room for the text after the fonts");
        say(&l);
        exit_task();
    }
    e->text = (char *)PAGE(SPARE_PAGE + first);
    e->u.m = (unsigned char *)PAGE(SPARE_PAGE + first + TEXT_PAGES);
    e->u.size = (WIN_OFF - first - TEXT_PAGES) * 4096;
    e->u.open = e->u.lost = 0;
    e->u.group = G_NONE;
    u_clear(&e->u);
    e->cw = font_width(&e->ui.mono, "M");
    e->len = e->cur = e->top = e->left = 0;
    e->mark = -1;
    e->marking = e->drag = e->prompt = e->flen = e->last = 0;
    e->dirty = e->locked = 0;
    e->click_at = 0;
    e->click_x = e->click_y = 0;
    e->pasted = e->paste_short = 0;
    e->field[0] = 0;
    choose(e);
    long n = fs_read_all(&e->fs, e->path, e->text, TEXT_MAX);
    u64 size = 0, kind = 0;
    if (n >= 0) {
        e->len = n;
        set_status(e, "opened", 0);
    } else {
        kind = fs_stat(&e->fs, e->path, &size);
        e->locked = kind != 0;
        set_status(e, kind == FS_DIR ? "a folder: not opened" : kind ? "larger than 64 KiB: not opened" : "new file", 0);
    }
    put_s(&l, "edit: opened ");
    put_s(&l, e->path);
    put_s(&l, " (");
    if (kind == FS_DIR) put_s(&l, "a folder: not opened, never saved over)");
    else if (e->locked) {
        put_dec(&l, size);
        put_s(&l, " bytes, more than ");
        put_dec(&l, TEXT_MAX);
        put_s(&l, ": not opened, never saved over)");
    } else {
        put_dec(&l, (u64)e->len);
        put_s(&l, " bytes)");
    }
    say(&l);
    put_s(&l, "edit: a file may hold ");
    put_dec(&l, TEXT_MAX);
    put_s(&l, " bytes; undo has ");
    put_dec(&l, e->u.size);
    say(&l);
    draw(e);
    u64 opened = app_open_drag(WIN_OFF, EW, EH, "Editor");
    put_s(&l, "edit: opened a window");
    put_s(&l, outcome(opened));
    say(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        int pending = e->dirty && !e->locked;               /* a save to make, soon */
        struct event ev = pending ? app_poll(dirty) : app_wait(dirty);
        int x = (int)ev.a, y = (int)ev.b;
        dirty = 0;
        if (ev.kind == EV_CLOSE) {
            if (e->dirty) save(e, &l);
            put_s(&l, "edit: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (ev.kind == EV_NONE) {
            if (!pending || millis() < e->save_at) {
                sleep_ms(30);
                continue;
            }
            save(e, &l);
        } else if (ev.kind == EV_KEY) {
            key(e, &l, ev.a);
        } else if (ev.kind == EV_DOWN) {
            press(e, &l, x, y);
        } else if (ev.kind == EV_MOVE) {
            if (e->drag != 1) continue;
            e->cur = hit(e, x, y);
        } else if (ev.kind == EV_UP) {
            release(e, &l, x, y);
        } else if (ev.kind == EV_COPY) {
            copy(e, &l, ev.a == COPY_CUT);
        } else if (ev.kind == EV_PASTE) {
            if (!paste_in(e, &l, ev)) continue;              /* drawn once, when the last piece is in */
        } else continue;
        draw(e);
        dirty = 1;
    }
}
