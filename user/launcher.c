/* Apps: every program, with its icon. The built-in apps first (clicking one asks the display
   server to start it, as its dock icon would), then every program on the SD card: click one
   to start it in a free open slot; a dot marks those running. A card program NAME's icon is
   the file NAME.icon beside it (tools/mkicon.py), and rides along in the program's image, so
   the program can show it in its title bar and the dock; without one it gets a tile with its
   initial.

   The card's programs come ten to a page, two rows of five, as many pages as it takes (up to
   MAX_PROGS programs). With more than one page, the heading's line has the page, "2 / 3",
   between a previous and a next button; Page Up and Page Down turn the pages too. Pages, not
   scrolling, because of memory: the window's pixels take 158 pages of the spare run, and the
   icons get what is left before the file server's buffer, room for 11 icons of 48 px. So
   only the icons of the page shown are loaded, when it is shown (those still on it are kept).

   Type to find: what is typed with Apps in front (letters, digits, any printable key but
   the space) goes in the search field on the heading's line, and the grid shows only the
   programs whose names have it, in any case, those that start with it first. Backspace
   takes the last key off, Escape clears the field. The arrows move a selection through the grid (from one page to the
   next at its ends), Home and End to the first and the last; Return starts the one
   selected, which after typing is the first match.

   It is in the manifest, slot 16: a window, the file server (to read programs and icons),
   and the launch capabilities for the open slots. What a program it starts may do is fixed
   by the open slot, not by the launcher.

   It also opens what the user opens in Files (Return, or a double-click, on a file), which
   cannot start programs itself: the display passes it on, only right after the user's key
   or click in Files (user/app.h, OP_OPEN_WITH), as an event "@open", or as the name pending
   if Apps is not running. Apps asks the display for the program's name and the file's path
   (OP_PENDING), then starts the program as Terminal's `run PROG FILE` does: in a free open
   slot, given its own folder and that file, read-write (edit saves to it; Terminal gives
   files read-write too). Its window opens in front. A program that is open already gets a
   second copy, in another slot, with the file: a program is given its files as it starts,
   so the running copy cannot take one; two copies of edit on one file would each save their
   own text over it. A program's own file (Files asks with no path) is started as a click on
   it here starts it: brought forward if it is open.

   It also keeps the desktop's settings on the card for the display server, which cannot
   write the card: "@prefs" from the display (pending, or an event) saves the time zone and
   the background in settings.txt, and at boot ("@startup") it reads them back and gives
   them to the display (user/prefs.h). */
#include "app.h"
#include "fs.h"
#include "elfload.h"
#include "net.h"
#include "prefs.h"

#define AW 480
#define AH 336
#define CELL_W 88
#define CELL_H 84
#define COLS 5
#define ROWS 2
#define PER_PAGE (COLS * ROWS)
#define ICON 48
#define GRID_X 20
#define BUILTIN_Y 34
#define CARD_Y 170
#define MAX_PROGS 64
#define LAUNCH_OPEN 6
#define OPEN_FIRST 10
#define OPEN_SLOTS 6
/* the spare run: assets (fonts, built-in icons) first, then */
#define IMAGE_PAGE 24      /* a program's image, pages 24-39 */
#define WIN_OFFSET 40      /* the window's pixels, 158 pages */
#define ICONS_PAGE 198     /* the page's icons, 48 px, one after another up to page 224 */
#define ICON_BYTES (8 + ICON * ICON * 4)
#define ICON_SLOTS ((224 - ICONS_PAGE) * 4096 / ICON_BYTES)
_Static_assert(ICON_SLOTS >= PER_PAGE, "a page's icons must fit");
/* On the card heading's line: the search field, and the pager's buttons with the page
   between them. */
#define HEAD_Y (CARD_Y - 26)
#define FIND_X 150
#define FIND_W 170
#define FIND_H 22
#define FIND_MAX 16
#define PREV_X 346
#define NEXT_X 438
#define BTN 22
enum { F_UI = 1, F_TITLE = 2, F_SMALL = 3, F_LABEL = 4 };
/* What a click (or a key) is on: 0-4 a built-in app, the pager's buttons, CARD + k the k-th
   card program shown (counting from the first page), NONE nothing. */
enum { PREV = 5, NEXT = 6, CARD = 10, NONE = -1 };

#define NBUILTIN 5
static const char *const builtin_names[NBUILTIN] = {"Notes", "Files", "Terminal", "Settings", "Security"};

struct prog {
    char name[FS_NAME_MAX + 1];
    int has_icon;          /* NAME.icon is on the card (and was a good one, if loaded) */
    int icon;              /* icon slot + 1 while loaded, or 0 */
    int slot;              /* the open slot it was started in + 1, or 0 */
};

struct launcher {
    struct font ui, title, small, label;
    struct picture builtin[NBUILTIN];
    struct surface win;
    struct fs_client fs;
    struct net_client net;
    struct prog p[MAX_PROGS];
    int n;
    int holder[ICON_SLOTS];  /* which program's icon each slot holds: its index + 1, or 0 */
    char find[FIND_MAX + 1]; /* what was typed, and how many letters */
    int nfind;
    int shown[MAX_PROGS];  /* the programs the grid shows (those that match), in order */
    int nshown;
    int page;              /* the page shown, from 0 */
    int sel;               /* the one selected, an index into shown, or -1 */
    int pressed;           /* the cell drawn pressed, as hit() says, or NONE */
};

static unsigned *icon_at(int i) { return (unsigned *)((char *)PAGE(SPARE_PAGE + ICONS_PAGE) + i * ICON_BYTES); }

static int has_dot(const char *s) {
    for (; *s; s++) if (*s == '.') return 1;
    return 0;
}

/* An icon asset (w, h, premultiplied pixels) shrunk to ICON x ICON, each pixel the average
   of those it covers, stored the same way. */
static void shrink(unsigned *dst, const unsigned *src) {
    int w = (int)src[0], h = (int)src[1];
    const unsigned *px = src + 2;
    dst[0] = ICON;
    dst[1] = ICON;
    for (int j = 0; j < ICON; j++)
        for (int i = 0; i < ICON; i++) {
            int x0 = i * w / ICON, x1 = (i + 1) * w / ICON, y0 = j * h / ICON, y1 = (j + 1) * h / ICON;
            if (x1 <= x0) x1 = x0 + 1;
            if (y1 <= y0) y1 = y0 + 1;
            unsigned a = 0, r = 0, g = 0, b = 0, n = 0;
            for (int y = y0; y < y1; y++)
                for (int x = x0; x < x1; x++) {
                    unsigned v = px[y * w + x];
                    a += v >> 24; r += (v >> 16) & 255; g += (v >> 8) & 255; b += v & 255; n++;
                }
            dst[2 + j * ICON + i] = (a / n) << 24 | (r / n) << 16 | (g / n) << 8 | (b / n);
        }
}

static void icon_name(char *out, const char *name) {
    int m = 0;
    for (; name[m] && m < FS_NAME_MAX; m++) out[m] = name[m];
    const char *ext = ".icon";
    for (int x = 0; ext[x]; x++) out[m++] = ext[x];
    out[m] = 0;
}

/* Whether `file` is NAME.icon, program `name`'s icon. */
static int icon_of(const char *name, const char *file) {
    int k = 0;
    for (; name[k] && k < FS_NAME_MAX; k++)
        if (name[k] != file[k]) return 0;
    const char *ext = ".icon";
    for (int x = 0; x < 6; x++)
        if (file[k + x] != ext[x]) return 0;
    return 1;
}

/* The programs on the card: every file whose name has no dot (folders, such as apps/ and
   notes/, are not programs), in the card's order. Their icons are loaded when a page shows
   them (load_icons); here only whether each has one. The listing comes FS_LIST_MAX entries
   to a request, so a card with more files takes more than one. */
static void scan(struct launcher *st, struct line *l) {
    st->n = 0;
    for (int pass = 0; pass < 2; pass++) {    /* the programs, then their icons */
        u64 from = 0, total = 0;
        for (;;) {
            long got = fs_list_dir(&st->fs, "", from, &total);
            if (got <= 0) break;
            const struct fs_entry *e = fs_entries(&st->fs);
            for (long i = 0; i < got; i++) {
                if (e[i].kind == FS_DIR) continue;
                if (pass == 1) {
                    for (int k = 0; k < st->n; k++)
                        if (icon_of(st->p[k].name, e[i].name)) st->p[k].has_icon = 1;
                    continue;
                }
                if (has_dot(e[i].name) || st->n == MAX_PROGS) continue;
                struct prog *p = &st->p[st->n++];
                int k = 0;
                for (; e[i].name[k] && k < FS_NAME_MAX; k++) p->name[k] = e[i].name[k];
                p->name[k] = 0;
                p->has_icon = p->icon = p->slot = 0;
            }
            from += (u64)got;
            if (from >= total) break;
        }
    }
    int icons = 0;
    for (int k = 0; k < st->n; k++) icons += st->p[k].has_icon;
    put_s(l, "apps: ");
    put_dec(l, (u64)st->n);
    put_s(l, " programs, ");
    put_dec(l, (u64)icons);
    put_s(l, " with icons\n");
    flush(l);
}

/* Load the icons of the page shown that are not loaded yet, into the slots no program on
   the page holds. A program whose NAME.icon is not a good icon is drawn with its initial. */
static void load_icons(struct launcher *st) {
    int first = st->page * PER_PAGE, last = first + PER_PAGE < st->nshown ? first + PER_PAGE : st->nshown;
    int keep[ICON_SLOTS] = {0};
    for (int k = first; k < last; k++) {
        struct prog *p = &st->p[st->shown[k]];
        if (p->icon) keep[p->icon - 1] = 1;
    }
    for (int s = 0; s < ICON_SLOTS; s++)
        if (!keep[s] && st->holder[s]) {
            st->p[st->holder[s] - 1].icon = 0;
            st->holder[s] = 0;
        }
    for (int k = first; k < last; k++) {
        struct prog *p = &st->p[st->shown[k]];
        if (p->icon || !p->has_icon) continue;
        int s = 0;
        while (s < ICON_SLOTS && st->holder[s]) s++;
        if (s == ICON_SLOTS) return;          /* never: a page has fewer cells than slots */
        char iconname[FS_NAME_MAX + 6];
        icon_name(iconname, p->name);
        long size = fs_read(&st->fs, iconname);
        const unsigned *d = (const unsigned *)fs_data(&st->fs);
        if (size > 8 && d[0] > 0 && d[1] > 0 && d[0] <= 64 && d[1] <= 64 && (long)(8 + d[0] * d[1] * 4) <= size) {
            shrink(icon_at(s), d);
            p->icon = s + 1;
            st->holder[s] = st->shown[k] + 1;
        } else {
            p->has_icon = 0;
        }
    }
}

static char lower(char c) { return c >= 'A' && c <= 'Z' ? (char)(c + 32) : c; }

/* Where what was typed is in `name` (in any case): 0 at its start, 1 later, -1 nowhere. */
static int found_at(const char *name, const char *find, int n) {
    for (int at = 0; name[at]; at++) {
        int j = 0;
        while (j < n && name[at + j] && lower(name[at + j]) == lower(find[j])) j++;
        if (j == n) return at > 0;
    }
    return n ? -1 : 0;
}

/* The programs the grid shows: every one, or those that match what was typed, those whose
   names start with it first. The first page, with the first match selected (none selected
   with nothing typed). */
static void refilter(struct launcher *st) {
    st->nshown = 0;
    for (int where = 0; where < 2; where++)
        for (int i = 0; i < st->n; i++)
            if (found_at(st->p[i].name, st->find, st->nfind) == where) st->shown[st->nshown++] = i;
    st->page = 0;
    st->sel = st->nfind && st->nshown ? 0 : -1;
}

static int pages(struct launcher *st) { return st->nshown ? (st->nshown + PER_PAGE - 1) / PER_PAGE : 1; }

static int running(struct prog *p) {
    return p->slot && sys1(SYS_BOOTINFO, (u64)(p->slot - 1)).x[4] == 1;
}

static void cell(struct launcher *st, int x, int y, const struct picture *pic, const char *name, int dot, int pressed,
                 int selected) {
    struct surface *s = &st->win;
    static const unsigned tints[6] = {0x3a6ee6, 0x2eaa6e, 0xe0873a, 0x9b59d0, 0xd8465a, 0x2a9dc0};
    if (selected) {
        round_rect(s, x + 4, y, CELL_W - 8, CELL_H - 4, 12, rgb(58, 110, 230), 255);
        round_rect(s, x + 6, y + 2, CELL_W - 12, CELL_H - 8, 10, pressed ? rgb(222, 228, 244) : rgb(236, 241, 252), 255);
    } else if (pressed) {
        round_rect(s, x + 4, y, CELL_W - 8, CELL_H - 4, 12, rgb(222, 228, 244), 255);
    }
    int ix = x + CELL_W / 2 - ICON / 2, iy = y + 6;
    if (pic && pic->px) icon(s, ix, iy, pic);
    else {
        round_rect(s, ix + 2, iy + 2, ICON - 4, ICON - 4, 12, tints[(unsigned char)name[0] % 6], 255);
        char ch[2] = {name[0] >= 'a' && name[0] <= 'z' ? (char)(name[0] - 32) : name[0], 0};
        font_text(s, &st->title, ix + ICON / 2 - font_width(&st->title, ch) / 2, iy + ICON / 2 + 7, ch,
                  rgb(255, 255, 255));
    }
    char label[FS_NAME_MAX + 1];
    int k = 0;
    for (; name[k] && k < FS_NAME_MAX; k++) label[k] = name[k];
    label[k] = 0;
    if (label[0] >= 'a' && label[0] <= 'z') label[0] = (char)(label[0] - 32);
    int w = font_width(&st->ui, label);
    font_text(s, &st->ui, x + CELL_W / 2 - w / 2, y + ICON + 24, label, rgb(40, 40, 50));
    if (dot) round_rect(s, x + CELL_W / 2 - 3, y + ICON + 31, 6, 6, 3, rgb(58, 110, 230), 255);
}

/* A round button with a chevron pointing left (dir -1) or right (1), gray when there is no
   page that way. Coordinates of the chevron in 1/16 pixel, as thick_line takes them. */
static void pager_button(struct surface *s, int x, int dir, int can) {
    round_rect(s, x, HEAD_Y, BTN, BTN, BTN / 2, rgb(232, 233, 238), 255);
    unsigned c = can ? rgb(60, 62, 74) : rgb(190, 192, 202);
    int cx = (x + BTN / 2) * 16 - dir * 16, cy = (HEAD_Y + BTN / 2) * 16;
    thick_line(s, cx - dir * 40, cy - 72, cx + dir * 40, cy, 2, c);
    thick_line(s, cx + dir * 40, cy, cx - dir * 40, cy + 72, 2, c);
}

/* The heading's line: the search field (a magnifier and what was typed, or what to do), and
   with more than one page, the pager. */
static void draw_heading(struct launcher *st) {
    struct surface *s = &st->win;
    if (st->nfind) {
        round_rect(s, FIND_X, HEAD_Y, FIND_W, FIND_H, FIND_H / 2, rgb(58, 110, 230), 255);
        round_rect(s, FIND_X + 2, HEAD_Y + 2, FIND_W - 4, FIND_H - 4, FIND_H / 2 - 2, rgb(255, 255, 255), 255);
    } else {
        round_rect(s, FIND_X, HEAD_Y, FIND_W, FIND_H, FIND_H / 2, rgb(232, 233, 238), 255);
    }
    unsigned gray = rgb(130, 130, 145);
    ring(s, FIND_X + 13, HEAD_Y + 10, 4, 2, gray);
    thick_line(s, (FIND_X + 16) * 16, (HEAD_Y + 13) * 16, (FIND_X + 19) * 16, (HEAD_Y + 16) * 16, 2, gray);
    int tx = FIND_X + 26, ty = HEAD_Y + 16;
    if (st->nfind) {
        font_text(s, &st->ui, tx, ty, st->find, rgb(40, 40, 50));
        fill(s, tx + font_width(&st->ui, st->find) + 1, HEAD_Y + 5, 1, FIND_H - 10, rgb(58, 110, 230));
    } else {
        font_text(s, &st->ui, tx, ty, "Type to find", gray);
    }
    int np = pages(st);
    if (np < 2) return;
    pager_button(s, PREV_X, -1, st->page > 0);
    pager_button(s, NEXT_X, 1, st->page + 1 < np);
    struct line t = {.n = 0};
    put_dec(&t, (u64)(st->page + 1));
    put_s(&t, " / ");
    put_dec(&t, (u64)np);
    t.b[t.n] = 0;
    int mid = (PREV_X + BTN + NEXT_X) / 2;
    font_text(s, &st->ui, mid - font_width(&st->ui, t.b) / 2, ty, t.b, rgb(90, 92, 106));
}

static void draw(struct launcher *st) {
    struct surface *s = &st->win;
    fill(s, 0, 0, AW, AH, rgb(247, 247, 250));
    font_text(s, &st->label, GRID_X, 24, "BUILT IN", rgb(140, 144, 158));
    /* On the built-in heading's line: the card heading's has the search field. */
    const char *hint = "card programs get their own memory and a window, nothing else";
    font_text(s, &st->small, AW - GRID_X - font_width(&st->small, hint), 24, hint, rgb(130, 130, 145));
    for (int i = 0; i < NBUILTIN; i++)
        cell(st, GRID_X + i * CELL_W, BUILTIN_Y, &st->builtin[i], builtin_names[i], 0, st->pressed == i, 0);
    fill(s, GRID_X, CARD_Y - 34, AW - 2 * GRID_X, 1, rgb(226, 228, 236));
    font_text(s, &st->label, GRID_X, CARD_Y - 10, "ON THE SD CARD", rgb(140, 144, 158));
    draw_heading(st);
    load_icons(st);
    int first = st->page * PER_PAGE;
    for (int k = first; k < first + PER_PAGE && k < st->nshown; k++) {
        struct prog *p = &st->p[st->shown[k]];
        struct picture pic = {0, 0, 0};
        if (p->icon) {
            const unsigned *raw = icon_at(p->icon - 1);
            pic.w = (int)raw[0];
            pic.h = (int)raw[1];
            pic.px = raw + 2;
        }
        cell(st, GRID_X + (k - first) % COLS * CELL_W, CARD_Y + (k - first) / COLS * CELL_H, p->icon ? &pic : 0,
             p->name, running(p), st->pressed == CARD + k, st->sel == k);
    }
    if (st->n == 0) font_text(s, &st->ui, GRID_X, CARD_Y + 30, "No programs on the SD card.", rgb(120, 120, 130));
    else if (st->nshown == 0) font_text(s, &st->ui, GRID_X, CARD_Y + 30, "No program on the card has that name.",
                                        rgb(120, 120, 130));
}

/* Read the program (and its icon), make its image, and start it in a free open slot, given
   the file `file` too if it is not "" (then even if the program is open already). */
static void start(struct launcher *st, struct line *l, int i, const char *file) {
    struct prog *p = &st->p[i];
    const char *why = 0;
    if (file[0] && fs_stat(&st->fs, file, 0) != FS_FILE) {
        put_s(l, "apps: ");
        put_s(l, file);
        put_s(l, " is not a file on the card\n");
        flush(l);
        return;
    }
    if (!file[0] && app_raise(p->name)) {
        put_s(l, "apps: ");
        put_s(l, p->name);
        put_s(l, " is already open\n");
        flush(l);
        return;
    }
    unsigned char *image = (unsigned char *)PAGE(SPARE_PAGE + IMAGE_PAGE);
    u64 len = 0;
    why = elf_load(&st->fs, p->name, image, &len);
    if (!why) {
        char iconname[FS_NAME_MAX + 6];
        icon_name(iconname, p->name);
        long isize = fs_read(&st->fs, iconname);
        image_add_icon(image, &len, (const unsigned char *)fs_data(&st->fs), isize > 0 ? (u64)isize : 0, p->name);
        why = "no free slot: close a program first";
        for (int k = 0; k < OPEN_SLOTS; k++) {
            if (sys1(SYS_BOOTINFO, OPEN_FIRST + (u64)k).x[4] == 1) continue;
            /* its own folder on the card, apps/NAME, and nothing else */
            char folder[FS_PATH_MAX + 1] = "apps/";
            for (int i = 0; p->name[i] && i < FS_NAME_MAX; i++) { folder[5 + i] = p->name[i]; folder[6 + i] = 0; }
            fs_unshare(&st->fs, OPEN_FIRST + (u64)k);
            fs_share(&st->fs, folder, OPEN_FIRST + (u64)k, FS_R | FS_W, 1);
            /* the file opened in Files, read-write, as `run PROG FILE` gives it */
            if (file[0]) {
                u64 given = fs_share(&st->fs, file, OPEN_FIRST + (u64)k, FS_R | FS_W, 0);
                put_s(l, "apps: gave ");
                put_s(l, p->name);
                put_s(l, " ");
                put_s(l, file);
                put_s(l, given == FS_OK ? " -> ok\n" : " -> refused\n");
                flush(l);
            }
            app_before_start();
            if (sys(SYS_EXEC, LAUNCH_OPEN + (u64)k, (u64)image, len, 0, 0).status != OK) continue;
            /* the network: only for the browser (what ran in this slot before loses it) */
            int wants = p->name[0] == 'w' && p->name[1] == 'e' && p->name[2] == 'b' && !p->name[3];
            net_call(&st->net, NET_ALLOW, OPEN_FIRST + (u64)k | (u64)wants << 8, 0);
            p->slot = OPEN_FIRST + k + 1;
            why = 0;
            break;
        }
    }
    put_s(l, "apps: ");
    put_s(l, p->name);
    if (why) {
        put_s(l, ": ");
        put_s(l, why);
    } else {
        put_s(l, " started in slot ");
        put_dec(l, (u64)(p->slot - 1));
        if (file[0]) {
            put_s(l, " with ");
            put_s(l, file);
        }
    }
    put_s(l, "\n");
    flush(l);
}

/* Start the card program called `name`, if the card has it, given `file` ("": none). */
static void start_named(struct launcher *st, struct line *l, const char *name, const char *file) {
    for (int i = 0; i < st->n; i++) {
        int j = 0;
        while (j < 15 && name[j] && name[j] == st->p[i].name[j]) j++;
        if (name[j] == st->p[i].name[j]) {
            start(st, l, i, file);
            return;
        }
    }
    put_s(l, "apps: ");
    put_s(l, name);
    put_s(l, " is not on the SD card\n");
    flush(l);
}

/* A name of up to 15 bytes, from two message words. */
static void name_of_words(char out[17], u64 a, u64 b) {
    for (int i = 0; i < 16; i++) out[i] = (char)((i < 8 ? a : b) >> (8 * (i % 8)));
    out[15] = out[16] = 0;
}

/* The path of the file Files asked to open, from the display, 16 bytes a request (user/app.h,
   OP_OPEN_WITH): into path, "" if it sends none. */
static void take_path(char path[FS_PATH_MAX + 1]) {
    int n = 0;
    for (u64 part = 1; n < FS_PATH_MAX && part <= (FS_PATH_MAX + 16) / 16; part++) {
        struct res r = sys(SYS_CALL, ENDPOINT, OP_PENDING, part, 0, 0);
        if (r.status != OK) break;
        int i = 0;
        for (char c; i < 16 && (c = (char)((i < 8 ? r.x[2] : r.x[3]) >> (8 * (i % 8)))) && n < FS_PATH_MAX; i++)
            path[n++] = c;
        if (i < 16) break;
    }
    path[n] = 0;
}

/* The display has something Files asked to open (EV_LAUNCH "@open"): ask what, and open it. */
static void open_asked(struct launcher *st, struct line *l) {
    struct res pend = sys(SYS_CALL, ENDPOINT, OP_PENDING, 0, 0, 0);
    char name[17], path[FS_PATH_MAX + 1];
    name_of_words(name, pend.status == OK ? pend.x[2] : 0, pend.status == OK ? pend.x[3] : 0);
    path[0] = 0;
    if (pend.status == OK && pend.x[1] == 1) take_path(path);
    if (name[0]) start_named(st, l, name, path);
}

/* The display's time zone and background, saved on the card as text (user/prefs.h). An
   older card's timezone.txt goes once settings.txt holds the zone. */
static void save_prefs(struct launcher *st, struct line *l) {
    long zone = app_zone();
    int bg = (int)app_background();
    struct line p = {.n = 0};
    put_prefs(&p, zone, bg);
    u64 ok = fs_write(&st->fs, PREFS_FILE, p.b, p.n);
    put_s(l, "apps: saved the time zone, ");
    put_zone(l, zone);
    put_s(l, ", and the background, ");
    put_s(l, bg_name((u64)bg));
    put_s(l, ", in " PREFS_FILE);
    put_s(l, ok == FS_OK ? " -> ok\n" : " -> refused\n");
    flush(l);
    if (ok == FS_OK && fs_delete(&st->fs, ZONE_FILE) == FS_OK) {
        put_s(l, "apps: removed " ZONE_FILE ": " PREFS_FILE " holds the time zone now\n");
        flush(l);
    }
}

/* At boot: give the display the time zone and the background saved on the card (or UTC and
   the first background, if none are), which it takes from Apps only this once. A card with
   no settings.txt may have an older timezone.txt, with the zone alone. */
static void restore_prefs(struct launcher *st, struct line *l) {
    long zone = 0, n = fs_read(&st->fs, PREFS_FILE);
    int bg = 0, got = 0, old = n < 0, want = old ? 1 : 3;
    if (old) n = fs_read(&st->fs, ZONE_FILE);
    if (n > 0) got = old ? parse_zone(fs_data(&st->fs), n, &zone) : parse_prefs(fs_data(&st->fs), n, &zone, &bg);
    struct res rz = sys(SYS_CALL, ENDPOINT, OP_SET, SET_ZONE, (u64)(zone + ZONE_BIAS), 0);
    struct res rb = sys(SYS_CALL, ENDPOINT, OP_SET, SET_BACKGROUND, (u64)bg, 0);
    if (n < 0) return;                            /* none saved: the display keeps its own */
    put_s(l, "apps: time zone ");
    if (got & 1) put_zone(l, zone);
    else put_s(l, "not understood");
    if (!old) {
        put_s(l, ", background ");
        put_s(l, got & 2 ? bg_name((u64)bg) : "not understood");
    }
    put_s(l, old ? ", from " ZONE_FILE : ", from " PREFS_FILE);
    int ok = got == want && rz.status == OK && rz.x[1] == 0 && rb.status == OK && rb.x[1] == 0;
    put_s(l, outcome(ok ? OK : BAD_ARG));
    put_s(l, "\n");
    flush(l);
}

/* What is at (x, y): a built-in app, a pager button, a card program shown, or NONE. */
static int hit(struct launcher *st, int x, int y) {
    if (pages(st) > 1 && y >= HEAD_Y - 4 && y < HEAD_Y + BTN + 4) {
        if (x >= PREV_X - 4 && x < PREV_X + BTN + 4) return PREV;
        if (x >= NEXT_X - 4 && x < NEXT_X + BTN + 4) return NEXT;
    }
    if (x < GRID_X) return NONE;
    int col = (x - GRID_X) / CELL_W;
    if (col >= COLS) return NONE;
    if (y >= BUILTIN_Y && y < BUILTIN_Y + CELL_H) return col < NBUILTIN ? col : NONE;
    if (y >= CARD_Y && y < CARD_Y + ROWS * CELL_H) {
        int k = st->page * PER_PAGE + (y - CARD_Y) / CELL_H * COLS + col;
        return k < st->nshown ? CARD + k : NONE;
    }
    return NONE;
}

/* The program selected (an index into p), or -1. */
static int selected(struct launcher *st) { return st->sel >= 0 ? st->shown[st->sel] : -1; }

/* Say what a key or a click changed: what the grid shows, the page, the program selected
   (the arguments: what they were before, the program as selected() said). */
static void tell(struct launcher *st, struct line *l, int nshown, int nfind, int page, int sel) {
    if (st->nfind != nfind || st->nshown != nshown) {
        put_s(l, "apps: ");
        if (st->nfind) {
            put_s(l, "find \"");
            put_s(l, st->find);
            put_s(l, "\": ");
            put_dec(l, (u64)st->nshown);
            put_s(l, " of ");
        } else {
            put_s(l, "find cleared: ");
        }
        put_dec(l, (u64)st->n);
        put_s(l, " programs\n");
        flush(l);
    }
    if (st->page != page) {
        put_s(l, "apps: page ");
        put_dec(l, (u64)(st->page + 1));
        put_s(l, " of ");
        put_dec(l, (u64)pages(st));
        put_s(l, "\n");
        flush(l);
    }
    if (selected(st) != sel && st->sel >= 0) {
        put_s(l, "apps: selected ");
        put_s(l, st->p[selected(st)].name);
        put_s(l, "\n");
        flush(l);
    }
}

/* A key: what it types in the search field, or how it moves the selection or the page.
   Returns the program to start (an index into shown), or -1. */
static int key(struct launcher *st, u64 k) {
    int last = st->nshown - 1, np = pages(st);
    if (k > ' ' && k < 127) {
        if (st->nfind < FIND_MAX) {
            st->find[st->nfind++] = (char)k;
            st->find[st->nfind] = 0;
            refilter(st);
        }
    } else if (k == 127 || k == 8) {
        if (st->nfind) {
            st->find[--st->nfind] = 0;
            refilter(st);
        }
    } else if (k == 27) {
        st->nfind = 0;
        st->find[0] = 0;
        refilter(st);
    } else if (k == '\r' || k == '\n') {
        return st->sel;
    } else if (k == KEY_PGUP || k == KEY_PGDN) {
        int to = st->page + (k == KEY_PGDN ? 1 : -1);
        if (to < 0 || to >= np) return -1;
        if (st->sel >= 0) {
            st->sel += (to - st->page) * PER_PAGE;
            if (st->sel > last) st->sel = last;
        }
        st->page = to;
    } else if (last >= 0 && k >= KEY_UP && k <= KEY_END) {
        int sel = st->sel;
        if (sel < 0) sel = st->page * PER_PAGE;     /* the first key selects the page's first */
        else if (k == KEY_LEFT && sel > 0) sel--;
        else if (k == KEY_RIGHT && sel < last) sel++;
        else if (k == KEY_UP && sel >= COLS) sel -= COLS;
        else if (k == KEY_DOWN && sel / COLS < last / COLS) sel = sel + COLS < last ? sel + COLS : last;
        else if (k == KEY_HOME) sel = 0;
        else if (k == KEY_END) sel = last;
        st->sel = sel;
        st->page = sel / PER_PAGE;
    }
    return -1;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct launcher *st = (struct launcher *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->title = font_of(assets, F_TITLE);
    st->small = font_of(assets, F_SMALL);
    st->label = font_of(assets, F_LABEL);
    for (int i = 0; i < NBUILTIN; i++) st->builtin[i] = picture_of(assets, ASSET_ICON, 10 + (unsigned)i);
    st->win = app_surface_at(WIN_OFFSET, AW, AH);
    fs_init(&st->fs, SPARE_PAGE);
    net_init(&st->net, SPARE_PAGE);
    st->pressed = NONE;
    st->nfind = 0;
    st->find[0] = 0;
    for (int i = 0; i < ICON_SLOTS; i++) st->holder[i] = 0;
    /* Started by a click on a program pinned in the dock? Then start that, and nothing else.
       Started by the display server at boot ("@startup")? Then give it the saved time zone
       and background, and open what startup.txt on the card lists: program names, and
       "apps" for this window (# starts a comment). Started to save those ("@prefs")? Then
       only that. */
    struct res pend = sys(SYS_CALL, ENDPOINT, OP_PENDING, 0, 0, 0);
    char startup[512], asked[17], file[FS_PATH_MAX + 1];
    int nstartup = 0, show = 1;
    for (int i = 0; i < 16; i++) asked[i] = pend.status == OK ? (char)(pend.x[2 + i / 8] >> (8 * (i % 8))) : 0;
    asked[16] = 0;
    file[0] = 0;
    if (pend.status == OK && pend.x[1] == 1) take_path(file);   /* a file Files asked to open */
    if (asked[0] == '@' && asked[1] == 'p') {    /* "@prefs" */
        save_prefs(st, &l);
        exit_task();
    }
    if (asked[0] == '@') restore_prefs(st, &l); /* "@startup": first, so the menu bar has them */
    scan(st, &l);
    refilter(st);
    if (asked[0]) {
        if (asked[0] != '@') {
            start_named(st, &l, asked, file);
            exit_task();
        }
        long n = fs_read(&st->fs, "startup.txt");
        if (n <= 0) exit_task();                 /* nothing to open at startup */
        const char *d = fs_data(&st->fs);
        for (long i = 0; i < n && i < (long)sizeof startup - 1; i++) startup[nstartup++] = d[i];
        startup[nstartup] = 0;
        show = 0;
        for (int i = 0; i + 3 < nstartup; i++)
            if ((i == 0 || startup[i - 1] <= ' ') && startup[i] == 'a' && startup[i + 1] == 'p' &&
                startup[i + 2] == 'p' && startup[i + 3] == 's' && (i + 4 == nstartup || startup[i + 4] <= ' '))
                show = 1;
        put_s(&l, "apps: opening what startup.txt lists\n");
        flush(&l);
    }
    u64 opened = BAD_ARG;
    if (show) {
        draw(st);
        opened = app_open_at(WIN_OFFSET, AW, AH, "Apps");
        put_s(&l, "apps: opened a window");
        put_s(&l, outcome(opened));
        put_s(&l, "\n");
        flush(&l);
    }
    /* the startup programs, after this window, so the last one listed ends up in front */
    for (int i = 0; i < nstartup;) {
        while (i < nstartup && startup[i] <= ' ') i++;
        if (startup[i] == '#') { while (i < nstartup && startup[i] != '\n') i++; continue; }
        char name[FS_NAME_MAX + 1];
        int k = 0;
        while (i < nstartup && startup[i] > ' ' && k < FS_NAME_MAX) name[k++] = startup[i++];
        while (i < nstartup && startup[i] > ' ') i++;
        name[k] = 0;
        if (k && !(k == 4 && name[0] == 'a' && name[1] == 'p' && name[2] == 'p' && name[3] == 's')) start_named(st, &l, name, "");
    }
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind == EV_LAUNCH) {          /* from the dock: up to 8 bytes of a name */
            char name[9];
            for (int i = 0; i < 8; i++) name[i] = (char)((i < 4 ? e.a : e.b) >> (8 * (i % 4)));
            name[8] = 0;
            if (name[0] == '@' && name[1] == 'p' && name[2] == 'r' && name[3] == 'e' && name[4] == 'f' &&
                name[5] == 's' && !name[6])
                save_prefs(st, &l);
            else if (name[0] == '@' && name[1] == 'o' && name[2] == 'p' && name[3] == 'e' && name[4] == 'n' && !name[5])
                open_asked(st, &l);                /* from Files, through the display */
            else start_named(st, &l, name, "");
            continue;
        }
        int nshown = st->nshown, nfind = st->nfind, page = st->page, sel = selected(st), c = NONE;
        if (e.kind == EV_KEY) {
            int k = key(st, e.a);
            if (k >= 0) c = CARD + k;
            tell(st, &l, nshown, nfind, page, sel);
        } else if (e.kind == EV_DOWN) {
            c = hit(st, (int)e.a, (int)e.b);
        }
        if (c == PREV || c == NEXT) {                /* as Page Up and Page Down */
            key(st, c == NEXT ? KEY_PGDN : KEY_PGUP);
            tell(st, &l, nshown, nfind, page, sel);
            c = NONE;
        }
        if (c == NONE) {
            if (st->nfind != nfind || st->page != page || selected(st) != sel) {
                draw(st);
                dirty = 1;
            }
            continue;
        }
        st->pressed = c;
        draw(st);
        if (c < NBUILTIN) {
            put_s(&l, "apps: asked the display server to start ");
            put_s(&l, builtin_names[c]);
            put_s(&l, "\n");
            flush(&l);
            sys(SYS_CALL, ENDPOINT, OP_START, (u64)c, 0, 0);
        } else {
            start(st, &l, st->shown[c - CARD], "");
        }
        st->pressed = NONE;
        draw(st);
        dirty = 1;
    }
}
