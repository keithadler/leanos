/* paint: a paint program, from the SD card. It edits the picture it was given (`run paint
   picture.bmp` in Terminal gives it picture.bmp), or, given none, apps/paint/untitled.bmp in
   its own folder, which it opens if it is there; the file server lets it reach nothing else.

   A tool bar at the top, the picture in the middle, the colors and a status line at the
   bottom. Drag to draw (the display gives a window that asks for it, app_open_drag, every
   move of a drag and its release). A click on a color makes it the first color, the one
   the tools draw with; a right click makes it the second, which starts white; X, or a click
   on the two squares beside the colors, swaps them. Drag with the right button (the same
   window hears it: EV_RDOWN, the moves, EV_RUP) and every tool works with the second color
   instead: the pencil, the brush, lines and shapes draw in it, the fill fills with it, the
   eraser paints it (the left button's eraser paints white), and the picker takes the color
   under the pointer as the second color.

   The tools, with their keys:
     P  pencil             one pixel
     B  brush              round, three sizes
     E  eraser             square, three sizes: paints white
     L  line               straight, from the press to the release
     R  rectangle          Shift+R filled
     O  ellipse            in the box from the press to the release; Shift+O filled
     F  fill               the area of one color the click is in, 4-connected
     I  color picker       takes the color under the pointer, as the first color (the
                           right button: as the second)
     1 2 3                 the size of the brush and the eraser, and of lines and outlines
     X                     swaps the two colors
     Delete or Backspace   clears the picture to white
     Ctrl+Z  undo          Ctrl+Y  redo      Ctrl+S  save now
   Lines, rectangles and ellipses show as you drag, and are drawn when you let go. The same
   buttons are in the tool bar, and the status line names the tool and its key.

   It saves by itself a second after the last change (Ctrl+S saves at once), and when its
   window closes; the status line says whether what you see is saved. A picture is a
   standard 24-bit uncompressed BMP: a 14-byte BITMAPFILEHEADER, a 40-byte BITMAPINFOHEADER,
   then the rows bottom-up, each padded to 4 bytes, no palette; any image program on a Mac or
   a PC opens it. It opens the same (and 32-bit ones, and top-down ones), up to 416 x 208. A
   file that is not one it can open is not opened and never saved over. A save writes
   apps/paint/save.part~ in pieces (a request moves at most 16 KiB) and then renames it over
   the picture, which the file server does in one journaled step: after a power cut the
   picture is the last save or the one before, never half of each.

   Memory. A program has 16 pages of code, 8 of data, 4 of stack and a spare run of 228
   pages (user/app.h). The spare run holds, in order:
     pages   0-35   the fonts every card program gets (141 KiB today; where they end is read
                    from the blob, so more fonts would shrink the undo memory, not break it)
     pages  36-106  undo: 71 pages, 290,816 bytes
     pages 107-223  the window: 416 x 288 pixels of 4 bytes, 479,232 bytes, 117 pages. The
                    picture lives there and nowhere else: 416 x 208, under the tool bar
     pages 224-227  the file server's buffer (fs.h)
   The data pages hold the rest (struct paint, 20 KiB of 32): which tiles the change being
   made has kept, a 2048-entry stack for the fill and a bit a pixel of what it filled.

   Undo keeps, for each change, what the 16 x 16 tiles it touched looked like before: a tile
   is kept the first time the change touches it, packed as runs of one color when that is
   shorter (a tile of one color takes 12 bytes with its header), else as its 768 bytes.
   Taking a change back swaps those tiles with the picture's, so the same record, turned
   around, is the redo. Undo records grow from the start of the undo pages, redo records
   from the end; when a change needs room, the oldest undo record goes, then the redo
   farthest away. A change touches at most the 338 tiles of the picture, at most 262,304
   bytes even when nothing packs, and the undo pages hold more than that (while the fonts
   take at most 42 pages): at least one change can always be taken back, and as many more as
   fit, typically hundreds (a stroke on white paper keeps a few hundred bytes). */
#include "../ui.h"
#include "../fs.h"

#define WW 416                 /* the window */
#define WH 288
#define BAR_H 36               /* the tool bar, at the top */
#define FOOT_H 44              /* the colors and the status line, at the bottom */
#define CY BAR_H               /* the canvas: between them, the window's whole width */
#define CW WW
#define CH (WH - BAR_H - FOOT_H)
#define FY (CY + CH)           /* where the colors begin */
#define TILE 16
#define TX (CW / TILE)         /* tiles across: 26 */
#define NTILES (TX * (CH / TILE))
#define WIN_PAGES ((WW * WH * 4 + 4095) / 4096)
#define WIN_OFF (FS_BUF_OFFSET - WIN_PAGES)   /* the window's pixels end where the file buffer begins */
#define ENTRY_MAX (8 + TILE * TILE * 3)       /* an undo entry: a header, a tile's bytes, a trailer */
#define UNDO_NEED ((u64)NTILES * ENTRY_MAX + 16)
#define FILL_STACK 2048
#define SAVE_AFTER 1000        /* ms after the last change */
#define SAVE_AGAIN 10000       /* ms after a save that failed (the card is full, say) */
#define PAPER 0xffffff
#define TMP "apps/paint/save.part~"

_Static_assert(CW % TILE == 0 && CH % TILE == 0, "the canvas is whole tiles");

enum { T_PENCIL, T_BRUSH, T_ERASER, T_LINE, T_RECT, T_RECT_FILL, T_OVAL, T_OVAL_FILL, T_FILL, T_PICK, NTOOL,
       T_CLEAR = NTOOL };
static const char *const tool_name[NTOOL + 1] = {"pencil", "brush", "eraser", "line", "rectangle",
                                                 "filled rectangle", "ellipse", "filled ellipse", "fill",
                                                 "color picker", "clear"};
static const char *const tool_key[NTOOL] = {"P", "B", "E", "L", "R", "Shift+R", "O", "Shift+O", "F", "I"};
static const char tool_char[NTOOL] = {'p', 'b', 'e', 'l', 'r', 'R', 'o', 'O', 'f', 'i'};
static const int brush_r[3] = {1, 3, 6};     /* the brush's radius at each size */
static const int eraser_r[3] = {3, 6, 10};   /* the eraser's half width */
static const int thick[3] = {1, 3, 5};       /* lines and outlines */

/* Windows Paint's colors: black, grays, white, then the hues. */
static const unsigned palette[16] = {0x000000, 0x7f7f7f, 0xc3c3c3, 0xffffff, 0xed1c24, 0x880015, 0xff7f27, 0xfff200,
                                     0x22b14c, 0xb5e61d, 0x00a2e8, 0x99d9ea, 0x3f48cc, 0xa349a4, 0xb97a57, 0xffaec9};

/* The tool bar's buttons: the tools, the three sizes, then undo, redo and clear. */
#define NBUTTON (NTOOL + 6)
#define B_SIZE NTOOL
#define B_UNDO (NTOOL + 3)
#define B_REDO (NTOOL + 4)
#define B_CLEAR (NTOOL + 5)
#define BUTTON_Y 7
#define BUTTON_H 23

/* Undo's memory (see the top). Each entry: a header word, its bytes padded to 4, and the
   header again, so a stack can be walked from either end. A header is a tile's number (bits
   0-11), how many bytes (12-23) and whether they are runs (bit 24); a record begins (undo)
   or ends (redo) with a mark, MARK and the tool, 8 bytes with nothing between. */
#define MARK 0xffffff00u
struct undo {
    unsigned char *m;
    u64 size, ut, rt;          /* undo records in [0, ut), redo records in [rt, size) */
    int nundo, nredo;          /* the whole records in each */
    u64 op;                    /* where the mark of the record being made is */
    int open, lost;            /* a record is being made; it did not fit, and is dropped */
};

struct paint {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    char path[FS_PATH_MAX + 1];
    int w, h;                  /* the picture, at the canvas's top left */
    int tool, size;
    unsigned color[2];         /* the first color and the second */
    int down;                  /* a drag on the picture is going on */
    int which;                 /* the color it draws with: 0 the first, 1 the second */
    int op;                    /* what it does (a tool) */
    int ax, ay, lx, ly;        /* where it began, and the last point drawn */
    int pen_r, pen_square;     /* the stamp strokes and lines are drawn with */
    unsigned ink;
    int dirty;                 /* changed since the last save */
    u64 save_at;               /* when to save it (ms) */
    int locked;                /* the file is not a picture it can open: never saved over */
    char note[72];             /* the status line's first line, when it has something to say */
    struct undo u;
    unsigned char kept[(NTILES + 7) / 8];   /* the tiles the record being made holds */
    unsigned char comp[TILE * TILE * 3];    /* a tile, packed */
    unsigned stack[FILL_STACK];             /* the fill's spans to look at: x | y << 16 */
    unsigned char filled[CW * CH / 8];      /* what the fill has filled, a bit a pixel */
};
_Static_assert(sizeof(struct paint) <= 8 * 4096, "paint's state must fit in its 8 data pages");

static void say(struct line *l) { put_s(l, "\n"); flush(l); }

static void put_color(struct line *l, unsigned c) {
    for (int i = 20; i >= 0; i -= 4) {
        char d[2] = {"0123456789abcdef"[c >> i & 15], 0};
        put_s(l, d);
    }
}

static void note(struct paint *p, const char *a, const char *b) {
    int n = 0;
    for (int i = 0; a[i] && n < 71; i++) p->note[n++] = a[i];
    for (int i = 0; b && b[i] && n < 71; i++) p->note[n++] = b[i];
    p->note[n] = 0;
}

static unsigned *pix(struct paint *p, int x, int y) { return p->win.px + (CY + y) * WW + x; }

static u64 isqrt64(u64 v) {
    u64 r = 0, bit = 1UL << 62;
    while (bit > v) bit >>= 2;
    while (bit) {
        if (v >= r + bit) { v -= r + bit; r = (r >> 1) + bit; } else r >>= 1;
        bit >>= 2;
    }
    return r;
}

/* ---- undo's memory ---- */

static int is_mark(unsigned h) { return (h & MARK) == MARK; }
static u64 esize(unsigned h) { return is_mark(h) ? 8 : 8 + (((h >> 12 & 0xfff) + 3) & ~3u); }
static unsigned *word(struct undo *u, u64 at) { return (unsigned *)(u->m + at); }

static void put_entry(struct undo *u, u64 at, unsigned h, const unsigned char *data) {
    u64 n = esize(h), len = h >> 12 & 0xfff;
    *word(u, at) = h;
    for (u64 i = 0; i + 8 < n; i++) u->m[at + 4 + i] = i < len ? data[i] : 0;
    *word(u, at + n - 4) = h;
}
static void push_undo(struct undo *u, unsigned h, const unsigned char *data) {
    put_entry(u, u->ut, h, data);
    u->ut += esize(h);
}
static void push_redo(struct undo *u, unsigned h, const unsigned char *data) {
    u->rt -= esize(h);
    put_entry(u, u->rt, h, data);
}

/* Drop the oldest undo record, unless it is the only one (the one being made, or taken
   back): 1 if it did. */
static int drop_oldest(struct undo *u) {
    if (!u->ut) return 0;
    u64 at = 8;
    while (at < u->ut && !is_mark(*word(u, at))) at += esize(*word(u, at));
    if (at >= u->ut) return 0;
    for (u64 i = at; i < u->ut; i += 4) *word(u, i - at) = *word(u, i);
    u->ut -= at;
    if (u->open) u->op -= at;
    u->nundo--;
    return 1;
}

/* Drop the redo record farthest from the next redo, unless it is the only one: 1 if it did. */
static int drop_farthest(struct undo *u) {
    if (u->rt >= u->size) return 0;
    u64 at = u->size - 8;
    while (at > u->rt && !is_mark(*word(u, at - 4))) at -= esize(*word(u, at - 4));
    if (at <= u->rt) return 0;
    u64 n = u->size - at;
    for (u64 i = at; i > u->rt;) {
        i -= 4;
        *word(u, i + n) = *word(u, i);
    }
    u->rt += n;
    u->nredo--;
    return 1;
}

/* Room for `need` more bytes between the two stacks, made by dropping the oldest records. */
static int room(struct undo *u, u64 need) {
    while (u->rt - u->ut < need)
        if (!drop_oldest(u) && !drop_farthest(u)) return 0;
    return 1;
}

/* ---- tiles ---- */

static void tile_box(struct paint *p, int t, int *x, int *y, int *w, int *h) {
    *x = t % TX * TILE;
    *y = t / TX * TILE;
    *w = p->w - *x < TILE ? p->w - *x : TILE;
    *h = p->h - *y < TILE ? p->h - *y : TILE;
}

/* Tile t's pixels (its part inside the picture), packed into `out`: runs of one color (the
   count less one, then blue, green and red), or, if that is no shorter, its bytes as they
   are (blue, green, red). Returns the entry's header. */
static unsigned pack(struct paint *p, int t, unsigned char *out) {
    int x0, y0, w, h;
    tile_box(p, t, &x0, &y0, &w, &h);
    int raw = w * h * 3, n = 0, run = 0;
    unsigned last = 0;
    for (int j = 0; j < h; j++)
        for (int i = 0; i <= w; i++) {
            int end = j == h - 1 && i == w;
            if (i == w && !end) continue;
            unsigned c = end ? 0 : *pix(p, x0 + i, y0 + j) & 0xffffff;
            if (!end && run && c == last && run < 256) { run++; continue; }
            if (run) {
                if (n + 4 >= raw) goto plain;
                out[n++] = (unsigned char)(run - 1);
                out[n++] = (unsigned char)last;
                out[n++] = (unsigned char)(last >> 8);
                out[n++] = (unsigned char)(last >> 16);
            }
            last = c;
            run = 1;
        }
    return (unsigned)t | (unsigned)n << 12 | 1u << 24;
plain:
    n = 0;
    for (int j = 0; j < h; j++)
        for (int i = 0; i < w; i++) {
            unsigned c = *pix(p, x0 + i, y0 + j);
            out[n++] = (unsigned char)c;
            out[n++] = (unsigned char)(c >> 8);
            out[n++] = (unsigned char)(c >> 16);
        }
    return (unsigned)t | (unsigned)n << 12;
}

/* The entry's tile, back into the picture. */
static void unpack(struct paint *p, unsigned h, const unsigned char *in) {
    int x0, y0, w, hh, k = 0, left = 0;
    tile_box(p, (int)(h & 0xfff), &x0, &y0, &w, &hh);
    unsigned c = 0;
    for (int j = 0; j < hh; j++)
        for (int i = 0; i < w; i++) {
            if (!left) {
                left = h >> 24 & 1 ? in[k++] + 1 : 1;
                c = in[k] | (unsigned)in[k + 1] << 8 | (unsigned)in[k + 2] << 16;
                k += 3;
            }
            *pix(p, x0 + i, y0 + j) = c;
            left--;
        }
}

/* The change being made: begun, a tile kept before it is first touched, ended. */
static void begin(struct paint *p, int tool) {
    struct undo *u = &p->u;
    u->rt = u->size;                    /* a new change: what was taken back is gone */
    u->nredo = 0;
    for (int i = 0; i < (int)sizeof p->kept; i++) p->kept[i] = 0;
    u->open = 1;
    u->lost = !room(u, 8);
    u->op = u->ut;
    if (!u->lost) push_undo(u, MARK | (unsigned)tool, 0);
    p->op = tool;
}

static void keep(struct paint *p, int t) {
    struct undo *u = &p->u;
    if (p->kept[t >> 3] >> (t & 7) & 1) return;
    p->kept[t >> 3] |= (unsigned char)(1 << (t & 7));
    if (!u->open || u->lost) return;
    unsigned h = pack(p, t, p->comp);
    if (!room(u, esize(h))) {           /* only if the undo pages are too few: see the top */
        u->ut = u->op;
        u->lost = 1;
        return;
    }
    push_undo(u, h, p->comp);
}

/* Put back what the change being made has drawn so far (a shape's last outline). */
static void unwind(struct paint *p) {
    struct undo *u = &p->u;
    if (!u->open || u->lost) return;
    for (u64 at = u->op + 8; at < u->ut; at += esize(*word(u, at))) unpack(p, *word(u, at), u->m + at + 4);
}

static void put_steps(struct paint *p, struct line *l) {
    put_dec(l, (u64)p->u.nundo);
    put_s(l, p->u.nundo == 1 ? " step to undo, " : " steps to undo, ");
    put_dec(l, (u64)p->u.nredo);
    put_s(l, " to redo (");
    put_dec(l, p->u.ut + (p->u.size - p->u.rt));
    put_s(l, " of ");
    put_dec(l, p->u.size);
    put_s(l, " bytes)");
}

static void mark_changed(struct paint *p) {
    p->dirty = 1;
    p->save_at = millis() + SAVE_AFTER;
    p->note[0] = 0;
}

/* The change is done: say what it was. */
static void finish(struct paint *p, struct line *l) {
    struct undo *u = &p->u;
    int tiles = 0;
    for (int t = 0; t < NTILES; t++) tiles += p->kept[t >> 3] >> (t & 7) & 1;
    p->down = 0;
    u->open = 0;
    if (!tiles) {                       /* it drew nothing */
        if (!u->lost) u->ut = u->op;
        return;
    }
    if (!u->lost) u->nundo++;
    mark_changed(p);
    put_s(l, "paint: ");
    put_s(l, tool_name[p->op]);
    put_s(l, ", ");
    put_dec(l, (u64)tiles);
    put_s(l, tiles == 1 ? " tile changed; " : " tiles changed; ");
    if (u->lost) put_s(l, "too large to undo; ");
    put_steps(p, l);
    say(l);
}

/* Take back the newest change (undo), or do again the last taken back (redo): each of its
   tiles swapped with the picture's, into a record on the other stack. */
static void undo_redo(struct paint *p, struct line *l, int redo) {
    struct undo *u = &p->u;
    if (redo ? !u->nredo : !u->nundo) {
        note(p, redo ? "Nothing to redo" : "Nothing to undo", 0);
        return;
    }
    u64 at = redo ? u->rt : u->ut;      /* the record's mark: which tool it was */
    if (redo) while (!is_mark(*word(u, at))) at += esize(*word(u, at));
    else while (!is_mark(*word(u, at - 4))) at -= esize(*word(u, at - 4));
    unsigned mark = redo ? *word(u, at) : *word(u, at - 4);
    int other = room(u, 8);             /* the swapped record is kept, while it fits */
    if (other && redo) {
        u->open = 1;
        u->op = u->ut;
        push_undo(u, mark, 0);
    } else if (other) {
        push_redo(u, mark, 0);
    }
    for (;;) {
        unsigned h = redo ? *word(u, u->rt) : *word(u, u->ut - 4);
        if (is_mark(h)) break;
        u64 n = esize(h), e = redo ? u->rt : u->ut - n;
        unsigned now = pack(p, (int)(h & 0xfff), p->comp);
        unpack(p, h, u->m + e + 4);
        if (redo) u->rt += n;
        else u->ut = e;
        if (other && !room(u, esize(now))) {
            other = 0;                  /* only if the undo pages are too few */
            if (redo) u->ut = u->op;
            else { u->rt = u->size; u->nredo = 0; }
        }
        if (other && redo) push_undo(u, now, p->comp);
        else if (other) push_redo(u, now, p->comp);
    }
    u->open = 0;
    if (redo) {
        u->rt += 8;
        u->nredo--;
        u->nundo += other;
    } else {
        u->ut -= 8;
        u->nundo--;
        u->nredo += other;
    }
    mark_changed(p);
    put_s(l, redo ? "paint: redid the " : "paint: undid the ");
    put_s(l, tool_name[mark & 0xff]);
    put_s(l, "; ");
    put_steps(p, l);
    say(l);
}

/* ---- drawing on the picture ---- */

/* Row y from x0 to x1 in color c, clipped to the picture; each tile it touches kept first. */
static void span(struct paint *p, int y, int x0, int x1, unsigned c) {
    if (y < 0 || y >= p->h) return;
    if (x0 < 0) x0 = 0;
    if (x1 >= p->w) x1 = p->w - 1;
    if (x0 > x1) return;
    for (int t = x0 / TILE; t <= x1 / TILE; t++) keep(p, y / TILE * TX + t);
    unsigned *row = pix(p, 0, y);
    for (int x = x0; x <= x1; x++) row[x] = c;
}

/* The pen, at (x, y): a disc of radius pen_r (0: one pixel), or a square. */
static void stamp(struct paint *p, int x, int y) {
    int r = p->pen_r;
    for (int dy = -r; dy <= r; dy++) {
        int hw = p->pen_square ? r : (int)isqrt((unsigned)(r * r - dy * dy + r));
        span(p, y + dy, x - hw, x + hw, p->ink);
    }
}

/* The pen along the line from (x0, y0) to (x1, y1) (Bresenham's). */
static void segment(struct paint *p, int x0, int y0, int x1, int y1) {
    int dx = x1 > x0 ? x1 - x0 : x0 - x1, dy = y1 > y0 ? y0 - y1 : y1 - y0;
    int sx = x0 < x1 ? 1 : -1, sy = y0 < y1 ? 1 : -1, err = dx + dy;
    for (;;) {
        stamp(p, x0, y0);
        if (x0 == x1 && y0 == y1) return;
        int e2 = 2 * err;
        if (e2 >= dy) { err += dy; x0 += sx; }
        if (e2 <= dx) { err += dx; y0 += sy; }
    }
}

/* Row y's part of the ellipse that fills the box from (x0, y0) to (x1, y1), in *l..*r: 0
   if the row misses it. In half pixels from the center: a pixel is in if its center is. */
static int oval_row(int x0, int y0, int x1, int y1, int y, int *l, int *r) {
    if (y < y0 || y > y1) return 0;
    long a = x1 - x0 + 1, b = y1 - y0 + 1, dy = 2L * y - y0 - y1, cx = (long)x0 + x1 + 1;
    long hw = (long)isqrt64((u64)(a * a) * (u64)(b * b - dy * dy) / (u64)(b * b));
    if (hw < 1) hw = 1;                 /* the tips: at least the middle pixel */
    *l = (int)((cx - hw) >> 1);
    *r = (int)((cx + hw - 1) >> 1);
    return 1;
}

static void order(int *a, int *b) {
    if (*a > *b) { int t = *a; *a = *b; *b = t; }
}

/* A rectangle or an ellipse in the box from (x0, y0) to (x1, y1): filled, or an outline
   `t` pixels wide. */
static void shape(struct paint *p, int x0, int y0, int x1, int y1, int oval, int filled, int t, unsigned c) {
    order(&x0, &x1);
    order(&y0, &y1);
    int ya = y0 < 0 ? 0 : y0, yb = y1 >= p->h ? p->h - 1 : y1;
    if (x1 - x0 + 1 <= 2 * t || y1 - y0 + 1 <= 2 * t) filled = 1;   /* no room inside */
    for (int y = ya; y <= yb; y++) {
        int l = x0, r = x1, il = 0, ir = -1;        /* the row, and the part of it not drawn */
        if (oval) {
            int ul, ur, dl, dr;
            oval_row(x0, y0, x1, y1, y, &l, &r);
            if (filled) {
            } else if (t == 1) {        /* the pixels with a neighbor outside */
                if (oval_row(x0, y0, x1, y1, y - 1, &ul, &ur) && oval_row(x0, y0, x1, y1, y + 1, &dl, &dr)) {
                    il = l + 1 > ul ? l + 1 : ul;
                    il = il > dl ? il : dl;
                    ir = r - 1 < ur ? r - 1 : ur;
                    ir = ir < dr ? ir : dr;
                }
            } else if (!oval_row(x0 + t, y0 + t, x1 - t, y1 - t, y, &il, &ir)) {
                ir = il - 1;
            }
        } else if (!filled && y >= y0 + t && y <= y1 - t) {
            il = x0 + t;
            ir = x1 - t;
        }
        if (il > ir) span(p, y, l, r, c);
        else {
            span(p, y, l, il - 1, c);
            span(p, y, ir + 1, r, c);
        }
    }
}

static int filled_at(struct paint *p, int x, int y) { return p->filled[(y * CW + x) >> 3] >> ((y * CW + x) & 7) & 1; }

/* Fill the area of one color that (x, y) is in (4-connected) with c: a span at a time, the
   spans above and below it to look at next on a stack. If the stack is ever full, what did
   not fit is found again afterwards: a pixel of the old color beside one filled. */
static void flood(struct paint *p, int x, int y, unsigned c) {
    unsigned was = *pix(p, x, y) & 0xffffff;
    c &= 0xffffff;
    if (was == c) return;
    for (int i = 0; i < (int)sizeof p->filled; i++) p->filled[i] = 0;
    int n = 0, full = 0;
    p->stack[n++] = (unsigned)x | (unsigned)y << 16;
    for (;;) {
        while (n) {
            unsigned s = p->stack[--n];
            int sx = (int)(s & 0xffff), sy = (int)(s >> 16), l = sx, r = sx;
            if ((*pix(p, sx, sy) & 0xffffff) != was) continue;
            while (l > 0 && (*pix(p, l - 1, sy) & 0xffffff) == was) l--;
            while (r < p->w - 1 && (*pix(p, r + 1, sy) & 0xffffff) == was) r++;
            span(p, sy, l, r, c);
            for (int i = l; i <= r; i++) p->filled[(sy * CW + i) >> 3] |= (unsigned char)(1 << ((sy * CW + i) & 7));
            for (int ny = sy - 1; ny <= sy + 1; ny += 2) {
                if (ny < 0 || ny >= p->h) continue;
                for (int i = l; i <= r; i++) {
                    if ((*pix(p, i, ny) & 0xffffff) != was || (i > l && (*pix(p, i - 1, ny) & 0xffffff) == was)) continue;
                    if (n < FILL_STACK) p->stack[n++] = (unsigned)i | (unsigned)ny << 16;
                    else full = 1;
                }
            }
        }
        if (!full) return;
        full = 0;
        for (int j = 0; j < p->h && !full; j++)
            for (int i = 0; i < p->w; i++) {
                if ((*pix(p, i, j) & 0xffffff) != was) continue;
                if ((i > 0 && filled_at(p, i - 1, j)) || (i < p->w - 1 && filled_at(p, i + 1, j)) ||
                    (j > 0 && filled_at(p, i, j - 1)) || (j < p->h - 1 && filled_at(p, i, j + 1))) {
                    if (n < FILL_STACK) p->stack[n++] = (unsigned)i | (unsigned)j << 16;
                    else { full = 1; break; }
                }
            }
        if (!n) return;
    }
}

/* ---- the window ---- */

static int button_x(int k) {
    return k < NTOOL ? 6 + 25 * k : k < B_UNDO ? 262 + 20 * (k - B_SIZE) : 328 + 25 * (k - B_UNDO);
}
static int button_w(int k) { return k >= B_SIZE && k < B_UNDO ? 18 : 23; }

static int button_at(int x, int y) {
    if (y < BUTTON_Y || y >= BUTTON_Y + BUTTON_H) return -1;
    for (int k = 0; k < NBUTTON; k++)
        if (x >= button_x(k) && x < button_x(k) + button_w(k)) return k;
    return -1;
}

static void line16(struct surface *s, int x0, int y0, int x1, int y1, int w, unsigned c) {
    thick_line(s, x0 * 16, y0 * 16, x1 * 16, y1 * 16, w, c);
}

/* Button k's picture, centered at (cx, cy). */
static void glyph(struct surface *s, int k, int cx, int cy, unsigned c, unsigned back) {
    switch (k) {
    case T_PENCIL:
        line16(s, cx - 5, cy + 5, cx + 4, cy - 4, 3, c);
        fill(s, cx - 6, cy + 5, 2, 2, c);
        break;
    case T_BRUSH:
        line16(s, cx + 5, cy - 6, cx, cy - 1, 2, c);
        round_rect(s, cx - 6, cy - 2, 8, 8, 4, c, 255);
        break;
    case T_ERASER:
        round_rect(s, cx - 7, cy - 4, 14, 9, 2, c, 255);
        round_rect(s, cx - 6, cy - 3, 6, 7, 1, back, 255);
        break;
    case T_LINE:
        line16(s, cx - 6, cy + 6, cx + 6, cy - 6, 2, c);
        break;
    case T_RECT:
    case T_RECT_FILL:
        fill(s, cx - 7, cy - 5, 14, 11, c);
        if (k == T_RECT) fill(s, cx - 5, cy - 3, 10, 7, back);
        break;
    case T_OVAL:
        ring(s, cx, cy, 6, 2, c);
        break;
    case T_OVAL_FILL:
        round_rect(s, cx - 7, cy - 7, 15, 15, 7, c, 255);
        break;
    case T_FILL:                        /* a drop */
        round_rect(s, cx - 5, cy - 2, 11, 10, 5, c, 255);
        for (int i = 0; i < 7; i++) fill(s, cx - i * 5 / 7, cy - 8 + i, i * 10 / 7 + 1, 1, c);
        break;
    case T_PICK:
        line16(s, cx - 6, cy + 6, cx + 2, cy - 2, 2, c);
        round_rect(s, cx, cy - 7, 7, 7, 3, c, 255);
        break;
    case B_UNDO:
    case B_REDO: {
        int d = k == B_UNDO ? -1 : 1;
        line16(s, cx - 6 * d, cy, cx + 6 * d, cy, 2, c);
        line16(s, cx + 6 * d, cy, cx + 2 * d, cy - 4, 2, c);
        line16(s, cx + 6 * d, cy, cx + 2 * d, cy + 4, 2, c);
        break;
    }
    case B_CLEAR:
        fill(s, cx - 6, cy - 7, 12, 15, c);
        fill(s, cx - 5, cy - 6, 10, 13, back);
        line16(s, cx - 3, cy - 3, cx + 3, cy + 3, 2, c);
        line16(s, cx - 3, cy + 3, cx + 3, cy - 3, 2, c);
        break;
    default: {                          /* a size: a dot as large */
        int r = k == B_SIZE ? 1 : k == B_SIZE + 1 ? 3 : 5;
        round_rect(s, cx - r, cy - r, 2 * r + 1, 2 * r + 1, r, c, 255);
    }
    }
}

static void draw_bar(struct paint *p) {
    struct surface *s = &p->win;
    fill(s, 0, 0, WW, BAR_H, rgb(236, 237, 241));
    fill(s, 0, BAR_H - 1, WW, 1, rgb(210, 212, 218));
    for (int k = 0; k < NBUTTON; k++) {
        int x = button_x(k), w = button_w(k);
        int on = k == p->tool || k == B_SIZE + p->size;
        int off = (k == B_UNDO && !p->u.nundo) || (k == B_REDO && !p->u.nredo);
        unsigned back = on ? rgb(58, 110, 230) : rgb(252, 252, 253);
        round_rect(s, x, BUTTON_Y, w, BUTTON_H, 5, on ? back : rgb(214, 216, 222), 255);
        round_rect(s, x + 1, BUTTON_Y + 1, w - 2, BUTTON_H - 2, 4, back, 255);
        glyph(s, k, x + w / 2, BUTTON_Y + BUTTON_H / 2, on ? rgb(255, 255, 255) : off ? rgb(190, 192, 200)
                                                                                      : rgb(52, 54, 64), back);
    }
}

/* The two colors, the palette, and the status line: the file, whether it is saved, the tool. */
static void draw_foot(struct paint *p) {
    struct surface *s = &p->win;
    fill(s, 0, FY, WW, FOOT_H, rgb(236, 237, 241));
    fill(s, 0, FY, WW, 1, rgb(210, 212, 218));
    fill(s, 19, FY + 16, 22, 22, rgb(90, 92, 100));
    fill(s, 20, FY + 17, 20, 20, p->color[1]);
    fill(s, 7, FY + 6, 22, 22, rgb(90, 92, 100));
    fill(s, 8, FY + 7, 20, 20, p->color[0]);
    for (int i = 0; i < 16; i++) {
        int x = 50 + 18 * (i % 8), y = FY + 6 + 18 * (i / 8);
        int on = palette[i] == p->color[0];
        fill(s, x, y, 16, 16, on ? rgb(30, 32, 40) : rgb(160, 162, 170));
        fill(s, x + 1 + on, y + 1 + on, 14 - 2 * on, 14 - 2 * on, palette[i]);
    }
    const char *name = p->path;
    for (const char *q = p->path; *q; q++) if (*q == '/') name = q + 1;
    char top[96], hint[96];
    int n = 0;
    for (int i = 0; name[i] && n < 40; i++) top[n++] = name[i];
    const char *state = p->note[0] ? p->note : p->locked ? "not opened" : p->dirty ? "edited" : "saved";
    top[n++] = ':';
    top[n++] = ' ';
    for (int i = 0; state[i] && n < 94; i++) top[n++] = state[i];
    top[n] = 0;
    n = 0;
    const char *t = tool_name[p->tool], *k = tool_key[p->tool];
    for (int i = 0; t[i] && n < 40; i++) hint[n++] = i ? t[i] : (char)(t[i] - 32);
    hint[n++] = ' ';
    hint[n++] = '(';
    for (int i = 0; k[i]; i++) hint[n++] = k[i];
    hint[n++] = ')';
    if (p->tool == T_BRUSH || p->tool == T_ERASER || p->tool == T_LINE || p->tool == T_RECT || p->tool == T_OVAL) {
        const char *z = ", size ";
        for (int i = 0; z[i]; i++) hint[n++] = z[i];
        hint[n++] = (char)('1' + p->size);
    }
    hint[n] = 0;
    clip_to(s, 206, FY, WW - 212, FOOT_H);
    font_text(s, &p->ui.small_bold, 206, FY + 18, top, p->locked || p->note[0] ? rgb(190, 60, 50) : rgb(60, 62, 74));
    font_text(s, &p->ui.small, 206, FY + 35, hint, rgb(110, 112, 124));
    clip_all(s);
}

/* The canvas past the picture's edges, when it is smaller. */
static void draw_margin(struct paint *p) {
    fill(&p->win, p->w, CY, CW - p->w, CH, rgb(186, 189, 196));
    fill(&p->win, 0, CY + p->h, p->w, CH - p->h, rgb(186, 189, 196));
}

/* ---- the file ---- */

static void le(unsigned char *b, int at, u64 v, int n) {
    for (int i = 0; i < n; i++) b[at + i] = (unsigned char)(v >> (8 * i));
}
static unsigned rd(const char *b, int at, int n) {
    unsigned v = 0;
    for (int i = 0; i < n; i++) v |= (unsigned)(unsigned char)b[at + i] << (8 * i);
    return v;
}

/* Save the picture: a BMP into TMP a piece at a time, then renamed over the picture in one
   step. */
static void save(struct paint *p, struct line *l) {
    if (p->locked) return;
    struct fs_client *c = &p->fs;
    unsigned char *d = (unsigned char *)c->buf + FS_DATA_OFF;
    u64 stride = ((u64)p->w * 3 + 3) & ~3UL, size = 54 + stride * (u64)p->h, at = 0, n = 54, st = FS_OK, t0 = millis();
    for (int i = 0; i < 54; i++) d[i] = 0;
    d[0] = 'B';
    d[1] = 'M';
    le(d, 2, size, 4);
    le(d, 10, 54, 4);                   /* where the pixels begin */
    le(d, 14, 40, 4);                   /* BITMAPINFOHEADER */
    le(d, 18, (u64)p->w, 4);
    le(d, 22, (u64)p->h, 4);            /* positive: bottom-up */
    le(d, 26, 1, 2);                    /* planes */
    le(d, 28, 24, 2);                   /* bits a pixel; 0 at 30: no compression */
    le(d, 34, stride * (u64)p->h, 4);
    le(d, 38, 2835, 4);                 /* 72 dots an inch, as pixels a meter */
    le(d, 42, 2835, 4);
    for (int r = 0; r <= p->h && st == FS_OK; r++) {
        if (r == p->h || n + stride > FS_CHUNK) {            /* a piece */
            fs_path(c, TMP);
            fs_offset(c, at);
            st = fs_call(c, at ? FS_WRITE_AT : FS_WRITE, n).x[1];
            at += n;
            n = 0;
        }
        if (r == p->h) break;
        const unsigned *row = pix(p, 0, p->h - 1 - r);
        for (int x = 0; x < p->w; x++) {
            d[n++] = (unsigned char)row[x];
            d[n++] = (unsigned char)(row[x] >> 8);
            d[n++] = (unsigned char)(row[x] >> 16);
        }
        for (u64 k = (u64)p->w * 3; k < stride; k++) d[n++] = 0;     /* the row's padding */
    }
    if (st == FS_OK) st = fs_rename(c, TMP, p->path);
    if (st != FS_OK) fs_delete(c, TMP);
    if (st == FS_OK) p->dirty = 0;
    else p->save_at = millis() + SAVE_AGAIN;
    note(p, st == FS_OK ? "" : st == FS_FULL ? "not saved, the card is full" : st == FS_DENIED ? "not saved, not given to paint"
                                                                                               : "not saved", 0);
    put_s(l, "paint: saved ");
    put_s(l, p->path);
    put_s(l, " (");
    put_dec(l, (u64)p->w);
    put_s(l, "x");
    put_dec(l, (u64)p->h);
    put_s(l, ", ");
    put_dec(l, size);
    put_s(l, " bytes) in ");
    put_dec(l, millis() - t0);
    put_s(l, st == FS_OK ? " ms -> ok" : " ms -> refused");
    say(l);
}

/* A blank picture, the canvas's size. */
static void blank(struct paint *p) {
    p->w = CW;
    p->h = CH;
    for (int y = 0; y < CH; y++) for (int x = 0; x < CW; x++) *pix(p, x, y) = PAPER;
}

/* Open the picture at p->path: a BMP of 24 or 32 bits a pixel, uncompressed, bottom-up or
   top-down, no larger than the canvas. Returns why not, or 0; a missing file is a new
   picture. */
static const char *open_file(struct paint *p) {
    struct fs_client *c = &p->fs;
    u64 size = 0;
    blank(p);
    u64 kind = fs_stat(c, p->path, &size);
    if (!kind) return 0;
    if (kind != FS_FILE) return "a folder";
    long got = fs_read_at(c, p->path, 0, &size);
    const char *b = fs_data(c);
    if (got < 54 || b[0] != 'B' || b[1] != 'M') return "not a BMP";
    unsigned off = rd(b, 10, 4), hsize = rd(b, 14, 4), bpp = rd(b, 28, 2), comp = rd(b, 30, 4);
    int w = (int)rd(b, 18, 4), h = (int)rd(b, 22, 4), down = h < 0;
    if (down) h = -h;
    if (hsize < 40 || rd(b, 26, 2) != 1 || (bpp != 24 && bpp != 32) || comp != 0)
        return "not a 24-bit BMP (compressed, or with a palette)";
    if (w < 1 || h < 1 || w > CW || h > CH) return "larger than 416 x 208";
    u64 stride = ((u64)w * bpp / 8 + 3) & ~3UL;
    if (off < 14 + hsize || off + stride * (u64)h > size) return "shorter than its header says";
    p->w = w;
    p->h = h;
    u64 per = FS_CHUNK / stride;        /* rows a read */
    for (u64 r0 = 0; r0 < (u64)h; r0 += per) {
        u64 rows = (u64)h - r0 < per ? (u64)h - r0 : per;
        got = fs_read_at(c, p->path, off + r0 * stride, 0);
        if (got < (long)(rows * stride)) return "shorter than its header says";
        for (u64 r = 0; r < rows; r++) {
            const unsigned char *q = (const unsigned char *)b + r * stride;
            int y = down ? (int)(r0 + r) : h - 1 - (int)(r0 + r);
            for (int x = 0; x < w; x++, q += bpp / 8) *pix(p, x, y) = rgb(q[2], q[1], q[0]);
        }
    }
    return 0;
}

/* The file it was given: the first file among its grants that is not in its own folder,
   else untitled.bmp in its folder (as edit chooses). */
static void choose(struct paint *p) {
    char list[2048];
    long n = fs_grants(&p->fs);
    const char *g = fs_data(&p->fs);
    for (int k = 0; k < (int)sizeof list; k++) list[k] = g[k];     /* the buffer is about to be reused */
    const char *q = list;
    for (long i = 0; i < n && q < list + sizeof list - 1; i++) {
        const char *path = q + 1;                                  /* after the rights byte */
        int len = 0;
        while (path[len]) len++;
        int own = len >= 5 && path[0] == 'a' && path[1] == 'p' && path[2] == 'p' && path[3] == 's' && path[4] == '/';
        if (!own && fs_stat(&p->fs, path, 0) != FS_DIR) {
            for (int k = 0; k <= len; k++) p->path[k] = path[k];
            return;
        }
        q = path + len + 1;
    }
    const char *d = "apps/paint/untitled.bmp";
    int k = 0;
    for (; d[k]; k++) p->path[k] = d[k];
    p->path[k] = 0;
}

/* ---- input ---- */

static void set_tool(struct paint *p, struct line *l, int tool) {
    p->tool = tool;
    put_s(l, "paint: tool ");
    put_s(l, tool_name[tool]);
    say(l);
}

static void set_color(struct paint *p, struct line *l, int which, unsigned c) {
    p->color[which] = c & 0xffffff;
    put_s(l, which ? "paint: second color " : "paint: first color ");
    put_color(l, p->color[which]);
    say(l);
}

static void clear(struct paint *p, struct line *l) {
    begin(p, T_CLEAR);
    for (int y = 0; y < p->h; y++) span(p, y, 0, p->w - 1, PAPER);
    finish(p, l);
}

/* The pen for the drag being begun: its size and color. */
static void pen(struct paint *p) {
    int t = p->tool;
    p->pen_square = t == T_ERASER;
    p->pen_r = t == T_PENCIL ? 0 : t == T_BRUSH ? brush_r[p->size] : t == T_ERASER ? eraser_r[p->size]
             : (thick[p->size] - 1) / 2;
    p->ink = t == T_ERASER && !p->which ? PAPER : p->color[p->which];
}

/* The drag, now at (x, y) on the canvas. */
static void drag(struct paint *p, int x, int y) {
    int t = p->op;
    if (t == T_PICK) {
        if (x >= 0 && y >= 0 && x < p->w && y < p->h) p->color[p->which] = *pix(p, x, y) & 0xffffff;
    } else if (t <= T_ERASER) {
        segment(p, p->lx, p->ly, x, y);
    } else if (t == T_LINE) {
        unwind(p);
        segment(p, p->ax, p->ay, x, y);
    } else if (t >= T_RECT && t <= T_OVAL_FILL) {
        unwind(p);
        shape(p, p->ax, p->ay, x, y, t >= T_OVAL, t == T_RECT_FILL || t == T_OVAL_FILL, thick[p->size], p->ink);
    }
    p->lx = x;
    p->ly = y;
}

static void release(struct paint *p, struct line *l) {
    if (p->op == T_PICK) {
        p->down = 0;
        set_color(p, l, p->which, p->color[p->which]);
        return;
    }
    finish(p, l);
}

/* A press at (x, y), with the left button (which 0) or the right (1): what it draws with. */
static void press(struct paint *p, struct line *l, int x, int y, int which) {
    if (p->down) release(p, l);         /* a release the display never sent (the window went) */
    if (y < CY) {
        int k = which ? -1 : button_at(x, y);         /* the tool bar: the left button only */
        if (k < 0) return;
        if (k < NTOOL) set_tool(p, l, k);
        else if (k < B_UNDO) p->size = k - B_SIZE;
        else if (k == B_CLEAR) clear(p, l);
        else undo_redo(p, l, k == B_REDO);
        return;
    }
    if (y >= FY) {
        int px = x - 50, py = y - FY - 6;
        if (px >= 0 && px < 8 * 18 && py >= 0 && py < 2 * 18 && px % 18 < 16 && py % 18 < 16)
            set_color(p, l, which, palette[py / 18 * 8 + px / 18]);
        else if (x >= 7 && x < 41 && y >= FY + 6 && y < FY + 38) {
            unsigned c = p->color[0];   /* the two squares: swapped */
            p->color[0] = p->color[1];
            p->color[1] = c;
        }
        return;
    }
    y -= CY;
    if (x >= p->w || y >= p->h) return;
    p->down = 1;
    p->which = which;
    p->ax = p->lx = x;
    p->ay = p->ly = y;
    pen(p);
    if (p->tool == T_PICK) {
        p->op = T_PICK;
        drag(p, x, y);
        return;
    }
    begin(p, p->tool);
    if (p->tool == T_FILL) {
        flood(p, x, y, p->color[p->which]);
        finish(p, l);
    } else if (p->tool <= T_ERASER) {
        stamp(p, x, y);
    } else {
        drag(p, x, y);
    }
}

static void key(struct paint *p, struct line *l, u64 k) {
    if (p->down) release(p, l);
    if (k == 26 || k == 25) undo_redo(p, l, k == 25);           /* Ctrl+Z, Ctrl+Y */
    else if (k == 19) save(p, l);                               /* Ctrl+S */
    else if (k == 127 || k == 8 || k == KEY_DELETE) clear(p, l);
    else if (k >= '1' && k <= '3') p->size = (int)(k - '1');
    else if (k == 'x' || k == 'X') {
        unsigned c = p->color[0];
        p->color[0] = p->color[1];
        p->color[1] = c;
    } else {
        for (int t = 0; t < NTOOL; t++)
            if ((u64)(unsigned char)tool_char[t] == k || ((u64)(unsigned char)tool_char[t] == k + 32 && t != T_RECT && t != T_OVAL))
                set_tool(p, l, t);
    }
}

/* Where the fonts end in the spare run: the first page after the last asset. */
static u64 assets_end(const unsigned char *blob) {
    const unsigned *h = (const unsigned *)blob;
    u64 end = 0;
    for (unsigned i = 0; h[0] == 0x53414e4c && i < h[2]; i++) {
        const unsigned *e = h + 3 + 4 * i;
        if (e[2] + e[3] > end) end = e[2] + e[3];
    }
    return (end + 4095) / 4096;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct paint *p = (struct paint *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    ui_load(&p->ui, assets);
    p->win = app_surface_at(WIN_OFF, WW, WH);
    fs_init(&p->fs, SPARE_PAGE);
    u64 first = assets_end(assets);
    p->u.m = (unsigned char *)PAGE(SPARE_PAGE + first);
    p->u.size = first < WIN_OFF ? (WIN_OFF - first) * 4096 : 0;
    p->u.ut = p->u.nundo = p->u.nredo = p->u.open = p->u.lost = 0;
    p->u.rt = p->u.size;
    p->tool = T_PENCIL;
    p->size = 1;
    p->color[0] = 0x000000;
    p->color[1] = PAPER;
    p->down = p->dirty = p->locked = 0;
    p->note[0] = 0;
    choose(p);
    const char *why = open_file(p);
    if (why) {
        p->locked = 1;
        blank(p);
        note(p, "not opened: ", why);
    }
    put_s(&l, "paint: opened ");
    put_s(&l, p->path);
    put_s(&l, " (");
    put_dec(&l, (u64)p->w);
    put_s(&l, "x");
    put_dec(&l, (u64)p->h);
    put_s(&l, why ? ", not opened: " : fs_stat(&p->fs, p->path, 0) ? ", from the card)" : ", new)");
    if (why) {
        put_s(&l, why);
        put_s(&l, "; it will not be saved over)");
    }
    say(&l);
    put_s(&l, "paint: undo has ");
    put_dec(&l, p->u.size);
    put_s(&l, " bytes; a change to the whole picture needs at most ");
    put_dec(&l, UNDO_NEED);
    say(&l);
    draw_bar(p);
    draw_margin(p);
    draw_foot(p);
    u64 opened = app_open_drag(WIN_OFF, WW, WH, "Paint");
    put_s(&l, "paint: opened a window");
    put_s(&l, outcome(opened));
    say(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        int pending = p->dirty && !p->locked && !p->down;          /* a save to make, soon */
        struct event ev = pending ? app_poll(dirty) : app_wait(dirty);
        u64 kind = ev.kind;
        int x = (int)ev.a, y = (int)ev.b;
        dirty = 0;
        if (kind == EV_CLOSE) {
            if (p->down) release(p, &l);
            if (p->dirty) save(p, &l);
            put_s(&l, "paint: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (kind == EV_NONE) {
            if (pending && millis() >= p->save_at) save(p, &l);
            else {
                sleep_ms(20);
                continue;
            }
        } else if (kind == EV_DOWN || kind == EV_RDOWN) {
            press(p, &l, x, y, kind == EV_RDOWN);
        } else if (kind == EV_MOVE) {
            if (!p->down) continue;
            drag(p, x, y - CY);
            if (p->op == T_PICK) draw_foot(p);
            dirty = 1;
            continue;
        } else if (kind == EV_UP || kind == EV_RUP) {
            if (!p->down) continue;
            drag(p, x, y - CY);
            release(p, &l);
        } else if (kind == EV_KEY) {
            key(p, &l, ev.a);
        } else continue;
        draw_bar(p);
        draw_foot(p);
        dirty = 1;
    }
}
