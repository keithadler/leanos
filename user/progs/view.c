/* view: a picture viewer, from the SD card. `run view photo.bmp` in Terminal shows that file
   (up to 7 files: each one it is given; given a folder, the pictures in it); given none, it
   shows the pictures in its own folder, apps/view/, in the order of their names (the card
   people use comes with two there, colors.bmp and sunset.ppm, which tools/mksamples.py makes
   at build time). The file server lets it reach nothing else.

   It reads BMP, uncompressed (1, 4 and 8 bits a pixel with a palette, 16 and 32 bits with or
   without color masks, 24 bits; rows bottom-up or top-down; the 12-byte header of the oldest
   BMPs and the 40- to 124-byte ones since), which is what `paint` saves, and binary PPM (P6)
   and PGM (P5) with samples of one byte (maxval 255, or less, stretched to 255). Anything else
   is refused, with the reason in the window: a file that is not a picture, a compressed BMP
   (RLE, or a JPEG or PNG inside one), one that ends before its pixels do, one wider or taller
   than 16384 pixels. The file is taken to be hostile: every size and offset in it is checked
   against the file's size before it is used, in 64-bit arithmetic that cannot overflow (16384
   x 16384 x 4 bytes is 1 GiB), and a pixel's palette index past the palette is black.

     Left, Right   the previous or next picture (N and P too, or Page Up and Page Down, or the
                   < and > buttons; Home and End: the first and the last); when the picture is
                   wider than the window, they move across it instead
     Up, Down      move up and down a picture taller than the window
     F (or 0)      fit: the whole picture in the window, the way each one opens (a picture
                   smaller than the window is shown at its own size, not enlarged)
     1             1:1, a pixel of the picture to a pixel of the screen
     + and -       zoom in and out, from 1/64 to 16 times (the buttons too)
     a click       on a picture larger than the window: that point to the middle

   A picture made smaller is averaged over each screen pixel's box of picture pixels (a box
   filter), not sampled, so fine detail turns to its average color instead of shimmering; one
   made larger repeats its pixels. The status line says the name, the size, the format and the
   zoom. The window cannot be dragged over a picture to move it: the display server sends a
   program a click (EV_DOWN) but not the moves of a drag.

   Memory: a program from the card has 64 KiB of code, 32 KiB of data, 16 KiB of stack and a
   spare run of 228 pages (912 KiB), of which the fonts take 64, this window's pixels 157 and
   the file server's buffer 4. A picture's pixels do not fit in what is left (3 pages; 640 x
   480 alone is 1.2 MB as the screen stores it), and would not fit in all of it. So view keeps
   no copy of the picture: whenever what it shows changes, it reads again just the rows it
   needs, from the file server, a piece at a time (up to 16128 bytes a request, fs.h), and
   draws them into the window as they come. That makes the size of a picture a question of
   time, not memory: fitting a large one reads all of it (under QEMU the file server gives
   about 1.3 MB a second: a 2 MB picture fits in under 2 s). The largest it takes is 16384 x
   16384 pixels (MAX_SIDE), where fitting it still averages at most 65 x 65 pixels into each
   one on the screen, in 32 bits; a bigger one is refused, saying so. While a slow picture is
   drawn, the window shows it coming, and a key or a click stops the drawing to do what it
   asks (the close button, at once). */
#include "../ui.h"
#include "../fs.h"

/* Only the drawing loops run often: the rest is compiled for size. */
#define COLD __attribute__((cold, minsize))

#define VW 500
#define VH 320                      /* 157 pages of pixels */
#define BAR_H 28                    /* the status line, across the foot */
#define AH (VH - BAR_H)             /* the picture's part of the window: VW x AH */
#define MAX_SIDE 16384
#define MAX_PICS 64                 /* pictures listed from the folder */
#define QUEUE 16                    /* events that come while it draws */
#define BTN_Y (AH + 4)
#define BTN_H 20

#define BG rgb(30, 31, 36)
#define BAR rgb(44, 46, 54)
#define EDGE rgb(62, 65, 76)
#define BTN rgb(66, 69, 82)
#define LIGHT rgb(228, 230, 238)
#define GRAY rgb(150, 154, 168)

/* How a pixel is stored: blue, green, red (BMP's 24 bits); a 16- or 32-bit word cut by color
   masks; an index into the palette (1, 4 or 8 bits); red, green, blue (PPM); a gray (PGM). */
enum { M_BGR, M_MASK, M_PAL, M_RGB, M_GRAY };

/* A picture, as its header says, every part of it checked against the file. */
struct pic {
    u64 w, h;
    u64 data, stride;               /* the first row stored: where in the file, and bytes from one to the next */
    int mode, bpp, topdown;
    unsigned mask[3], max[3];       /* M_MASK: red, green, blue, and what each can reach */
    int shift[3], bits[3];
    unsigned pal[256];              /* M_PAL; entries past the palette are black */
    unsigned char lut[256];         /* M_RGB and M_GRAY: a sample (up to maxval) to 0..255 */
    char format[24];
};

struct view {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    char folder[FS_PATH_MAX + 1];   /* its own: apps/view */
    char given[FS_GRANTS_PER_SLOT][FS_PATH_MAX + 1];
    int ngiven;
    char names[MAX_PICS][FS_NAME_MAX + 1];   /* the folder's pictures, sorted */
    int nnames, cur;                /* the list: the files it was given, then the folder's */
    char path[FS_PATH_MAX + 1];     /* the picture shown */
    const char *name;               /* its last part */
    int ok;                         /* its header was good; if not, why */
    char why[160];
    u64 size;
    struct pic p;
    u64 dw, dh;                     /* the picture's size on the screen */
    long px, py;                    /* when larger than the window: how far into it the window starts */
    int fit;
    unsigned zn, zd;                /* the zoom, when + , - or 1 chose it: zn / zd */
    /* the file, read in pieces: [lo, hi) of it is in the file server buffer's data area */
    u64 lo, hi, reads, read_us;
    int short_read;
    unsigned s0[VW], s1[VW];        /* for each column of the window, the picture's columns [s0, s1) */
    unsigned acc[3 * VW];           /* one row's sums */
    struct event q[QUEUE];
    int qn, qh;
};

_Static_assert(sizeof(struct view) <= 8 * 4096, "view's state is larger than its data run");

static const unsigned char zeros[8] = {0};

/* ---- the file, a piece at a time ---- */

/* Read the file from `start` into the buffer, for the `n` bytes at `off`: their address, or
   zeros if the file does not have them (it changed since view checked it). */
static const unsigned char *fetch(struct view *v, u64 off, u64 n, u64 start) {
    u64 t0 = micros();
    long got = fs_read_at(&v->fs, v->path, start, 0);
    v->reads++;
    v->read_us += micros() - t0;
    v->lo = start;
    v->hi = start + (u64)(got > 0 ? got : 0);
    if (off < v->lo || off + n > v->hi) {
        v->short_read = 1;
        return zeros;
    }
    return (const unsigned char *)v->fs.buf + FS_DATA_OFF + (off - v->lo);
}

/* The `n` bytes at `off` (n up to FS_CHUNK). */
static inline const unsigned char *get(struct view *v, u64 off, u64 n) {
    if (off >= v->lo && off + n <= v->hi) return (const unsigned char *)v->fs.buf + FS_DATA_OFF + (off - v->lo);
    return fetch(v, off, n, off);
}

/* A row's bytes are about to be read, from `off`. If they are not in the buffer, read them;
   and when the rows go backward in the file (a BMP's are stored bottom-up), read the piece
   that ends where this row does, so the next rows up the screen are in it too. */
static void want(struct view *v, u64 off, u64 n) {
    if (n > FS_CHUNK) n = FS_CHUNK;
    if (off >= v->lo && off + n <= v->hi) return;
    u64 start = off >= v->lo ? off : off + n > FS_CHUNK ? off + n - FS_CHUNK : 0;
    fetch(v, off, n, start);
}

static unsigned le16(const unsigned char *p) { return p[0] | (unsigned)p[1] << 8; }
static unsigned le32(const unsigned char *p) { return le16(p) | le16(p + 2) << 16; }

/* ---- reading the header ---- */

static void scopy(char *d, const char *s, int max) {
    int i = 0;
    for (; s[i] && i < max; i++) d[i] = s[i];
    d[i] = 0;
}

/* why = a, then b, then a number and c (any of them may be 0) */
COLD static void refuse(struct view *v, const char *a, const char *b, u64 n, const char *c) {
    struct line l = {.n = 0};
    put_s(&l, a);
    if (b) put_s(&l, b);
    if (c) { put_dec(&l, n); put_s(&l, c); }
    if (l.n > sizeof v->why - 1) l.n = sizeof v->why - 1;
    for (u64 i = 0; i < l.n; i++) v->why[i] = l.b[i];
    v->why[l.n] = 0;
}

COLD static void too_large(struct view *v, u64 w, u64 h) {
    struct line l = {.n = 0};
    put_dec(&l, w);
    put_s(&l, " x ");
    put_dec(&l, h);
    put_s(&l, " pixels is too large: view takes pictures up to 16384 x 16384");
    l.b[l.n] = 0;
    refuse(v, l.b, 0, 0, 0);
}

/* The pixels, `stride` bytes a row from `data`, must be in the file. */
COLD static int in_file(struct view *v, u64 data, u64 stride) {
    if (data <= v->size && stride * v->p.h <= v->size - data) return 1;
    refuse(v, "the file ends before its pixels do: it has ", 0, v->size, " bytes, and is cut short");
    return 0;
}

COLD static int bmp(struct view *v) {
    struct pic *p = &v->p;
    if (v->size < 26) { refuse(v, "too short to be a BMP", 0, 0, 0); return 0; }
    u64 hn = v->size < 14 + 124 + 16 ? v->size : 14 + 124 + 16;
    const unsigned char *h = get(v, 0, hn);
    unsigned data = le32(h + 10), hs = le32(h + 14), planes, comp = 0, used = 0, entry = 4;
    long w, ht;
    if (hs == 12) {                                     /* the oldest header: 16-bit sizes */
        w = le16(h + 18);
        ht = le16(h + 20);
        planes = le16(h + 22);
        p->bpp = (int)le16(h + 24);
        entry = 3;
    } else if (hs == 40 || hs == 52 || hs == 56 || hs == 64 || hs == 108 || hs == 124) {
        if (v->size < 14 + (u64)hs) { refuse(v, "the file ends inside its header", 0, 0, 0); return 0; }
        w = (int)le32(h + 18);
        ht = (int)le32(h + 22);
        planes = le16(h + 26);
        p->bpp = (int)le16(h + 28);
        comp = le32(h + 30);
        used = le32(h + 46);
    } else {
        refuse(v, "an unknown kind of BMP: its header is ", 0, hs, " bytes");
        return 0;
    }
    static const char *const packed[] = {0, "RLE8", "RLE4", 0, "a JPEG", "a PNG"};
    if (comp == 1 || comp == 2 || comp == 4 || comp == 5) {
        refuse(v, "a compressed BMP (", packed[comp], 0, 0);
        refuse(v, v->why, "): view reads only uncompressed ones", 0, 0);
        return 0;
    }
    int masks = comp == 3 || comp == 6;
    if ((comp != 0 && !masks) || (hs == 64 && comp != 0)) {
        refuse(v, "a BMP compressed in a way view does not know (", 0, comp, ")");
        return 0;
    }
    if (planes != 1) { refuse(v, "a bad BMP header: ", 0, planes, " planes"); return 0; }
    p->topdown = ht < 0;
    if (ht < 0) ht = -ht;
    if (w <= 0 || ht == 0) { refuse(v, "a picture with no pixels: its width or height is 0 or less", 0, 0, 0); return 0; }
    if (w > MAX_SIDE || ht > MAX_SIDE) { too_large(v, (u64)w, (u64)ht); return 0; }
    p->w = (u64)w;
    p->h = (u64)ht;
    int b = p->bpp;
    if (b == 1 || b == 4 || b == 8) {
        if (masks) { refuse(v, "a bad BMP header: color masks with a palette", 0, 0, 0); return 0; }
        u64 n = used && used < (1u << b) ? used : 1u << b, at = 14 + (u64)hs;
        if (at + n * entry > v->size) { refuse(v, "the file ends inside its palette", 0, 0, 0); return 0; }
        want(v, at, n * entry);                         /* all of it at once: at most 1 KiB */
        for (int i = 0; i < 256; i++) p->pal[i] = 0;
        for (u64 i = 0; i < n; i++) {
            const unsigned char *q = get(v, at + i * entry, 3);
            p->pal[i] = rgb(q[2], q[1], q[0]);
        }
        p->mode = M_PAL;
    } else if (b == 16 || b == 32) {
        p->mode = M_MASK;
        if (masks) {
            /* after a 40-byte header, else in it: at byte 54 either way */
            if (v->size < 54 + 12) { refuse(v, "the file ends inside its color masks", 0, 0, 0); return 0; }
            const unsigned char *q = get(v, 54, 12);
            for (int i = 0; i < 3; i++) p->mask[i] = le32(q + 4 * i);
        } else if (b == 16) {
            p->mask[0] = 0x7c00; p->mask[1] = 0x03e0; p->mask[2] = 0x001f;
        } else {
            p->mask[0] = 0xff0000; p->mask[1] = 0xff00; p->mask[2] = 0xff;
        }
        for (int i = 0; i < 3; i++) {                   /* where each color is, and how many bits */
            u64 m = p->mask[i];                         /* (64 bits: m >> 32 is 0, not m) */
            int s = 0, n = 0;
            while (m && !(m & 1)) { m >>= 1; s++; }
            while (m >> n) n++;
            p->shift[i] = s;
            p->bits[i] = n;
            p->max[i] = n ? (unsigned)((1ull << n) - 1) : 1;
        }
    } else if (b == 24 && !masks) {
        p->mode = M_BGR;
    } else {
        refuse(v, "a BMP of ", 0, (u64)b, masks ? " bits a pixel with color masks, which view does not read"
                                               : " bits a pixel, which view does not read");
        return 0;
    }
    p->stride = ((u64)w * (u64)b + 31) / 32 * 4;
    if (data < 14 + (u64)hs) { refuse(v, "a bad BMP header: its pixels start inside it", 0, 0, 0); return 0; }
    if (!in_file(v, data, p->stride)) return 0;
    p->data = data;
    struct line l = {.n = 0};
    put_s(&l, "BMP ");
    put_dec(&l, (u64)b);
    put_s(&l, "-bit");
    l.b[l.n] = 0;
    scopy(p->format, l.b, sizeof p->format - 1);
    return 1;
}

/* A number of a PPM or PGM header: skip white space and # comments, then the digits. */
COLD static long ppm_number(const unsigned char *h, u64 n, u64 *at) {
    for (;;) {
        while (*at < n && (h[*at] == ' ' || h[*at] == '\t' || h[*at] == '\r' || h[*at] == '\n')) (*at)++;
        if (*at < n && h[*at] == '#') { while (*at < n && h[*at] != '\n') (*at)++; continue; }
        break;
    }
    long v = 0;
    int digits = 0;
    while (*at < n && h[*at] >= '0' && h[*at] <= '9') {
        if (v > 100000000) return -1;
        v = v * 10 + (h[(*at)++] - '0');
        digits++;
    }
    return digits ? v : -1;
}

COLD static int ppm(struct view *v, int gray) {
    struct pic *p = &v->p;
    u64 n = v->size < 1024 ? v->size : 1024, at = 2;
    const unsigned char *h = get(v, 0, n);
    long w = ppm_number(h, n, &at), ht = ppm_number(h, n, &at), maxval = ppm_number(h, n, &at);
    if (w < 0 || ht < 0 || maxval < 0 || at >= n || !(h[at] == ' ' || h[at] == '\t' || h[at] == '\r' || h[at] == '\n')) {
        refuse(v, gray ? "a bad PGM header" : "a bad PPM header", 0, 0, 0);
        return 0;
    }
    if (maxval == 0 || maxval > 255) {
        refuse(v, "samples up to ", 0, (u64)maxval, maxval ? " (two bytes each): view takes one byte a sample, maxval 255"
                                                        : ": a maxval of 0 is not a picture");
        return 0;
    }
    if (w == 0 || ht == 0) { refuse(v, "a picture with no pixels: its width or height is 0", 0, 0, 0); return 0; }
    if (w > MAX_SIDE || ht > MAX_SIDE) { too_large(v, (u64)w, (u64)ht); return 0; }
    p->w = (u64)w;
    p->h = (u64)ht;
    p->bpp = gray ? 8 : 24;
    p->mode = gray ? M_GRAY : M_RGB;
    p->topdown = 1;                                     /* a PPM's rows go down the picture */
    p->stride = p->w * (gray ? 1 : 3);
    if (!in_file(v, at + 1, p->stride)) return 0;
    p->data = at + 1;
    for (unsigned i = 0; i < 256; i++) p->lut[i] = (unsigned char)(i >= (unsigned)maxval ? 255 : (i * 255 + (unsigned)maxval / 2) / (unsigned)maxval);
    scopy(p->format, gray ? "PGM" : "PPM", 8);
    return 1;
}

/* What the file is, from its first bytes. */
COLD static int header(struct view *v) {
    if (v->size < 2) { refuse(v, v->size ? "too short to be a picture" : "the file is empty", 0, 0, 0); return 0; }
    const unsigned char *h = get(v, 0, 2);
    unsigned a = h[0], b = h[1];
    if (a == 'B' && b == 'M') return bmp(v);
    if (a == 'P' && (b == '5' || b == '6')) return ppm(v, b == '5');
    if (a == 'P' && b >= '1' && b <= '4') {
        refuse(v, b == '4' ? "a PBM (P4), black and white, which view does not read: it reads P5 and P6"
                           : "a PNM written as text (P1 to P3), which view does not read: it reads binary P5 and P6", 0, 0, 0);
        return 0;
    }
    if (a == 0x89 && b == 'P') refuse(v, "a PNG, which view does not read: it reads BMP, PPM and PGM", 0, 0, 0);
    else if (a == 0xff && b == 0xd8) refuse(v, "a JPEG, which view does not read: it reads BMP, PPM and PGM", 0, 0, 0);
    else refuse(v, "not a picture view knows: a BMP starts with BM, a PPM with P6, a PGM with P5", 0, 0, 0);
    return 0;
}

/* ---- the list of pictures ---- */

static int lower(int c) { return c >= 'A' && c <= 'Z' ? c + 32 : c; }

/* A name that ends in .bmp, .ppm, .pgm or .pnm, in either case. */
COLD static int picture_name(const char *s) {
    int n = 0;
    while (s[n]) n++;
    if (n < 5 || s[n - 4] != '.') return 0;
    static const char exts[] = "bmp\0ppm\0pgm\0pnm";
    for (int e = 0; e < 4; e++) {
        const char *x = exts + 4 * e;
        if (lower(s[n - 3]) == x[0] && lower(s[n - 2]) == x[1] && lower(s[n - 1]) == x[2]) return 1;
    }
    return 0;
}

static int same(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == *b;
}
static int before(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return (unsigned char)*a < (unsigned char)*b;
}

static int count(struct view *v) { return v->ngiven + v->nnames; }

/* The pictures: the files it was given (its grants that are not folders), then the folder's
   (the grant that is one: apps/view), by name, without those it was given as well. */
COLD static void gather(struct view *v) {
    char list[2048];
    long n = fs_grants(&v->fs);
    const char *g = fs_data(&v->fs);
    for (int k = 0; k < (int)sizeof list; k++) list[k] = g[k];      /* the buffer is about to be reused */
    list[sizeof list - 1] = 0;
    scopy(v->folder, "apps/view", FS_PATH_MAX);
    const char *p = list;
    for (long i = 0; i < n && p < list + sizeof list - 1; i++) {
        const char *path = p + 1;                                    /* after the rights byte */
        int len = 0;
        while (path[len] && path + len < list + sizeof list - 1) len++;
        if (fs_stat(&v->fs, path, 0) == FS_DIR) scopy(v->folder, path, FS_PATH_MAX);
        else if (v->ngiven < FS_GRANTS_PER_SLOT) scopy(v->given[v->ngiven++], path, FS_PATH_MAX);
        p = path + len + 1;
    }
    v->nnames = 0;
    u64 total = 0;
    for (u64 from = 0;;) {
        long got = fs_list_dir(&v->fs, v->folder, from, &total);
        if (got <= 0) break;
        const struct fs_entry *e = fs_entries(&v->fs);
        for (long i = 0; i < got; i++) {
            char name[FS_NAME_MAX + 1];
            scopy(name, e[i].name, FS_NAME_MAX);
            if (e[i].kind != FS_FILE || !picture_name(name) || v->nnames >= MAX_PICS) continue;
            char full[FS_PATH_MAX + 1];
            struct line l = {.n = 0};
            put_s(&l, v->folder);
            put_s(&l, "/");
            put_s(&l, name);
            l.b[l.n < FS_PATH_MAX ? l.n : FS_PATH_MAX] = 0;
            scopy(full, l.b, FS_PATH_MAX);
            int dup = 0;
            for (int k = 0; k < v->ngiven; k++) dup |= same(v->given[k], full);
            if (dup) continue;
            int at = v->nnames++;                                    /* in order of names */
            while (at > 0 && before(name, v->names[at - 1])) {
                scopy(v->names[at], v->names[at - 1], FS_NAME_MAX);
                at--;
            }
            scopy(v->names[at], name, FS_NAME_MAX);
        }
        from += (u64)got;
        if (from >= total) break;
    }
}

/* ---- the view: where the picture goes ---- */

/* Where the picture's left (or top) edge is in the window: centered if it fits, else `pan`
   into it. */
static long origin(u64 shown, long room, long pan) { return (long)shown <= room ? (room - (long)shown) / 2 : -pan; }

static void clamp(struct view *v) {
    long mx = (long)v->dw - VW, my = (long)v->dh - AH;
    if (v->px > mx) v->px = mx;
    if (v->py > my) v->py = my;
    if (v->px < 0) v->px = 0;
    if (v->py < 0) v->py = 0;
}

/* Show the picture `dw` x `dh` on the screen, keeping the point at the middle of the window
   where it is. */
COLD static void resize(struct view *v, u64 dw, u64 dh) {
    if (dw < 1) dw = 1;
    if (dh < 1) dh = 1;
    /* (a picture that fits the window has its middle there: exactly) */
    v->px = ((long)v->dw <= VW ? (long)dw / 2 : (long)((u64)(v->px + VW / 2) * dw / v->dw)) - VW / 2;
    v->py = ((long)v->dh <= AH ? (long)dh / 2 : (long)((u64)(v->py + AH / 2) * dh / v->dh)) - AH / 2;
    v->dw = dw;
    v->dh = dh;
    clamp(v);
}

COLD static void fit(struct view *v) {
    u64 w = v->p.w, h = v->p.h;
    v->fit = 1;
    v->zn = 0;
    if (w <= VW && h <= AH) resize(v, w, h);
    else if (w * AH >= h * VW) resize(v, VW, h * VW / w);
    else resize(v, w * AH / h, AH);
}

/* The zooms + and - go through, as fractions. */
static const unsigned char zooms[][2] = {{1, 64}, {1, 32}, {1, 16}, {1, 8}, {1, 6}, {1, 4}, {1, 3}, {1, 2}, {2, 3},
                                         {1, 1}, {3, 2}, {2, 1}, {3, 1}, {4, 1}, {6, 1}, {8, 1}, {16, 1}};
#define NZOOM ((int)(sizeof zooms / sizeof zooms[0]))

COLD static void zoom(struct view *v, int dir) {
    int pick = -1;
    for (int i = 0; i < NZOOM; i++) {
        u64 a = zooms[i][0] * v->p.w, b = v->dw * zooms[i][1];      /* this zoom against the one shown */
        if (dir > 0 && a > b) { pick = i; break; }
        if (dir < 0 && a < b) pick = i;
        if (dir == 0 && i == 9) pick = i;                           /* 1:1 */
    }
    if (pick < 0) return;
    v->fit = 0;
    v->zn = zooms[pick][0];
    v->zd = zooms[pick][1];
    resize(v, v->p.w * zooms[pick][0] / zooms[pick][1], v->p.h * zooms[pick][0] / zooms[pick][1]);
}

/* The zoom in percent: the one chosen, or what fitting came to. */
static u64 percent(struct view *v) {
    return v->zn ? (v->zn * 100 + v->zd / 2) / v->zd : (v->dw * 100 + v->p.w / 2) / v->p.w;
}

/* ---- drawing ---- */

/* Pixel x of a row, as 0x00RRGGBB, from its bytes at q (for 1 and 4 bits: the byte it is in). */
static inline unsigned decode(const struct pic *p, const unsigned char *q, u64 x) {
    if (p->mode == M_BGR) return rgb(q[2], q[1], q[0]);
    if (p->mode == M_RGB) return rgb(p->lut[q[0]], p->lut[q[1]], p->lut[q[2]]);
    if (p->mode == M_GRAY) {
        unsigned g = p->lut[q[0]];
        return rgb(g, g, g);
    }
    if (p->mode == M_PAL) {
        unsigned i = q[0] >> (8 - p->bpp - (int)(x * (u64)p->bpp % 8));
        return p->pal[i & ((1u << p->bpp) - 1)];
    }
    unsigned word = p->bpp == 16 ? le16(q) : le32(q), c[3];
    for (int i = 0; i < 3; i++) {
        unsigned k = (word & p->mask[i]) >> p->shift[i];
        c[i] = p->bits[i] >= 8 ? k >> (p->bits[i] - 8) : k * 255 / p->max[i];
    }
    return rgb(c[0], c[1], c[2]);
}

/* Add row `sy` of the picture (from the top) into the sums of columns [xa, xb). Straight from
   the buffer when the row's part is all in it, as it is unless a row is longer than a read. */
static void add_row(struct view *v, u64 sy, int xa, int xb) {
    const struct pic *p = &v->p;
    u64 bpp = (u64)p->bpp, bytes = bpp < 8 ? 1 : bpp / 8;
    u64 row = p->data + (p->topdown ? sy : p->h - 1 - sy) * p->stride;
    u64 from = (u64)v->s0[xa] * bpp / 8, to = ((u64)v->s1[xb - 1] * bpp + 7) / 8;
    want(v, row + from, to - from);
    int direct = row + from >= v->lo && row + to <= v->hi;
    const unsigned char *base = direct ? (const unsigned char *)v->fs.buf + FS_DATA_OFF + (row + from - v->lo) : zeros;
    for (int x = xa; x < xb; x++) {
        unsigned r = 0, g = 0, b = 0;
        for (u64 sx = v->s0[x]; sx < v->s1[x]; sx++) {
            u64 at = sx * bpp / 8;
            unsigned c = decode(p, direct ? base + (at - from) : get(v, row + at, bytes), sx);
            r += c >> 16;
            g += c >> 8 & 255;
            b += c & 255;
        }
        v->acc[3 * x] += r;
        v->acc[3 * x + 1] += g;
        v->acc[3 * x + 2] += b;
    }
}

COLD static void say(struct line *l) { put_s(l, "\n"); flush(l); }

/* While it draws: let the display show what is drawn so far, and hear what came meanwhile.
   The close button ends it; a key or a click stops the drawing (1), to do what it asks. */
COLD static int listen(struct view *v) {
    int stop = 0;
    for (;;) {
        struct event e = app_poll(1);
        if (e.kind == EV_NONE) return stop;
        if (e.kind == EV_CLOSE) {
            struct line l = {.n = 0};
            put_s(&l, "view: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (e.kind != EV_KEY && e.kind != EV_DOWN) continue;
        if (v->qn < QUEUE) v->q[(v->qh + v->qn++) % QUEUE] = e;
        stop = 1;
    }
}

/* The picture into the window, from the file: 1 if it stopped for an event. */
static int render(struct view *v) {
    struct surface *s = &v->win;
    const struct pic *p = &v->p;
    long ix = origin(v->dw, VW, v->px), iy = origin(v->dh, AH, v->py);
    int xa = ix < 0 ? 0 : (int)ix, xb = ix + (long)v->dw > VW ? VW : (int)(ix + (long)v->dw);
    int ya = iy < 0 ? 0 : (int)iy, yb = iy + (long)v->dh > AH ? AH : (int)(iy + (long)v->dh);
    fill(s, 0, 0, VW, AH, BG);
    for (int x = xa; x < xb; x++) {                     /* each column's box of picture columns */
        u64 u = (u64)(x - ix);
        v->s0[x] = (unsigned)(u * p->w / v->dw);
        v->s1[x] = (unsigned)((u + 1) * p->w / v->dw);
        if (v->s1[x] <= v->s0[x]) v->s1[x] = v->s0[x] + 1;
    }
    u64 shown = millis();
    for (int y = ya; y < yb; y++) {
        u64 t = (u64)(y - iy), r0 = t * p->h / v->dh, r1 = (t + 1) * p->h / v->dh;
        if (r1 <= r0) r1 = r0 + 1;
        for (int i = 3 * xa; i < 3 * xb; i++) v->acc[i] = 0;
        for (u64 sy = r0; sy < r1; sy++) add_row(v, sy, xa, xb);
        unsigned *out = s->px + y * s->stride;
        for (int x = xa; x < xb; x++) {
            unsigned n = (v->s1[x] - v->s0[x]) * (unsigned)(r1 - r0), *a = v->acc + 3 * x;
            out[x] = n == 1 ? rgb(a[0], a[1], a[2]) : rgb((a[0] + n / 2) / n, (a[1] + n / 2) / n, (a[2] + n / 2) / n);
        }
        if (millis() - shown >= 100) {                  /* a slow one: show it coming */
            shown = millis();
            if (listen(v)) return 1;
        }
    }
    return 0;
}

/* A button of the status line: its x, width, label and the key it presses. */
struct button { short x, w; char key; char label[4]; };
static const struct button buttons[] = {
    {8, 24, 'p', "<"}, {36, 24, 'n', ">"},
    {VW - 132, 36, 'f', "Fit"}, {VW - 92, 36, '1', "1:1"}, {VW - 52, 20, '-', "-"}, {VW - 28, 20, '+', "+"}};
#define NBUTTON ((int)(sizeof buttons / sizeof buttons[0]))
#define TEXT_X 68
#define TEXT_W (VW - 132 - 8 - TEXT_X)

COLD static void bar(struct view *v) {
    struct surface *s = &v->win;
    fill(s, 0, AH, VW, BAR_H, BAR);
    fill(s, 0, AH, VW, 1, EDGE);
    for (int i = 0; i < NBUTTON; i++) {
        const struct button *b = &buttons[i];
        round_rect(s, b->x, BTN_Y, b->w, BTN_H, 6, BTN, 255);
        font_text(s, &v->ui.small_bold, b->x + b->w / 2 - font_width(&v->ui.small_bold, b->label) / 2, BTN_Y + 15,
                  b->label, LIGHT);
    }
    struct line l = {.n = 0};
    if (!count(v)) put_s(&l, "no pictures");
    else if (!v->ok) put_s(&l, "cannot show it");
    else {
        put_dec(&l, v->p.w);
        put_s(&l, " x ");
        put_dec(&l, v->p.h);
        put_s(&l, "   ");
        put_s(&l, v->p.format);
        put_s(&l, v->fit && v->dw < v->p.w ? "   fit " : "   ");
        put_dec(&l, percent(v));
        put_s(&l, "%");
    }
    l.b[l.n] = 0;
    int dx = font_width(&v->ui.small, l.b), room = TEXT_W - dx - 12;
    char name[FS_NAME_MAX + 1];
    scopy(name, count(v) ? v->name : "", FS_NAME_MAX);
    int n = 0;
    while (name[n]) n++;
    while (n > 4 && font_width(&v->ui.small_bold, name) > room) {    /* too long: cut, with ... */
        n--;
        name[n - 3] = name[n - 2] = name[n - 1] = '.';
        name[n] = 0;
    }
    int x = font_text(s, &v->ui.small_bold, TEXT_X, AH + 18, name, LIGHT);
    font_text(s, &v->ui.small, x + (name[0] ? 12 : 0), AH + 18, l.b, GRAY);
}

/* Instead of a picture: a heading, and why. */
COLD static void message(struct view *v, const char *title, const char *text) {
    struct surface *s = &v->win;
    fill(s, 0, 0, VW, AH, BG);
    font_text(s, &v->ui.bold, 28, AH / 2 - 16, title, LIGHT);
    text_wrap(s, &v->ui.body, 28, AH / 2 + 10, VW - 56, 21, text, GRAY);
}

/* Everything, and the log: 1 if the drawing stopped for an event. */
COLD static int draw(struct view *v, struct line *l) {
    bar(v);
    if (!count(v)) {
        message(v, "No pictures", "Give view one with run view FILE in Terminal, or put BMP, PPM or PGM files "
                                  "in its folder, apps/view.");
        return 0;
    }
    if (!v->ok) {
        char title[FS_NAME_MAX + 20];
        struct line t = {.n = 0};
        put_s(&t, "Cannot show ");
        put_s(&t, v->name);
        t.b[t.n < sizeof title - 1 ? t.n : sizeof title - 1] = 0;
        scopy(title, t.b, sizeof title - 1);
        message(v, title, v->why);
        return 0;
    }
    u64 t0 = millis();
    v->reads = v->read_us = 0;
    v->short_read = 0;
    if (render(v)) return 1;
    put_s(l, "view: drew ");
    put_s(l, v->name);
    put_s(l, " at ");
    put_dec(l, percent(v));
    put_s(l, v->fit ? "% (fit), " : "%, ");
    put_dec(l, v->dw);
    put_s(l, "x");
    put_dec(l, v->dh);
    put_s(l, " on the screen, in ");
    put_dec(l, millis() - t0);
    put_s(l, " ms from ");
    put_dec(l, v->reads);
    put_s(l, v->reads == 1 ? " read (" : " reads (");
    put_dec(l, v->read_us / 1000);
    put_s(l, " ms of it reading)");
    if (v->short_read) put_s(l, "; the file ended early: it changed");
    say(l);
    return 0;
}

/* ---- going through the pictures ---- */

COLD static void open_pic(struct view *v, struct line *l) {
    if (!count(v)) return;
    if (v->cur < v->ngiven) scopy(v->path, v->given[v->cur], FS_PATH_MAX);
    else {
        struct line t = {.n = 0};
        put_s(&t, v->folder);
        put_s(&t, "/");
        put_s(&t, v->names[v->cur - v->ngiven]);
        t.b[t.n < FS_PATH_MAX ? t.n : FS_PATH_MAX] = 0;
        scopy(v->path, t.b, FS_PATH_MAX);
    }
    v->name = v->path;
    for (const char *c = v->path; *c; c++) if (*c == '/') v->name = c + 1;
    v->lo = v->hi = 0;
    v->ok = 0;
    v->size = 0;
    memset(&v->p, 0, sizeof v->p);
    fs_path(&v->fs, v->path);
    struct res r = fs_call(&v->fs, FS_STAT, 0);
    if (r.x[1] == FS_DENIED) refuse(v, "view was not given this file", 0, 0, 0);
    else if (r.x[1] != FS_OK) refuse(v, "no such file", 0, 0, 0);
    else if (r.x[3] != FS_FILE) refuse(v, "a folder, not a picture", 0, 0, 0);
    else {
        v->size = r.x[2];
        v->ok = header(v);
    }
    if (v->ok) {
        v->dw = v->p.w;                                 /* so fit() keeps the middle */
        v->dh = v->p.h;
        v->px = v->py = 0;
        fit(v);
    }
    put_s(l, "view: ");
    if (v->ok) {
        put_s(l, "opened ");
        put_s(l, v->path);
        put_s(l, ": ");
        put_dec(l, v->p.w);
        put_s(l, "x");
        put_dec(l, v->p.h);
        put_s(l, ", ");
        put_s(l, v->p.format);
        if (v->p.topdown && v->p.format[0] == 'B') put_s(l, ", top-down");     /* a BMP that says so */
    } else {
        put_s(l, "cannot show ");
        put_s(l, v->path);
        put_s(l, ": ");
        put_s(l, v->why);
    }
    say(l);
}

COLD static int go(struct view *v, struct line *l, int to) {
    int n = count(v);
    if (n < 2) return 0;
    v->cur = (to % n + n) % n;                          /* around, at either end */
    open_pic(v, l);
    return 1;
}

/* A key: 1 if it changed what is shown. */
COLD static int key(struct view *v, struct line *l, u64 k) {
    int wide = v->ok && (long)v->dw > VW, tall = v->ok && (long)v->dh > AH;
    if (k == 'n' || k == 'N' || k == ' ' || k == KEY_PGDN || (k == KEY_RIGHT && !wide)) return go(v, l, v->cur + 1);
    if (k == 'p' || k == 'P' || k == 127 || k == KEY_PGUP || (k == KEY_LEFT && !wide)) return go(v, l, v->cur - 1);
    if (k == KEY_HOME) return go(v, l, 0);
    if (k == KEY_END) return go(v, l, count(v) - 1);
    if (!v->ok) return 0;
    if (k == 'f' || k == 'F' || k == '0') fit(v);
    else if (k == '1') zoom(v, 0);
    else if (k == '+' || k == '=') zoom(v, 1);
    else if (k == '-' || k == '_') zoom(v, -1);
    else if (k >= KEY_UP && k <= KEY_LEFT) {           /* move across it, not past its edges */
        long px = v->px, py = v->py;
        v->px += k == KEY_RIGHT ? VW / 4 : k == KEY_LEFT ? -VW / 4 : 0;
        v->py += k == KEY_DOWN && tall ? AH / 4 : k == KEY_UP && tall ? -AH / 4 : 0;
        clamp(v);
        return px != v->px || py != v->py;
    } else return 0;
    return 1;
}

/* A click: a button, or on a picture larger than the window, that point to the middle. */
COLD static int click(struct view *v, struct line *l, int x, int y) {
    if (y >= AH) {
        for (int i = 0; i < NBUTTON; i++)
            if (x >= buttons[i].x && x < buttons[i].x + buttons[i].w && y >= BTN_Y && y < BTN_Y + BTN_H)
                return key(v, l, (u64)buttons[i].key);
        return 0;
    }
    if (!v->ok || ((long)v->dw <= VW && (long)v->dh <= AH)) return 0;
    if ((long)v->dw > VW) v->px += x - VW / 2;
    if ((long)v->dh > AH) v->py += y - AH / 2;
    clamp(v);
    return 1;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct view *v = (struct view *)DATA;
    struct line l = {.n = 0};
    ui_load(&v->ui, app_assets());
    v->win = app_surface(VW, VH);
    fs_init(&v->fs, SPARE_PAGE);
    v->ngiven = v->nnames = v->cur = v->qn = v->qh = 0;
    v->lo = v->hi = 0;
    gather(v);
    put_s(&l, "view: ");
    put_dec(&l, (u64)v->ngiven);
    put_s(&l, v->ngiven == 1 ? " file given, " : " files given, ");
    put_dec(&l, (u64)v->nnames);
    put_s(&l, v->nnames == 1 ? " picture in " : " pictures in ");
    put_s(&l, v->folder);
    say(&l);
    open_pic(v, &l);
    fill(&v->win, 0, 0, VW, AH, BG);
    bar(v);
    u64 opened = app_open(VW, VH, "View");
    put_s(&l, "view: opened a window");
    put_s(&l, outcome(opened));
    say(&l);
    if (opened != OK) exit_task();

    /* Take every event waiting, then draw once: keys held down, or typed fast, do not each
       draw a picture that the next one replaces. */
    int dirty = 0, want_draw = 1;
    for (;;) {
        struct event e;
        if (v->qn) {
            e = v->q[v->qh];
            v->qh = (v->qh + 1) % QUEUE;
            v->qn--;
        } else {
            e = want_draw ? app_poll(dirty) : app_wait(dirty);
            dirty = 0;
        }
        if (e.kind == EV_NONE) {
            want_draw = draw(v, &l);
            dirty = 1;
            continue;
        }
        if (e.kind == EV_CLOSE) {
            put_s(&l, "view: window closed, exiting");
            say(&l);
            exit_task();
        }
        if (e.kind == EV_KEY) want_draw |= key(v, &l, e.a);
        else if (e.kind == EV_DOWN) want_draw |= click(v, &l, (int)e.a, (int)e.b);
    }
}
