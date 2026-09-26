/* Drawing into 32-bit 0x00RRGGBB surfaces: rectangles, anti-aliased rounded rectangles and
   lines, soft shadows, text, and copying one surface into another. Everything clips to the
   surface's clip rectangle. Integer arithmetic only: user programs have no floating point. */
#pragma once
#include "font.h"

struct surface {
    unsigned *px;
    int w, h;
    int stride;              /* pixels per row */
    int cx0, cy0, cx1, cy1;  /* clip: x in [cx0, cx1), y in [cy0, cy1) */
};

static inline struct surface surface_of(unsigned *px, int w, int h) {
    return (struct surface){px, w, h, w, 0, 0, w, h};
}
static inline void clip_all(struct surface *s) { s->cx0 = 0; s->cy0 = 0; s->cx1 = s->w; s->cy1 = s->h; }
static inline void clip_to(struct surface *s, int x, int y, int w, int h) {
    s->cx0 = x < 0 ? 0 : x;
    s->cy0 = y < 0 ? 0 : y;
    s->cx1 = x + w > s->w ? s->w : x + w;
    s->cy1 = y + h > s->h ? s->h : y + h;
}

static inline unsigned rgb(unsigned r, unsigned g, unsigned b) { return (r << 16) | (g << 8) | b; }

/* a and b blended, t = 0..255 the weight of b. Red and blue are blended together in one
   multiply, green in another; the weight is stretched to 0..256 so 0 gives exactly a and
   255 exactly b, and nothing divides. */
static inline unsigned mix(unsigned a, unsigned b, unsigned t) {
    unsigned u = t + (t >> 7), v = 256 - u;
    unsigned rb = ((a & 0xFF00FFu) * v + (b & 0xFF00FFu) * u) >> 8;
    unsigned g = ((a & 0x00FF00u) * v + (b & 0x00FF00u) * u) >> 8;
    return (rb & 0xFF00FFu) | (g & 0x00FF00u);
}

static inline int inside(const struct surface *s, int x, int y) {
    return x >= s->cx0 && x < s->cx1 && y >= s->cy0 && y < s->cy1;
}

static inline void blend(struct surface *s, int x, int y, unsigned c, unsigned alpha) {
    if (!inside(s, x, y) || alpha == 0) return;
    unsigned *p = s->px + y * s->stride + x;
    *p = alpha >= 255 ? c : mix(*p, c, alpha);
}

static inline void fill(struct surface *s, int x, int y, int w, int h, unsigned c) {
    int x0 = x < s->cx0 ? s->cx0 : x, y0 = y < s->cy0 ? s->cy0 : y;
    int x1 = x + w > s->cx1 ? s->cx1 : x + w, y1 = y + h > s->cy1 ? s->cy1 : y + h;
    for (int j = y0; j < y1; j++) {
        unsigned *row = s->px + j * s->stride;
        for (int i = x0; i < x1; i++) row[i] = c;
    }
}

static inline void fill_alpha(struct surface *s, int x, int y, int w, int h, unsigned c, unsigned alpha) {
    int x0 = x < s->cx0 ? s->cx0 : x, y0 = y < s->cy0 ? s->cy0 : y;
    int x1 = x + w > s->cx1 ? s->cx1 : x + w, y1 = y + h > s->cy1 ? s->cy1 : y + h;
    for (int j = y0; j < y1; j++) {
        unsigned *row = s->px + j * s->stride;
        for (int i = x0; i < x1; i++) row[i] = mix(row[i], c, alpha);
    }
}

/* A vertical gradient from `top` to `bottom`. */
static inline void gradient(struct surface *s, int x, int y, int w, int h, unsigned top, unsigned bottom) {
    for (int j = 0; j < h; j++) fill(s, x, y + j, w, 1, mix(top, bottom, h > 1 ? (unsigned)(j * 255 / (h - 1)) : 0));
}

static inline unsigned isqrt(unsigned v) {
    unsigned r = 0, bit = 1u << 30;
    while (bit > v) bit >>= 2;
    while (bit) {
        if (v >= r + bit) { v -= r + bit; r = (r >> 1) + bit; } else r >>= 1;
        bit >>= 2;
    }
    return r;
}

/* How much of pixel (px, py) a rounded rectangle covers, 0..255: 16x16 subpixel distance
   to the nearest corner circle. */
static inline unsigned round_cover(int px, int py, int x, int y, int w, int h, int r) {
    int cx = px < x + r ? x + r : px >= x + w - r ? x + w - r - 1 : px;
    int cy = py < y + r ? y + r : py >= y + h - r ? y + h - r - 1 : py;
    if (cx == px || cy == py) return 255;
    int dx = (px - cx) * 16, dy = (py - cy) * 16;
    int d = (int)isqrt((unsigned)(dx * dx + dy * dy));
    int cover = r * 16 - d + 8;
    return cover <= 0 ? 0 : cover >= 16 ? 255 : (unsigned)(cover * 255 / 16);
}

/* One row's pixels [i0, i1) of a rounded rectangle, already clipped. */
static inline void round_span(struct surface *s, int j, int i0, int i1, int x, int y, int w, int h, int r,
                              unsigned c, unsigned alpha) {
    unsigned *row = s->px + j * s->stride;
    int corner = j < y + r || j >= y + h - r;
    for (int i = i0; i < i1; i++) {
        unsigned a = alpha;
        if (corner && (i < x + r || i >= x + w - r)) {
            a = (round_cover(i, j, x, y, w, h, r) * alpha + 255) >> 8;
            if (!a) continue;
        }
        row[i] = a >= 255 ? c : mix(row[i], c, a);
    }
}

static inline void round_rect(struct surface *s, int x, int y, int w, int h, int r, unsigned c, unsigned alpha) {
    int x0 = x < s->cx0 ? s->cx0 : x, x1 = x + w > s->cx1 ? s->cx1 : x + w;
    int y0 = y < s->cy0 ? s->cy0 : y, y1 = y + h > s->cy1 ? s->cy1 : y + h;
    if (alpha == 0) return;
    for (int j = y0; j < y1; j++) round_span(s, j, x0, x1, x, y, w, h, r, c, alpha);
}

/* A rounded rectangle whose color runs from `top` to `bottom`. */
static inline void round_gradient(struct surface *s, int x, int y, int w, int h, int r, unsigned top, unsigned bottom) {
    int x0 = x < s->cx0 ? s->cx0 : x, x1 = x + w > s->cx1 ? s->cx1 : x + w;
    int y0 = y < s->cy0 ? s->cy0 : y, y1 = y + h > s->cy1 ? s->cy1 : y + h;
    for (int j = y0; j < y1; j++)
        round_span(s, j, x0, x1, x, y, w, h, r, mix(top, bottom, h > 1 ? (unsigned)((j - y) * 255 / (h - 1)) : 0), 255);
}

/* Darken c: keep `f` of it, f = 0..256. */
static inline unsigned darken(unsigned c, unsigned f) {
    return (((c & 0xFF00FFu) * f >> 8) & 0xFF00FFu) | (((c & 0x00FF00u) * f >> 8) & 0x00FF00u);
}

/* A soft shadow, `drop` pixels lower, under a rounded rectangle (x, y, w, h, r) that is
   drawn over it next. It looks like six black layers of alpha 10, the rectangle grown by
   1 to 6 pixels; but those layers share their corner centers, so how dark a pixel gets
   depends only on its distance to the lowered rectangle. That is worked out once per
   pixel (a square root only in the corners), in one pass, from two small tables. And the
   rectangle hides everything under it but its corners, so that part is skipped: the work
   follows the edge, not the area. The larger table depends only on r: shadow_keep makes
   it once, for every shadow of that radius (keep_e, made for the r it is given with). */
#define SHADOW_KEEP(r) (((r) + 7) * 16 + 1)   /* the table's entries for radius r */
/* keep_e[e]: what the six layers leave at distance e (1/16 px) from a corner's center */
static inline void shadow_keep(unsigned short *keep_e, int r) {
    int emax = (r + 7) * 16;
    for (int e = 0; e <= emax; e++) {
        unsigned f = 256;
        for (int k = 1; k <= 6; k++) {
            int cover = (r + k) * 16 - e + 8;
            unsigned a = cover <= 0 ? 0 : cover >= 16 ? 255 : (unsigned)(cover * 255 / 16);
            unsigned ak = (a * 10 + 255) >> 8;
            f = f * (256 - ak) >> 8;
        }
        keep_e[e] = (unsigned short)f;
    }
}
static inline void shadow(struct surface *s, int x, int y, int w, int h, int r, int drop,
                          const unsigned short *keep_e) {
    int by = y + 4 + drop;                      /* the layers' base: the rectangle, lowered */
    /* keep_n[n]: what n full layers leave of the pixel under them (0..256) */
    unsigned keep_n[8];
    keep_n[0] = 256;
    for (int n = 1; n < 8; n++) keep_n[n] = keep_n[n - 1] * 246 >> 8;
    int emax = (r + 7) * 16;
    int x0 = x - 6 < s->cx0 ? s->cx0 : x - 6, x1 = x + w + 6 > s->cx1 ? s->cx1 : x + w + 6;
    int y0 = by - 6 < s->cy0 ? s->cy0 : by - 6, y1 = by + h + 6 > s->cy1 ? s->cy1 : by + h + 6;
    for (int j = y0; j < y1; j++) {
        unsigned *row = s->px + j * s->stride;
        /* the covered part of this row: all of the rectangle's width away from its top and
           bottom corners, the middle only within them */
        int h0 = x1, h1 = x1;
        if (j >= y && j < y + h) {
            int inset = (j < y + r || j >= y + h - r) ? r : 0;
            h0 = x + inset;
            h1 = x + w - inset;
        }
        int iny = j >= by + r && j < by + h - r;
        int ydist = j < by ? by - j : j >= by + h ? j - (by + h) + 1 : 0;
        int cy = j < by + r ? by + r : by + h - r - 1;
        for (int i = x0; i < x1; i++) {
            if (i >= h0 && i < h1) { i = h1 - 1; continue; }
            int inx = i >= x + r && i < x + w - r;
            unsigned f;
            if (!inx && !iny) {
                int cx = i < x + r ? x + r : x + w - r - 1;
                int dx = (i - cx) * 16, dy = (j - cy) * 16;
                unsigned e = isqrt((unsigned)(dx * dx + dy * dy));
                f = e <= (unsigned)emax ? keep_e[e] : 256;
            } else {
                int dist = inx ? ydist : (i < x ? x - i : i >= x + w ? i - (x + w) + 1 : 0);
                f = dist == 0 ? keep_n[6] : dist <= 6 ? keep_n[7 - dist] : 256;
            }
            if (f < 256) row[i] = darken(row[i], f);
        }
    }
}

/* An anti-aliased line of the given width, by distance from each pixel to the segment
   (coordinates in 1/16 pixel). */
static inline void thick_line(struct surface *s, int x0, int y0, int x1, int y1, int width, unsigned c) {
    int minx = (x0 < x1 ? x0 : x1) / 16 - width, maxx = (x0 > x1 ? x0 : x1) / 16 + width;
    int miny = (y0 < y1 ? y0 : y1) / 16 - width, maxy = (y0 > y1 ? y0 : y1) / 16 + width;
    int dx = x1 - x0, dy = y1 - y0;
    int len2 = dx * dx + dy * dy;
    int half = width * 8;
    for (int py = miny; py <= maxy; py++)
        for (int px = minx; px <= maxx; px++) {
            int qx = px * 16 + 8 - x0, qy = py * 16 + 8 - y0;
            int t = len2 ? (qx * dx + qy * dy) : 0;
            int ex, ey;
            if (t <= 0) { ex = qx; ey = qy; }
            else if (t >= len2) { ex = qx - dx; ey = qy - dy; }
            else {
                /* distance to the line: |cross| / length */
                int cross = qx * dy - qy * dx;
                if (cross < 0) cross = -cross;
                int d = cross / (int)isqrt((unsigned)len2);
                int cover = half - d + 8;
                blend(s, px, py, c, cover <= 0 ? 0 : cover >= 16 ? 255 : (unsigned)(cover * 255 / 16));
                continue;
            }
            int d = (int)isqrt((unsigned)(ex * ex + ey * ey));
            int cover = half - d + 8;
            blend(s, px, py, c, cover <= 0 ? 0 : cover >= 16 ? 255 : (unsigned)(cover * 255 / 16));
        }
}

/* An anti-aliased circle outline centered at (cx, cy), radius r, `width` pixels thick. */
static inline void ring(struct surface *s, int cx, int cy, int r, int width, unsigned c) {
    for (int y = cy - r - 2; y <= cy + r + 2; y++)
        for (int x = cx - r - 2; x <= cx + r + 2; x++) {
            int dx = (x - cx) * 16, dy = (y - cy) * 16;
            int d = (int)isqrt((unsigned)(dx * dx + dy * dy));
            int off = d - r * 16;
            if (off < 0) off = -off;
            int cover = width * 8 - off + 8;
            blend(s, x, y, c, cover <= 0 ? 0 : cover >= 16 ? 255 : (unsigned)(cover * 255 / 16));
        }
}

/* Text in the 5x7 font, each font pixel `scale` screen pixels; a character cell is
   6 x 8 font pixels. Returns the x after the last character. */
static inline int text(struct surface *s, int x, int y, const char *str, unsigned c, int scale) {
    for (; *str; str++, x += 6 * scale) {
        unsigned ch = (unsigned char)*str;
        if (ch < 32 || ch > 126) ch = '?';
        const unsigned char *g = font5x7[ch - 32];
        for (int row = 0; row < 7; row++)
            for (int col = 0; col < 5; col++)
                if (g[row] & (16 >> col)) fill(s, x + col * scale, y + row * scale, scale, scale, c);
    }
    return x;
}

static inline int text_width(const char *str, int scale) {
    int n = 0;
    while (str[n]) n++;
    return n ? n * 6 * scale - scale : 0;
}

/* The copyright sign, as tall as a line of text at `scale`: a ring with a c in it.
   Returns the x after it. */
static inline int copyright_sign(struct surface *s, int x, int y, unsigned c, int scale) {
    int size = 7 * scale;
    ring(s, x + size / 2, y + size / 2, size / 2, scale > 1 ? scale / 2 + 1 : 1, c);
    int cs = scale > 2 ? scale / 2 : 1;
    text(s, x + size / 2 - (5 * cs) / 2, y + size / 2 - (7 * cs) / 2, "c", c, cs);
    return x + size + 2 * scale;
}

/* Copy `src` into `dst` with its top-left corner at (x, y), clipped to `dst`'s clip. */
static inline void blit(struct surface *dst, int x, int y, const struct surface *src) {
    int x0 = x < dst->cx0 ? dst->cx0 : x, y0 = y < dst->cy0 ? dst->cy0 : y;
    int x1 = x + src->w > dst->cx1 ? dst->cx1 : x + src->w;
    int y1 = y + src->h > dst->cy1 ? dst->cy1 : y + src->h;
    for (int j = y0; j < y1; j++) {
        const unsigned *from = src->px + (j - y) * src->stride + (x0 - x);
        unsigned *to = dst->px + j * dst->stride;
        for (int i = x0; i < x1; i++) to[i] = *from++;
    }
}

/* Copy `src` to (x, y), rounding off the corners that fall outside the rounded rectangle
   (fx, fy, fw, fh, r): those pixels are blended by how much of them the shape covers. */
static inline void blit_rounded(struct surface *dst, int x, int y, const struct surface *src,
                                int fx, int fy, int fw, int fh, int r) {
    int x0 = x < dst->cx0 ? dst->cx0 : x, y0 = y < dst->cy0 ? dst->cy0 : y;
    int x1 = x + src->w > dst->cx1 ? dst->cx1 : x + src->w;
    int y1 = y + src->h > dst->cy1 ? dst->cy1 : y + src->h;
    for (int j = y0; j < y1; j++) {
        const unsigned *from = src->px + (j - y) * src->stride;
        unsigned *to = dst->px + j * dst->stride;
        int corner_row = j < fy + r || j >= fy + fh - r;
        for (int i = x0; i < x1; i++) {
            unsigned c = from[i - x];
            if (corner_row && (i < fx + r || i >= fx + fw - r)) {
                unsigned a = round_cover(i, j, fx, fy, fw, fh, r);
                if (a) to[i] = a >= 255 ? c : mix(to[i], c, a);
            } else {
                to[i] = c;
            }
        }
    }
}

/* The mouse pointer: an arrow, 12 x 19, '#' outline, '.' fill. */
static const char *const pointer_art[19] = {
    "#           ", "##          ", "#.#         ", "#..#        ", "#...#       ",
    "#....#      ", "#.....#     ", "#......#    ", "#.......#   ", "#........#  ",
    "#.........# ", "#..........#", "#......#####", "#...#..#    ", "#..# #..#   ",
    "#.#  #..#   ", "##    #..#  ", "      #..#  ", "       ##   ",
};

static inline void pointer(struct surface *s, int x, int y) {
    for (int j = 0; j < 19; j++)
        for (int i = 0; i < 12; i++) {
            char c = pointer_art[j][i];
            if (c == '#') blend(s, x + i, y + j, rgb(20, 20, 24), 255);
            else if (c == '.') blend(s, x + i, y + j, rgb(255, 255, 255), 255);
        }
}
