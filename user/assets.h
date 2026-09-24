/* Reading a task's asset blob (built by tools/mkassets.py): fonts, icons, pictures. The
   machine layer copies the blob to the start of the task's spare run at boot; a task maps
   the run and passes its address here. */
#pragma once
#include "gfx.h"

enum { ASSET_FONT = 1, ASSET_ICON = 2, ASSET_IMAGE = 3 };

struct glyph {
    unsigned cp;
    int advance;            /* 1/64 pixel */
    unsigned short w, h;
    short left, top;        /* from the pen position, top above the baseline */
    unsigned offset;
};

struct font {
    unsigned px, ascent, descent, line, count;
    const struct glyph *glyphs;
    const unsigned char *coverage;
};

struct picture {
    int w, h;
    const unsigned *px;
};

static inline const unsigned char *asset_find(const unsigned char *blob, unsigned kind, unsigned id) {
    const unsigned *h = (const unsigned *)blob;
    if (h[0] != 0x53414e4c /* "LNAS" */) return 0;
    for (unsigned i = 0; i < h[2]; i++) {
        const unsigned *e = h + 3 + 4 * i;
        if (e[0] == kind && e[1] == id) return blob + e[2];
    }
    return 0;
}

static inline struct font font_of(const unsigned char *blob, unsigned id) {
    const unsigned *f = (const unsigned *)asset_find(blob, ASSET_FONT, id);
    struct font out = {0};
    if (!f) return out;
    out.px = f[0];
    out.ascent = f[1];
    out.descent = f[2];
    out.line = f[3];
    out.count = f[4];
    out.glyphs = (const struct glyph *)(f + 5);
    out.coverage = (const unsigned char *)(out.glyphs + out.count);
    return out;
}

static inline struct picture picture_of(const unsigned char *blob, unsigned kind, unsigned id) {
    const unsigned *p = (const unsigned *)asset_find(blob, kind, id);
    struct picture out = {0, 0, 0};
    if (p) { out.w = (int)p[0]; out.h = (int)p[1]; out.px = p + 2; }
    return out;
}

/* The next character of a UTF-8 string. */
static inline unsigned utf8_next(const char **s) {
    const unsigned char *p = (const unsigned char *)*s;
    unsigned c = *p++;
    if (c >= 0xE0 && p[0] && p[1]) { c = ((c & 15) << 12) | ((p[0] & 63) << 6) | (p[1] & 63); p += 2; }
    else if (c >= 0xC0 && p[0]) { c = ((c & 31) << 6) | (p[0] & 63); p += 1; }
    *s = (const char *)p;
    return c;
}

static inline const struct glyph *glyph_of(const struct font *f, unsigned cp) {
    if (cp >= 32 && cp < 127 && cp - 32 < f->count) return &f->glyphs[cp - 32];
    for (unsigned i = 95; i < f->count; i++) if (f->glyphs[i].cp == cp) return &f->glyphs[i];
    return &f->glyphs['?' - 32];
}

/* Text with its baseline at y. Returns the pen position after it. */
static inline int font_text(struct surface *s, const struct font *f, int x, int y, const char *str, unsigned c) {
    if (!f->glyphs) return x;
    int pen = x * 64;
    while (*str) {
        const struct glyph *g = glyph_of(f, utf8_next(&str));
        int gx = pen / 64 + g->left, gy = y - g->top;
        const unsigned char *cov = f->coverage + g->offset;
        /* only the part of the glyph inside the clip */
        int j0 = s->cy0 - gy > 0 ? s->cy0 - gy : 0, j1 = s->cy1 - gy < g->h ? s->cy1 - gy : g->h;
        int i0 = s->cx0 - gx > 0 ? s->cx0 - gx : 0, i1 = s->cx1 - gx < g->w ? s->cx1 - gx : g->w;
        for (int j = j0; j < j1; j++) {
            unsigned *row = s->px + (gy + j) * s->stride + gx;
            for (int i = i0; i < i1; i++) {
                unsigned a = cov[j * g->w + i];
                if (a) row[i] = a >= 255 ? c : mix(row[i], c, a);
            }
        }
        pen += g->advance;
    }
    return pen / 64;
}

static inline int font_width(const struct font *f, const char *str) {
    if (!f->glyphs) return 0;
    int pen = 0;
    while (*str) pen += glyph_of(f, utf8_next(&str))->advance;
    return pen / 64;
}

/* An icon with premultiplied alpha, top-left at (x, y). */
static inline void icon(struct surface *s, int x, int y, const struct picture *p) {
    int j0 = s->cy0 - y > 0 ? s->cy0 - y : 0, j1 = s->cy1 - y < p->h ? s->cy1 - y : p->h;
    int i0 = s->cx0 - x > 0 ? s->cx0 - x : 0, i1 = s->cx1 - x < p->w ? s->cx1 - x : p->w;
    for (int j = j0; j < j1; j++) {
        int dy = y + j;
        for (int i = i0; i < i1; i++) {
            int dx = x + i;
            unsigned v = p->px[j * p->w + i], a = v >> 24;
            if (!a) continue;
            unsigned *d = s->px + dy * s->stride + dx;
            unsigned inv = 255 - a;
            unsigned r = ((v >> 16) & 255) + ((*d >> 16) & 255) * inv / 255;
            unsigned g = ((v >> 8) & 255) + ((*d >> 8) & 255) * inv / 255;
            unsigned b = (v & 255) + (*d & 255) * inv / 255;
            *d = rgb(r > 255 ? 255 : r, g > 255 ? 255 : g, b > 255 ? 255 : b);
        }
    }
}

/* An icon drawn `size` pixels square at (x, y): each pixel the average of the source
   pixels it covers (premultiplied, so edges stay clean). */
static inline void icon_scaled(struct surface *s, int x, int y, int size, const struct picture *p) {
    if (!p->px || size <= 0) return;
    int j0 = s->cy0 - y > 0 ? s->cy0 - y : 0, j1 = s->cy1 - y < size ? s->cy1 - y : size;
    int i0 = s->cx0 - x > 0 ? s->cx0 - x : 0, i1 = s->cx1 - x < size ? s->cx1 - x : size;
    for (int j = j0; j < j1; j++) {
        int dy = y + j;
        int sy0 = j * p->h / size, sy1 = (j + 1) * p->h / size;
        if (sy1 <= sy0) sy1 = sy0 + 1;
        for (int i = i0; i < i1; i++) {
            int dx = x + i;
            int sx0 = i * p->w / size, sx1 = (i + 1) * p->w / size;
            if (sx1 <= sx0) sx1 = sx0 + 1;
            unsigned a = 0, r = 0, g = 0, b = 0, n = 0;
            for (int yy = sy0; yy < sy1; yy++)
                for (int xx = sx0; xx < sx1; xx++) {
                    unsigned v = p->px[yy * p->w + xx];
                    a += v >> 24;
                    r += (v >> 16) & 255;
                    g += (v >> 8) & 255;
                    b += v & 255;
                    n++;
                }
            a /= n; r /= n; g /= n; b /= n;
            if (!a) continue;
            unsigned *d = s->px + dy * s->stride + dx;
            unsigned inv = 255 - a;
            unsigned rr = r + ((*d >> 16) & 255) * inv / 255;
            unsigned gg = g + ((*d >> 8) & 255) * inv / 255;
            unsigned bb = b + (*d & 255) * inv / 255;
            *d = rgb(rr > 255 ? 255 : rr, gg > 255 ? 255 : gg, bb > 255 ? 255 : bb);
        }
    }
}

/* A picture stretched over the whole surface, smoothly (bilinear), for the clipped part. */
static inline void stretch(struct surface *s, const struct picture *p) {
    if (!p->px) return;
    for (int y = s->cy0; y < s->cy1; y++) {
        /* source position in 1/256 pixel, at pixel centers */
        int sy = (int)(((2 * y + 1) * p->h * 128) / s->h) - 128;
        if (sy < 0) sy = 0;
        int y0 = sy >> 8, fy = sy & 255;
        int y1 = y0 + 1 < p->h ? y0 + 1 : y0;
        const unsigned *r0 = p->px + y0 * p->w, *r1 = p->px + y1 * p->w;
        unsigned *row = s->px + y * s->stride;
        for (int x = s->cx0; x < s->cx1; x++) {
            int sx = (int)(((2 * x + 1) * p->w * 128) / s->w) - 128;
            if (sx < 0) sx = 0;
            int x0 = sx >> 8, fx = sx & 255;
            int x1 = x0 + 1 < p->w ? x0 + 1 : x0;
            unsigned top = mix(r0[x0], r0[x1], (unsigned)fx), bottom = mix(r1[x0], r1[x1], (unsigned)fx);
            row[x] = mix(top, bottom, (unsigned)fy);
        }
    }
}
