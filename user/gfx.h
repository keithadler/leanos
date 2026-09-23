/* Drawing into 32-bit 0x00RRGGBB surfaces: rectangles, text, and copying one surface into
   another. Everything clips to the destination. */
#pragma once
#include "font.h"

struct surface {
    unsigned *px;
    int w, h;
    int stride; /* pixels per row */
};

static inline unsigned rgb(unsigned r, unsigned g, unsigned b) { return (r << 16) | (g << 8) | b; }

static inline void fill(struct surface *s, int x, int y, int w, int h, unsigned c) {
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > s->w) w = s->w - x;
    if (y + h > s->h) h = s->h - y;
    for (int j = 0; j < h; j++) {
        unsigned *row = s->px + (y + j) * s->stride + x;
        for (int i = 0; i < w; i++) row[i] = c;
    }
}

/* A vertical gradient from `top` to `bottom`. */
static inline void gradient(struct surface *s, int x, int y, int w, int h, unsigned top, unsigned bottom) {
    for (int j = 0; j < h; j++) {
        unsigned t = h > 1 ? (unsigned)(j * 255 / (h - 1)) : 0;
        unsigned r = (((top >> 16) & 255) * (255 - t) + ((bottom >> 16) & 255) * t) / 255;
        unsigned g = (((top >> 8) & 255) * (255 - t) + ((bottom >> 8) & 255) * t) / 255;
        unsigned b = ((top & 255) * (255 - t) + (bottom & 255) * t) / 255;
        fill(s, x, y + j, w, 1, rgb(r, g, b));
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
    return n * 6 * scale - scale;
}

/* Copy `src` into `dst` with its top-left corner at (x, y). */
static inline void blit(struct surface *dst, int x, int y, const struct surface *src) {
    for (int j = 0; j < src->h; j++) {
        int dy = y + j;
        if (dy < 0 || dy >= dst->h) continue;
        for (int i = 0; i < src->w; i++) {
            int dx = x + i;
            if (dx < 0 || dx >= dst->w) continue;
            dst->px[dy * dst->stride + dx] = src->px[j * src->stride + i];
        }
    }
}
