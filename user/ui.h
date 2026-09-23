/* The fonts every program from the SD card finds at the start of its spare run (the kernel
   image's open-slot assets, OPEN_ASSETS in the Makefile), and text laid out with them. */
#pragma once
#include "app.h"

enum { UI_BODY = 1, UI_BOLD = 2, UI_SMALL = 3, UI_TITLE = 4, UI_MEDIUM = 5, UI_MONO = 6,
       UI_HUGE = 7, UI_SMALL_BOLD = 8 };

struct ui {
    struct font body, bold, small, title, medium, mono, huge, small_bold;
};

static inline void ui_load(struct ui *u, const unsigned char *assets) {
    u->body = font_of(assets, UI_BODY);
    u->bold = font_of(assets, UI_BOLD);
    u->small = font_of(assets, UI_SMALL);
    u->title = font_of(assets, UI_TITLE);
    u->medium = font_of(assets, UI_MEDIUM);
    u->mono = font_of(assets, UI_MONO);
    u->huge = font_of(assets, UI_HUGE);
    u->small_bold = font_of(assets, UI_SMALL_BOLD);
}

/* `str` in font `f`, wrapped at word boundaries to `width` pixels, first baseline at y,
   `lh` pixels a line. Returns the baseline after the last line. */
static inline int text_wrap(struct surface *s, const struct font *f, int x, int y, int width, int lh,
                            const char *str, unsigned c) {
    char line[160];
    while (*str) {
        /* take whole words while the line still fits (always at least one word) */
        int end = 0, j = 0;
        for (;;) {
            while (str[j] && str[j] != ' ' && j < 158) j++;
            for (int i = 0; i < j; i++) line[i] = str[i];
            line[j] = 0;
            if (end > 0 && font_width(f, line) > width) break;
            end = j;
            if (!str[j] || j >= 158) break;
            j++;
        }
        for (int i = 0; i < end; i++) line[i] = str[i];
        line[end] = 0;
        font_text(s, f, x, y, line, c);
        y += lh;
        str += end;
        while (*str == ' ') str++;
    }
    return y;
}
