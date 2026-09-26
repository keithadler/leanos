/* The desktop's settings, kept on the card: the time zone (user/zone.h) and the background.

   Settings chooses them and tells the display server (SET), which takes them only from
   Settings' badge. The display cannot write the card, so it asks Apps, which can, to save
   both in settings.txt, one "name value" line each:

       zone UTC+5:30
       background Dawn

   At boot Apps reads it back and gives each to the display, which takes each from Apps only
   that once. A card from before settings.txt keeps the zone alone in timezone.txt
   ("UTC+5:30"): Apps reads that when there is no settings.txt, and removes it once
   settings.txt holds the zone. */
#pragma once
#include "zone.h"

#define PREFS_FILE "settings.txt"
#define NBG 3                    /* the backgrounds, as SET_BACKGROUND numbers them */

static inline const char *bg_name(u64 i) {
    static const char *const names[NBG] = {"Indigo", "Graphite", "Dawn"};
    return i < NBG ? names[i] : "?";
}

/* How many bytes of `w` start s (n bytes), or 0 if s does not start with all of it. */
static inline long prefs_word(const char *s, long n, const char *w) {
    long i = 0;
    for (; w[i]; i++)
        if (i >= n || s[i] != w[i]) return 0;
    return i;
}

/* settings.txt, from the first n bytes of s: each line understood sets *zone or *bg, and its
   bit in the answer (1 the zone, 2 the background). Other lines are skipped. */
static inline int parse_prefs(const char *s, long n, long *zone, int *bg) {
    int got = 0;
    for (long i = 0, e; i < n; i = e + 1) {
        for (e = i; e < n && s[e] != '\n'; e++) {}
        long k, end = e;
        while (end > i && (s[end - 1] == ' ' || s[end - 1] == '\r' || s[end - 1] == '\t')) end--;
        if ((k = prefs_word(s + i, end - i, "zone ")) && parse_zone(s + i + k, end - i - k, zone)) got |= 1;
        if ((k = prefs_word(s + i, end - i, "background ")))
            for (int b = 0; b < NBG; b++)
                if (end - i - k > 0 && prefs_word(s + i + k, end - i - k, bg_name((u64)b)) == end - i - k) {
                    *bg = b;
                    got |= 2;
                }
    }
    return got;
}

/* What parse_prefs reads. */
static inline void put_prefs(struct line *l, long zone, int bg) {
    put_s(l, "zone ");
    put_zone(l, zone);
    put_s(l, "\nbackground ");
    put_s(l, bg_name((u64)bg));
    put_s(l, "\n");
}
