/* The time zone: how far local time is from UTC, in minutes east (+5:30 is 330, -3:30 is
   -210), from -12:00 to +14:00 in quarter hours. The kernel keeps only UTC; the zone is how
   the desktop shows it.

   Settings chooses it and tells the display server (SET, as it does the background; only
   Settings may). The display server keeps it, shows the menu bar's clock in it, and tells
   any program that asks (ZONE): Clock asks every second. It is kept on the card, with the
   background, in settings.txt (user/prefs.h) by Apps, which the display asks to save them,
   and which reads them back when the display starts it at boot; an older card's
   timezone.txt ("UTC+5:30") is read too. A message word cannot carry a negative number, so
   the zone travels as minutes + ZONE_BIAS. */
#pragma once
#include "date.h"

#define ZONE_MIN (-12 * 60)
#define ZONE_MAX (14 * 60)
#define ZONE_BIAS (-ZONE_MIN)
#define ZONE_FILE "timezone.txt"

static inline int zone_ok(long m) { return m >= ZONE_MIN && m <= ZONE_MAX && m % 15 == 0; }

/* A message word to a zone, or 0 (UTC) if it is not one. */
static inline long zone_of_word(u64 w) {
    long m = w <= (u64)(ZONE_MAX + ZONE_BIAS) ? (long)w - ZONE_BIAS : 0;
    return zone_ok(m) ? m : 0;
}

/* Unix seconds as local time: date_of() of this gives the local date and time. */
static inline u64 local_of(u64 wall, long zone) {
    long t = (long)wall + zone * 60;
    return t > 0 ? (u64)t : 0;
}

/* "UTC", "UTC+9", "UTC+5:30", "UTC-3:30" */
static inline void put_zone(struct line *l, long zone) {
    put_s(l, "UTC");
    if (!zone) return;
    put_s(l, zone < 0 ? "-" : "+");
    u64 a = (u64)(zone < 0 ? -zone : zone);
    put_dec(l, a / 60);
    if (a % 60) {
        put_s(l, ":");
        put_two(l, a % 60);
    }
}

/* "2026-01-03 01:30:05": the date and time in the zone. */
static inline void put_local(struct line *l, u64 wall, long zone) {
    struct date d = date_of(local_of(wall, zone));
    put_dec(l, (u64)d.year);
    put_s(l, "-");
    put_two(l, (u64)d.month);
    put_s(l, "-");
    put_two(l, (u64)d.day);
    put_s(l, " ");
    put_two(l, (u64)d.h);
    put_s(l, ":");
    put_two(l, (u64)d.m);
    put_s(l, ":");
    put_two(l, (u64)d.s);
}

/* Reads what put_zone writes (and "+5:30", "-3", or "UTC+05:30"), from the first n bytes of
   s, ignoring spaces around it. Returns 1 and sets *zone if it is a zone. */
static inline int parse_zone(const char *s, long n, long *zone) {
    long i = 0;
    while (i < n && (s[i] == ' ' || s[i] == '\t')) i++;
    int utc = i + 3 <= n && s[i] == 'U' && s[i + 1] == 'T' && s[i + 2] == 'C';
    if (utc) i += 3;
    long sign = 1, h = 0, m = 0, digits = 0;
    if (i < n && (s[i] == '+' || s[i] == '-')) {
        sign = s[i] == '-' ? -1 : 1;
        i++;
        for (; i < n && s[i] >= '0' && s[i] <= '9' && digits < 2; i++, digits++) h = h * 10 + (s[i] - '0');
        if (!digits) return 0;
        if (i < n && s[i] == ':') {
            i++;
            if (i + 2 > n || s[i] < '0' || s[i] > '9' || s[i + 1] < '0' || s[i + 1] > '9') return 0;
            m = (s[i] - '0') * 10 + (s[i + 1] - '0');
            i += 2;
            if (m >= 60) return 0;
        }
    } else if (!utc) return 0;           /* neither "UTC" nor a sign: not a zone */
    while (i < n && (s[i] == ' ' || s[i] == '\t' || s[i] == '\r' || s[i] == '\n')) i++;
    if (i != n) return 0;
    long z = sign * (h * 60 + m);
    if (!zone_ok(z)) return 0;
    *zone = z;
    return 1;
}
