/* Dates from Unix seconds (UTC): the civil calendar, by Howard Hinnant's days-from-civil
   algorithm run backward. No time zones yet: leanos keeps and shows UTC. */
#pragma once
#include "lib.h"

struct date { int year, month, day, weekday, h, m, s; };   /* month 1-12, weekday 0 = Sunday */

static inline struct date date_of(u64 t) {
    struct date d;
    long days = (long)(t / 86400);
    u64 r = t % 86400;
    d.h = (int)(r / 3600);
    d.m = (int)(r / 60 % 60);
    d.s = (int)(r % 60);
    d.weekday = (int)((days + 4) % 7);                    /* 1970-01-01 was a Thursday */
    long z = days + 719468, era = z / 146097;
    long doe = z - era * 146097;
    long yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    long doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    long mp = (5 * doy + 2) / 153;
    d.day = (int)(doy - (153 * mp + 2) / 5 + 1);
    d.month = (int)(mp < 10 ? mp + 3 : mp - 9);
    d.year = (int)(yoe + era * 400 + (d.month <= 2));
    return d;
}

static const char *const month_names[12] = {"January", "February", "March", "April", "May", "June", "July",
                                            "August", "September", "October", "November", "December"};
static const char *const day_names[7] = {"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"};

static inline void put_two(struct line *l, u64 v) {
    if (v < 10) put_s(l, "0");
    put_dec(l, v);
}

/* 2026-09-23 14:05:09 UTC */
static inline void put_date(struct line *l, u64 t) {
    struct date d = date_of(t);
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
    put_s(l, " UTC");
}
