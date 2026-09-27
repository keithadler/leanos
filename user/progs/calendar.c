/* calendar: a month at a time, and what is on each day. The month is a grid of weeks, Monday
   first (as ISO 8601 has it, the way the dates in its file are written), with the days of the
   months before and after it dimmed; today is the blue one. Select a day, with a click or the
   keys, and the panel on the right lists its events.

   Left, Right       a day back or on            Home, End   the month's first or last day
   Up, Down          a week back or on           T           today
   Page Up, Down     a month (the same day, or the month's last if it is shorter)
   Return or N       a new event on the day: type a line, Return keeps it, Escape cancels
   Tab               picks the day's events in turn; Delete (or Backspace) deletes the one picked
   The buttons at the top go a month back, a month on and to today. A click on an event picks
   it, and its x deletes it; New event starts one. A click anywhere else stops the typing.

   Today is the kernel's time of day (`time`, system call 22) in the time zone chosen in
   Settings, which the display server tells anyone who asks (ZONE): both exactly as Clock gets
   them, and asked again every second, so a new zone, midnight, or the time server's first
   answer shows at once. The Pi has no clock that runs while it is off: until a time server
   has answered, the kernel does not know the date and has no guess at it. Then the calendar
   says "the date is not set", starts at January 2026, and goes to today as soon as it is
   known.

   The events are kept in apps/calendar/events.txt, in its own folder, as plain text, one to a
   line, sorted by date (a day's in the order they were added):

       2027-12-30 Dentist at 9:30

   It is read at start: lines that are not an event are skipped (and said, and left out the
   next time it is written), and an event's text is cut at 80 characters. It is written whole
   after each change, in one request, which the file server makes one journaled change: after
   a power cut the file is as it was before the change or after it, never half of each (as
   edit saves). So it holds what one request does, 16 KiB, and at most 200 events; a day
   takes a new one while it has fewer than 7 (the panel shows 7). If the file holds more, or
   cannot be read, the calendar shows what it could read and writes nothing, so it never
   loses what it did not take in. */
#include "../ui.h"
#include "../fs.h"
#include "../zone.h"

/* All of it runs when a key or a click comes, or once a second: compiled for size, as Clock
   is, but for the drawing of text, rounded rectangles and lines, the part that loops over
   pixels. */
#define COLD __attribute__((cold, minsize))

#define CW 592
#define CH 276               /* 160 pages of pixels: the spare run's last 4 are the file buffer */
#define PATH "apps/calendar/events.txt"
#define TEXT_MAX 80          /* bytes of an event's text */
#define ITEMS_MAX 200
#define ROWS 7               /* the events of a day, as many as the panel shows */
#define UNSET_YEAR 2026      /* January of it, while the date is not set */

/* the month: the title between the arrows, the weekdays' names, then 6 weeks of 7 days */
#define GX 14
#define GY 70
#define CELL_W 46
#define CELL_H 32
#define BTN_Y 14
#define BTN_H 26
#define ARROW_W 30
#define PREV_X GX
#define NEXT_X (GX + 7 * CELL_W - ARROW_W)
/* the panel: the day selected, the Today button, its events, and New event (or the line
   being typed) */
#define PX 350
#define TODAY_X (CW - 14 - 56)
#define TODAY_W 56
#define ROW_X (PX + 10)
#define ROW_W (CW - 10 - ROW_X)
#define ROW_Y 74
#define ROW_H 22
#define DEL_W 26             /* an event's x, at the right of its row */
#define ADD_Y 238
#define ADD_H 26

#define BG rgb(252, 252, 253)
#define PANEL rgb(242, 243, 247)
#define INK rgb(36, 38, 46)
#define GRAY rgb(120, 124, 138)
#define DIM rgb(184, 188, 200)
#define ACCENT rgb(58, 110, 230)
#define SEL rgb(222, 231, 252)
#define BUTTON rgb(228, 230, 237)
#define DOT rgb(236, 128, 52)
#define WARN rgb(190, 104, 16)

/* An event: its day, and a line of text (not `struct event`, which is the display's). */
struct item {
    int y, m, d;
    char text[TEXT_MAX + 1];
};

struct cal {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    struct line l;
    struct item items[ITEMS_MAX];
    int n;
    int y, m, d;             /* the day selected; its month is the one shown (0: none yet) */
    int ty, tm, td;          /* today, in the zone (ty 0: the date is not set) */
    int pick;                /* the day's event picked (Tab, a click), -1 none */
    int typing;              /* a new event is being typed, into `input` */
    char input[TEXT_MAX + 1];
    int ilen;
    int writable;            /* events.txt was read whole, or is new: writing it loses nothing */
    const char *note;        /* what went wrong with the last thing done, until the next */
};

COLD static void say(struct cal *c) {
    put_s(&c->l, "\n");
    flush(&c->l);
}

/* "2027-12-30" into out (10 bytes), the year with 4 digits */
COLD static int ymd(char *out, int y, int m, int d) {
    int v[3] = {y, m, d}, w[3] = {4, 2, 2}, n = 0;
    for (int k = 0; k < 3; k++) {
        if (k) out[n++] = '-';
        for (int i = w[k] - 1, x = v[k]; i >= 0; i--, x /= 10) out[n + i] = (char)('0' + x % 10);
        n += w[k];
    }
    return n;
}
COLD static void put_ymd(struct line *l, int y, int m, int d) {
    char t[11];
    t[ymd(t, y, m, d)] = 0;
    put_s(l, t);
}

COLD static long key_of(const struct item *it) { return days_of(it->y, it->m, it->d); }
COLD static int same(int y, int m, int d, int y2, int m2, int d2) { return y == y2 && m == m2 && d == d2; }

/* The selected day's events: the first one's index, and how many (they are together). */
COLD static int day_items(struct cal *c, int *first) {
    long k = days_of(c->y, c->m, c->d);
    int i = 0;
    while (i < c->n && key_of(&c->items[i]) < k) i++;
    *first = i;
    int n = 0;
    while (i + n < c->n && key_of(&c->items[i + n]) == k) n++;
    return n;
}

/* The grid: the 1st of the month is in column (its weekday, from Monday), of the first week. */
COLD static int first_col(int y, int m) { return (weekday_of(days_of(y, m, 1)) + 6) % 7; }

/* The day in cell `i` (0-41) of the month shown. */
COLD static void cell_date(struct cal *c, int i, int *y, int *m, int *d) {
    *y = c->y;
    *m = c->m;
    *d = i - first_col(c->y, c->m) + 1;
    if (*d < 1) {
        if (--*m < 1) { *m = 12; --*y; }
        *d += month_days(*y, *m);
    } else if (*d > month_days(*y, *m)) {
        *d -= month_days(*y, *m);
        if (++*m > 12) { *m = 1; ++*y; }
    }
}

/* Select a day (years 1 to 9999): its month is shown, and nothing of it picked. */
COLD static void select_day(struct cal *c, int y, int m, int d) {
    if (y < 1 || y > 9999) return;
    if (y != c->y || m != c->m) {
        put_s(&c->l, "calendar: showing ");
        put_s(&c->l, month_names[m - 1]);
        put_s(&c->l, " ");
        put_dec(&c->l, (u64)y);
        put_s(&c->l, ", ");
        put_dec(&c->l, (u64)month_days(y, m));
        put_s(&c->l, " days from a ");
        put_s(&c->l, day_names[weekday_of(days_of(y, m, 1))]);
        say(c);
    }
    if (same(y, m, d, c->y, c->m, c->d)) return;
    c->y = y;
    c->m = m;
    c->d = d;
    c->pick = -1;
    put_s(&c->l, "calendar: selected ");
    put_ymd(&c->l, y, m, d);
    say(c);
}

/* n days back or on (a week at most). */
COLD static void go_days(struct cal *c, int n) {
    int y = c->y, m = c->m, d = c->d + n;
    if (d < 1) {
        if (--m < 1) { m = 12; y--; }
        d += month_days(y, m);
    } else if (d > month_days(y, m)) {
        d -= month_days(y, m);
        if (++m > 12) { m = 1; y++; }
    }
    select_day(c, y, m, d);
}

/* A month back (-1) or on (1): the same day, or the month's last if it is shorter. */
COLD static void go_month(struct cal *c, int n) {
    int y = c->y, m = c->m + n;
    if (m < 1) { m = 12; y--; }
    if (m > 12) { m = 1; y++; }
    if (y < 1 || y > 9999) return;
    select_day(c, y, m, c->d < month_days(y, m) ? c->d : month_days(y, m));
}

COLD static void go_today(struct cal *c) {
    if (!c->ty) {
        c->note = "the date is not set";
        return;
    }
    select_day(c, c->ty, c->tm, c->td);
}

/* The file, as it is kept: into the file buffer's data area, which fs_write sends as it is.
   Returns its length. */
COLD static long file_text(struct cal *c, char *out) {
    long n = 0;
    for (int i = 0; i < c->n; i++) {
        const struct item *it = &c->items[i];
        n += ymd(out + n, it->y, it->m, it->d);
        out[n++] = ' ';
        for (int k = 0; it->text[k]; k++) out[n++] = it->text[k];
        out[n++] = '\n';
    }
    return n;
}
COLD static long file_bytes(struct cal *c) {
    long n = 0;
    for (int i = 0; i < c->n; i++) n += 12 + (long)slen(c->items[i].text);
    return n;
}

COLD static void save(struct cal *c) {
    if (!c->writable) {
        c->note = "events.txt was not read whole: not saved";
        put_s(&c->l, "calendar: not saved: " PATH " was not read whole");
        say(c);
        return;
    }
    char *out = (char *)fs_data(&c->fs);
    long n = file_text(c, out);
    u64 st = fs_write(&c->fs, PATH, out, (u64)n);
    if (st != FS_OK) c->note = st == FS_DENIED ? "not given its folder: not saved" : "could not save";
    put_s(&c->l, "calendar: saved ");
    put_dec(&c->l, (u64)c->n);
    put_s(&c->l, c->n == 1 ? " event in " PATH " (" : " events in " PATH " (");
    put_dec(&c->l, (u64)n);
    put_s(&c->l, st == FS_OK ? " bytes) -> ok" : " bytes) -> refused");
    say(c);
}

/* A new event, after the day's others (items stay sorted by day, each day's in order). */
COLD static int insert(struct cal *c, const struct item *it) {
    if (c->n >= ITEMS_MAX) return 0;
    long k = key_of(it);
    int at = c->n;
    while (at > 0 && key_of(&c->items[at - 1]) > k) at--;
    for (int i = c->n; i > at; i--) c->items[i] = c->items[i - 1];
    c->items[at] = *it;
    c->n++;
    return 1;
}

COLD static void log_item(struct cal *c, const char *what, const struct item *it) {
    put_s(&c->l, what);
    put_ymd(&c->l, it->y, it->m, it->d);
    put_s(&c->l, ": ");
    put_s(&c->l, it->text);
    say(c);
}

/* Return or N: start typing a new event, if the day and the file have room for one. */
COLD static void start_typing(struct cal *c) {
    int first;
    if (day_items(c, &first) >= ROWS) c->note = "a day holds 7 events";
    else if (c->n >= ITEMS_MAX || file_bytes(c) + 13 > FS_CHUNK) c->note = "the calendar is full";
    else {
        c->typing = 1;
        c->ilen = 0;
        c->pick = -1;
        put_s(&c->l, "calendar: typing an event for ");
        put_ymd(&c->l, c->y, c->m, c->d);
        say(c);
    }
}

COLD static void stop_typing(struct cal *c, const char *why) {
    c->typing = 0;
    put_s(&c->l, "calendar: no event added (");
    put_s(&c->l, why);
    put_s(&c->l, ")");
    say(c);
}

/* Return: the line typed becomes an event, if it fits (spaces at its ends go). */
COLD static void keep(struct cal *c) {
    int a = 0, b = c->ilen;
    while (a < b && c->input[a] == ' ') a++;
    while (b > a && c->input[b - 1] == ' ') b--;
    if (a == b) {
        stop_typing(c, "nothing typed");
        return;
    }
    c->typing = 0;
    struct item it = {c->y, c->m, c->d, {0}};
    for (int i = a; i < b; i++) it.text[i - a] = c->input[i];
    if (file_bytes(c) + 12 + (b - a) > FS_CHUNK || !insert(c, &it)) {
        c->note = "the calendar is full";
        return;
    }
    log_item(c, "calendar: added an event on ", &it);
    save(c);
}

/* Delete the day's event number `k`. */
COLD static void delete(struct cal *c, int k) {
    int first, n = day_items(c, &first);
    if (k < 0 || k >= n) return;
    struct item gone = c->items[first + k];
    for (int i = first + k; i < c->n - 1; i++) c->items[i] = c->items[i + 1];
    c->n--;
    c->pick = n - 1 == 0 ? -1 : k < n - 1 ? k : k - 1;
    log_item(c, "calendar: deleted an event on ", &gone);
    save(c);
}

/* A key while typing: into the line, or Return, Escape, Backspace. */
COLD static void type_key(struct cal *c, u64 k) {
    if (k == 27) stop_typing(c, "Escape");
    else if (k == '\r' || k == '\n') keep(c);
    else if (k == 127 || k == 8) {
        if (c->ilen) c->ilen--;
    } else if (k >= 32 && k < 127 && c->ilen < TEXT_MAX) c->input[c->ilen++] = (char)k;
}

COLD static void key(struct cal *c, u64 k) {
    c->note = 0;
    if (c->typing) {
        type_key(c, k);
        return;
    }
    int first, n = day_items(c, &first);
    u64 lower = k >= 'A' && k <= 'Z' ? k + 32 : k;
    if (k == KEY_LEFT || k == KEY_RIGHT) go_days(c, k == KEY_LEFT ? -1 : 1);
    else if (k == KEY_UP || k == KEY_DOWN) go_days(c, k == KEY_UP ? -7 : 7);
    else if (k == KEY_PGUP || k == KEY_PGDN) go_month(c, k == KEY_PGUP ? -1 : 1);
    else if (k == KEY_HOME) select_day(c, c->y, c->m, 1);
    else if (k == KEY_END) select_day(c, c->y, c->m, month_days(c->y, c->m));
    else if (lower == 't') go_today(c);
    else if (k == '\r' || k == '\n' || lower == 'n') start_typing(c);
    else if (k == '\t' && n) c->pick = c->pick + 1 < n ? c->pick + 1 : -1;
    else if ((k == KEY_DELETE || k == 127 || k == 8) && c->pick >= 0) delete(c, c->pick);
    else if (k == 27) c->pick = -1;
}

COLD static int in(int x, int y, int bx, int by, int bw, int bh) {
    return x >= bx && x < bx + bw && y >= by && y < by + bh;
}

COLD static void click(struct cal *c, int x, int y) {
    c->note = 0;
    if (c->typing) {
        if (in(x, y, ROW_X, ADD_Y, ROW_W, ADD_H)) return;      /* in the line being typed */
        stop_typing(c, "a click elsewhere");
    }
    if (in(x, y, PREV_X, BTN_Y, ARROW_W, BTN_H)) go_month(c, -1);
    else if (in(x, y, NEXT_X, BTN_Y, ARROW_W, BTN_H)) go_month(c, 1);
    else if (in(x, y, TODAY_X, BTN_Y, TODAY_W, BTN_H)) go_today(c);
    else if (in(x, y, GX, GY, 7 * CELL_W, 6 * CELL_H)) {
        int cy, cm, cd;
        cell_date(c, (y - GY) / CELL_H * 7 + (x - GX) / CELL_W, &cy, &cm, &cd);
        select_day(c, cy, cm, cd);
    } else if (in(x, y, ROW_X, ROW_Y, ROW_W, ROWS * ROW_H)) {
        int first, n = day_items(c, &first), r = (y - ROW_Y) / ROW_H;
        if (r >= n) return;
        if (x >= ROW_X + ROW_W - DEL_W) {
            delete(c, r);
            c->pick = -1;
        } else c->pick = r;
    } else if (in(x, y, ROW_X, ADD_Y, ROW_W, ADD_H)) start_typing(c);
}

/* A paste, while typing: its printable characters, into the line. */
COLD static void paste(struct cal *c, struct event e) {
    char piece[16];
    int k = paste_text(e, piece);
    for (int i = 0; i < k && c->ilen < TEXT_MAX; i++)
        if (piece[i] >= 32 && piece[i] < 127) c->input[c->ilen++] = piece[i];
}

/* What the kernel says the date is, in the zone: asked every second. A change is shown at
   once; the first time the date is known, or at midnight if today was selected, the
   selection goes to today (not while an event is being typed for the day selected). */
COLD static int check_today(struct cal *c) {
    u64 wall = sys0(SYS_TIME).x[6];
    long zone = app_zone();
    int y = 0, m = 0, d = 0;
    if (wall) {
        struct date t = date_of(local_of(wall, zone));
        y = t.year;
        m = t.month;
        d = t.day;
    }
    if (same(y, m, d, c->ty, c->tm, c->td)) return 0;
    int was = c->ty, on_today = same(c->y, c->m, c->d, c->ty, c->tm, c->td);
    c->ty = y;
    c->tm = m;
    c->td = d;
    if (!y) return 1;
    put_s(&c->l, "calendar: today is ");
    put_ymd(&c->l, y, m, d);
    put_s(&c->l, " in ");
    put_zone(&c->l, zone);
    say(c);
    if (!c->typing && (!was || on_today)) select_day(c, y, m, d);
    return 1;
}

/* Read events.txt, skipping lines that are not an event. */
COLD static int digits(const char *s, int n, int *v) {
    *v = 0;
    for (int i = 0; i < n; i++) {
        if (s[i] < '0' || s[i] > '9') return 0;
        *v = *v * 10 + (s[i] - '0');
    }
    return 1;
}
COLD static int parse(const char *s, long n, struct item *it) {
    while (n > 0 && (s[n - 1] == '\r' || s[n - 1] == ' ' || s[n - 1] == '\t')) n--;
    if (n < 12 || !digits(s, 4, &it->y) || s[4] != '-' || !digits(s + 5, 2, &it->m) || s[7] != '-' ||
        !digits(s + 8, 2, &it->d) || s[10] != ' ')
        return 0;
    if (it->y < 1 || it->m < 1 || it->m > 12 || it->d < 1 || it->d > month_days(it->y, it->m)) return 0;
    long a = 11;
    while (a < n && (s[a] == ' ' || s[a] == '\t')) a++;
    int k = 0;
    for (long i = a; i < n && k < TEXT_MAX; i++)
        it->text[k++] = s[i] == '\t' ? ' ' : (unsigned char)s[i] < 32 || s[i] == 127 ? '?' : s[i];
    it->text[k] = 0;
    return k > 0;
}
COLD static void load(struct cal *c) {
    u64 size = 0;
    long got = fs_read_at(&c->fs, PATH, 0, &size);
    if (got < 0) {
        c->writable = !fs_stat(&c->fs, PATH, 0);
        put_s(&c->l, c->writable ? "calendar: no events yet (" PATH " is new)"
                                 : "calendar: could not read " PATH ": it will not be written");
        say(c);
        return;
    }
    c->writable = (u64)got >= size;
    const char *s = fs_data(&c->fs);
    int skipped = 0;
    for (long i = 0; i < got;) {
        long e = i;
        while (e < got && s[e] != '\n') e++;
        struct item it;
        int blank = 1;
        for (long k = i; k < e; k++) blank &= s[k] == ' ' || s[k] == '\t' || s[k] == '\r';
        if (!blank) {
            if (!parse(s + i, e - i, &it)) skipped++;
            else if (!insert(c, &it)) c->writable = 0;     /* more than it holds: never written */
        }
        i = e + 1;
    }
    put_s(&c->l, "calendar: read ");
    put_dec(&c->l, (u64)c->n);
    put_s(&c->l, c->n == 1 ? " event from " PATH : " events from " PATH);
    if (skipped) {
        put_s(&c->l, ", skipped ");
        put_dec(&c->l, (u64)skipped);
        put_s(&c->l, skipped == 1 ? " line that is not one" : " lines that are not one");
    }
    if (!c->writable) put_s(&c->l, ", and more than fits: it will not be written");
    say(c);
}

/* ---- drawing ---- */

/* Text, its width, rounded rectangles and lines, each drawn in one place rather than inlined
   at every call (as Clock does), which keeps the code small. */
__attribute__((noinline)) static int text_at(struct cal *c, const struct font *f, int x, int y, const char *s,
                                             unsigned color) {
    return font_text(&c->win, f, x, y, s, color);
}
__attribute__((noinline)) static int width(const struct font *f, const char *s) { return font_width(f, s); }
__attribute__((noinline)) static void box(struct cal *c, int x, int y, int w, int h, int r, unsigned color) {
    round_rect(&c->win, x, y, w, h, r, color, 255);
}
__attribute__((noinline)) static void line_at(struct cal *c, int x0, int y0, int x1, int y1, int w, unsigned color) {
    thick_line(&c->win, x0, y0, x1, y1, w, color);
}

/* Text that fits `w` pixels: cut, with "..." after it, if it does not. */
COLD static void fit(const struct font *f, const char *s, int w, char *out) {
    int n = 0;
    while (s[n] && n < TEXT_MAX) { out[n] = s[n]; n++; }
    out[n] = 0;
    while (n > 0 && width(f, out) > w) {
        n--;
        out[n] = out[n + 1] = out[n + 2] = '.';
        out[n + 3] = 0;
    }
}

COLD static void button(struct cal *c, int x, int w, const char *label, int on) {
    box(c, x, BTN_Y, w, BTN_H, 7, BUTTON);
    const struct font *f = &c->ui.small_bold;
    text_at(c, f, x + (w - width(f, label)) / 2, BTN_Y + 17, label, on ? INK : DIM);
}
COLD static void chevron(struct cal *c, int x, int dir) {
    int cx = (x + ARROW_W / 2) * 16, cy = (BTN_Y + BTN_H / 2) * 16;
    box(c, x, BTN_Y, ARROW_W, BTN_H, 7, BUTTON);
    line_at(c, cx - dir * 40, cy - 80, cx + dir * 40, cy, 2, INK);      /* dir 1: >, -1: < */
    line_at(c, cx + dir * 40, cy, cx - dir * 40, cy + 80, 2, INK);
}

COLD static void draw_month(struct cal *c) {
    struct line t = {.n = 0};
    put_s(&t, month_names[c->m - 1]);
    put_s(&t, " ");
    put_dec(&t, (u64)c->y);
    t.b[t.n] = 0;
    text_at(c, &c->ui.title, GX + 7 * CELL_W / 2 - width(&c->ui.title, t.b) / 2, BTN_Y + 22, t.b, INK);
    chevron(c, PREV_X, -1);
    chevron(c, NEXT_X, 1);
    static const char *const wd[7] = {"Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"};
    for (int i = 0; i < 7; i++)
        text_at(c, &c->ui.small_bold, GX + i * CELL_W + (CELL_W - width(&c->ui.small_bold, wd[i])) / 2, 60,
                  wd[i], GRAY);
    /* which of the 42 days have events: a bit each */
    int fy, fm, fd;
    cell_date(c, 0, &fy, &fm, &fd);
    long k0 = days_of(fy, fm, fd);
    u64 marked = 0;
    for (int i = 0; i < c->n; i++) {
        long k = key_of(&c->items[i]) - k0;
        if (k >= 0 && k < 42) marked |= 1UL << k;
    }
    for (int i = 0; i < 42; i++) {
        int y, m, d, x0 = GX + i % 7 * CELL_W, y0 = GY + i / 7 * CELL_H;
        cell_date(c, i, &y, &m, &d);
        int today = c->ty && same(y, m, d, c->ty, c->tm, c->td), here = m == c->m;
        if (same(y, m, d, c->y, c->m, c->d)) box(c, x0 + 2, y0 + 1, CELL_W - 4, CELL_H - 2, 8, SEL);
        if (today) box(c, x0 + 5, y0 + 3, CELL_W - 10, CELL_H - 6, 8, ACCENT);
        struct line n = {.n = 0};
        put_dec(&n, (u64)d);
        n.b[n.n] = 0;
        const struct font *f = today ? &c->ui.bold : &c->ui.body;
        text_at(c, f, x0 + (CELL_W - width(f, n.b)) / 2, y0 + 20, n.b, today ? rgb(255, 255, 255) : here ? INK : DIM);
        if (marked >> i & 1)
            box(c, x0 + CELL_W / 2 - 2, y0 + 24, 5, 5, 2, today ? rgb(255, 255, 255) : here ? DOT : mix(DOT, BG, 150));
    }
}

COLD static void draw_panel(struct cal *c) {
    fill(&c->win, PX, 0, CW - PX, CH, PANEL);
    int x = PX + 14;
    text_at(c, &c->ui.small, x, 24, day_names[weekday_of(days_of(c->y, c->m, c->d))], GRAY);
    struct line t = {.n = 0};
    put_s(&t, month_names[c->m - 1]);
    put_s(&t, " ");
    put_dec(&t, (u64)c->d);
    put_s(&t, ", ");
    put_dec(&t, (u64)c->y);
    t.b[t.n] = 0;
    text_at(c, &c->ui.bold, x, 44, t.b, INK);
    button(c, TODAY_X, TODAY_W, "Today", c->ty != 0);
    int first, n = day_items(c, &first);
    /* one line under the date: typing's keys, the last thing done, or how things are */
    struct line u = {.n = 0};
    unsigned color = GRAY;
    if (c->typing) put_s(&u, "Return keeps it, Escape cancels");
    else if (c->note) { put_s(&u, c->note); color = WARN; }
    else if (!c->ty) { put_s(&u, "the date is not set"); color = WARN; }
    else if (!n) put_s(&u, "no events");
    else {
        put_dec(&u, (u64)n);
        put_s(&u, n == 1 ? " event" : " events");
    }
    u.b[u.n] = 0;
    text_at(c, &c->ui.small, x, 64, u.b, color);
    char cut[TEXT_MAX + 4];
    for (int r = 0; r < n && r < ROWS; r++) {
        int y = ROW_Y + r * ROW_H;
        box(c, ROW_X, y + 1, ROW_W, ROW_H - 2, 6, r == c->pick ? SEL : rgb(255, 255, 255));
        fit(&c->ui.body, c->items[first + r].text, ROW_W - DEL_W - 12, cut);
        text_at(c, &c->ui.body, ROW_X + 8, y + 16, cut, INK);
        int cx = (ROW_X + ROW_W - DEL_W / 2) * 16, cy = (y + ROW_H / 2) * 16;
        line_at(c, cx - 48, cy - 48, cx + 48, cy + 48, 1, GRAY);
        line_at(c, cx - 48, cy + 48, cx + 48, cy - 48, 1, GRAY);
    }
    if (c->typing) {                     /* the line being typed, with a cursor at its end */
        box(c, ROW_X, ADD_Y, ROW_W, ADD_H, 7, ACCENT);
        box(c, ROW_X + 2, ADD_Y + 2, ROW_W - 4, ADD_H - 4, 5, rgb(255, 255, 255));
        c->input[c->ilen] = 0;
        const char *shown = c->input;    /* its end, if it is longer than the box */
        while (*shown && width(&c->ui.body, shown) > ROW_W - 22) shown++;
        int end = text_at(c, &c->ui.body, ROW_X + 8, ADD_Y + 18, shown, INK);
        fill(&c->win, end + 1, ADD_Y + 6, 2, ADD_H - 12, ACCENT);
    } else {
        box(c, ROW_X, ADD_Y, ROW_W, ADD_H, 7, BUTTON);
        const char *label = "+  New event";
        text_at(c, &c->ui.small_bold, ROW_X + (ROW_W - width(&c->ui.small_bold, label)) / 2, ADD_Y + 17, label,
                  n < ROWS ? INK : DIM);
    }
}

COLD static void draw(struct cal *c) {
    fill(&c->win, 0, 0, CW, CH, BG);
    draw_month(c);
    draw_panel(c);
}

COLD __attribute__((section(".text.start"))) void _start(void) {
    struct cal *c = (struct cal *)DATA;
    c->l.n = 0;
    ui_load(&c->ui, app_assets());
    c->win = app_surface(CW, CH);
    fs_init(&c->fs, SPARE_PAGE);
    c->n = 0;
    c->y = c->m = c->d = 0;
    c->ty = c->tm = c->td = 0;
    c->pick = -1;
    c->typing = 0;
    c->note = 0;
    load(c);
    check_today(c);
    if (!c->ty) {
        put_s(&c->l, "calendar: the date is not set (no time server has answered)");
        say(c);
        select_day(c, UNSET_YEAR, 1, 1);
    }
    draw(c);
    u64 opened = app_open(CW, CH, "Calendar");
    put_s(&c->l, "calendar: opened a window");
    put_s(&c->l, outcome(opened));
    say(c);
    if (opened != OK) exit_task();
    int dirty = 0;
    u64 checked = millis();
    for (;;) {
        struct event e = app_poll(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&c->l, "calendar: window closed, exiting");
            say(c);
            exit_task();
        }
        int changed = 1;
        if (e.kind == EV_KEY) key(c, e.a);
        else if (e.kind == EV_DOWN) click(c, (int)e.a, (int)e.b);
        else if (e.kind == EV_PASTE && c->typing) paste(c, e);
        else changed = 0;
        if (millis() - checked >= 1000) {
            checked = millis();
            changed |= check_today(c);
        }
        if (changed) {
            draw(c);
            dirty = 1;
        } else if (e.kind == EV_NONE) sleep_ms(50);
    }
}
