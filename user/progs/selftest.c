/* selftest: one boot that says what a real board does differently from QEMU. The self-test
   card (make pi-selftest) starts it at boot (its startup.txt); test/selftest.sh runs it under
   QEMU, where every check must pass. It runs its checks one after the other and says each
   result on one line of its log (the serial console) and in its window:

     selftest: NAME: PASS|FAIL|INFO details

   and last `selftest: done: N passed, M failed, K info`. tools/serial.py --summary gathers
   those lines. Before each check it says `selftest: checking NAME`, so a check that never
   ends (a request the file server never answers) is named by the last such line.

     memory   every page of its spare run (228 pages): a pattern unique to each word written
              everywhere, then read back everywhere, then its complement, then bytes one at a
              time read back as whole words. The first 64 pages hold its fonts: each is copied
              aside, tested, and put back. PASS: every word read as written. Its speed is
              printed too: the run fits in the Pi's 1 MiB L2 cache, so what it mostly shows is
              whether the pages are cached as they should be (a mapping with the wrong
              memory attributes is many times slower).
     sd       a 1 MiB file in its folder on the card (apps/selftest), 12 KiB a request, a
              pattern that differs in every word and from run to run; read back and every
              byte compared; then deleted. PASS: every request answered, every byte right,
              and the card's free space as it was. Times both ways (MiB/s).
     sdfiles  50 files of 1 KiB: written, read back and compared, deleted; timed each way.
     clock    the kernel's clock (the `time` call, 10 ms ticks) against the processor's
              counter (lib.h's micros) over 3 s. PASS: they agree within 30 ms.
     sleep    sleep_ms(100) ten times, each measured by the counter. A sleep is whole 10 ms
              ticks from the last one, so 90 to 100 ms; a tick that comes late and catches up
              makes one shorter. PASS: the median from 90 to 130 ms, and none under 80 ms.
     screen   60 frames, each the whole window drawn and handed to the display (POLL, which
              draws it before it answers). PASS: every frame shown within 10 s in all.
     cpu      INFO: a counted loop, a yield, the counter's rate, the uptime, the tasks alive.
     usb      INFO: a program cannot ask the USB driver anything: the usb: lines say.
     time     INFO: the time of day, if the network has set it.
     input    a key and a click in its window, waited for 20 s: PASS if both came; INFO if
              not (nobody may be at the keyboard).

   Every check has a time limit and says FAIL with what it saw rather than wait for ever. It
   uses no network. When it is done the window stays until it is closed. */
#include "../ui.h"
#include "../fs.h"
#include "../date.h"

#define COLD __attribute__((cold, minsize))

#define WW 480
#define WH 340          /* 160 pages of pixels: pages 64-223 of the spare run, before the
                           file server's buffer (224-227) */
#define ROW_Y 54
#define ROW_H 28        /* a check's row: its detail on up to two lines */
#define DETAIL_X 128

#define SPARE_PAGES 228
#define ASSET_PAGES 64

#define BIG (1024 * 1024UL)       /* the big file */
#define CHUNK (12 * 1024UL)       /* each request: three 4 KiB clusters */
#define SMALL_N 50
#define SMALL (1024UL)
#define SD_BUDGET_US (90 * 1000000UL)
#define SCREEN_FRAMES 60
#define SCREEN_BUDGET_US (10 * 1000000UL)
#define INPUT_WAIT_MS 20000

enum { C_MEMORY, C_SD, C_SDFILES, C_CLOCK, C_SLEEP, C_SCREEN, C_CPU, C_USB, C_TIME, C_INPUT, NCHECK };
static const char *const check_names[NCHECK] = {"memory", "sd", "sdfiles", "clock", "sleep", "screen",
                                                "cpu", "usb", "time", "input"};
enum { WAITING, RUNNING, PASS, FAIL, INFO };
static const char *const state_names[5] = {"", "...", "PASS", "FAIL", "INFO"};

struct check {
    int state;
    char detail[180];
};

struct selftest {
    struct ui ui;
    struct surface win;
    struct fs_client fs;
    int win_ok;
    struct check c[NCHECK];
    u64 keys, clicks, last_key, click_x, click_y;
    char dir[FS_PATH_MAX + 1];
    u64 sample[SCREEN_FRAMES];
};

/* ---- numbers in lines ---- */

/* microseconds as milliseconds, one decimal */
COLD static void put_ms(struct line *l, u64 us) {
    put_dec(l, us / 1000);
    put_s(l, ".");
    put_dec(l, us / 100 % 10);
}

/* hundredths as n.nn */
COLD static void put_hundredths(struct line *l, u64 v) {
    put_dec(l, v / 100);
    put_s(l, v % 100 < 10 ? ".0" : ".");
    put_dec(l, v % 100);
}

/* `bytes` in `us` as MiB/s */
COLD static void put_rate(struct line *l, u64 bytes, u64 us) {
    put_hundredths(l, us ? bytes * 100000000UL / 1048576UL / us : 0);
    put_s(l, " MiB/s");
}

COLD static u64 absdiff(u64 a, u64 b) { return a > b ? a - b : b - a; }

COLD static void sort(u64 *v, int n) {
    for (int i = 1; i < n; i++)
        for (int j = i; j > 0 && v[j - 1] > v[j]; j--) {
            u64 t = v[j];
            v[j] = v[j - 1];
            v[j - 1] = t;
        }
}

/* ---- the window ---- */

static const unsigned state_color[5] = {0xc8ccd8, 0x8a90a8, 0x2e9e5b, 0xd8433a, 0x3a6ee6};

/* `s` in font f at (x, y), cut short with "..." if it is wider than w */
COLD static void text_fit(struct selftest *t, const struct font *f, int x, int y, int w, const char *s, unsigned c) {
    char b[160];
    int n = 0;
    while (s[n] && n < 150) { b[n] = s[n]; n++; }
    b[n] = 0;
    if (font_width(f, b) > w) {
        int dots = font_width(f, "...");
        while (n > 0 && font_width(f, b) + dots > w) b[--n] = 0;
        b[n] = '.';
        b[n + 1] = '.';
        b[n + 2] = '.';
        b[n + 3] = 0;
    }
    font_text(&t->win, f, x, y, b, c);
}

/* `s` on up to two lines of width w (the first's baseline at y), broken at a space; the
   second cut short if need be */
COLD static void text_two(struct selftest *t, const struct font *f, int x, int y, int w, const char *s, unsigned c) {
    char b[160];
    int n = 0, cut = 0;
    while (s[n] && n < 150) {
        b[n] = s[n];
        b[++n] = 0;
        if (font_width(f, b) > w) break;
        if (!s[n] || s[n] == ' ') cut = n;
    }
    if (!s[n] || n >= 150 || !cut) {           /* one line: level with the check's name */
        text_fit(t, f, x, y + 6, w, s, c);
        return;
    }
    b[cut] = 0;
    font_text(&t->win, f, x, y, b, c);
    text_fit(t, f, x, y + 13, w, s + cut + 1, c);
}

COLD static void counts(struct selftest *t, u64 *pass, u64 *fail, u64 *info) {
    *pass = *fail = *info = 0;
    for (int i = 0; i < NCHECK; i++) {
        *pass += t->c[i].state == PASS;
        *fail += t->c[i].state == FAIL;
        *info += t->c[i].state == INFO;
    }
}

COLD static void draw(struct selftest *t, int done) {
    struct surface *s = &t->win;
    fill(s, 0, 0, WW, WH, rgb(250, 250, 252));
    font_text(s, &t->ui.bold, 16, 24, "Hardware self-test", rgb(24, 26, 36));
    u64 pass, fail, info;
    counts(t, &pass, &fail, &info);
    struct line l = {.n = 0};
    if (done) {
        put_dec(&l, pass);
        put_s(&l, " passed, ");
        put_dec(&l, fail);
        put_s(&l, " failed, ");
        put_dec(&l, info);
        put_s(&l, " info. Send the serial log and a photo of this window.");
    } else {
        put_s(&l, "Checking; each result also goes to the serial log.");
    }
    l.b[l.n < sizeof l.b ? l.n : sizeof l.b - 1] = 0;
    text_fit(t, &t->ui.small, 16, 42, WW - 32, l.b, done ? (fail ? state_color[FAIL] : state_color[PASS]) : rgb(110, 114, 130));
    for (int i = 0; i < NCHECK; i++) {
        int y = ROW_Y + i * ROW_H, st = t->c[i].state;
        if (i) fill(s, 16, y - 1, WW - 32, 1, rgb(232, 234, 240));
        round_rect(s, 14, y + 5, 44, 18, 9, state_color[st], 255);
        const char *sn = state_names[st];
        font_text(s, &t->ui.small_bold, 36 - font_width(&t->ui.small_bold, sn) / 2, y + 18, sn, rgb(255, 255, 255));
        font_text(s, &t->ui.small_bold, 66, y + 18, check_names[i], rgb(40, 42, 54));
        text_two(t, &t->ui.small, DETAIL_X, y + 12, WW - DETAIL_X - 12, t->c[i].detail,
                 st == FAIL ? state_color[FAIL] : rgb(90, 92, 104));
    }
}

/* Events, from any poll: the close button, and the keys and clicks the input check counts. */
COLD static void on_event(struct selftest *t, struct event e) {
    if (e.kind == EV_CLOSE) t->win_ok = 0;
    else if (e.kind == EV_KEY) { t->keys++; t->last_key = e.a; }
    else if (e.kind == EV_DOWN) { t->clicks++; t->click_x = e.a; t->click_y = e.b; }
}

/* Hand the window to the display (drawn before it answers), and take what events wait. */
COLD static struct res present(struct selftest *t, int dirty) {
    struct res r = {.x = {BAD_ARG}};
    if (!t->win_ok) return r;
    r = sys(SYS_CALL, ENDPOINT, OP_POLL, (u64)dirty, 0, 0);
    struct event e = app_event(r);
    for (int k = 0; k < 16 && e.kind != EV_NONE && t->win_ok; k++) {
        on_event(t, e);
        e = app_poll(0);
    }
    return r;
}

COLD static void show(struct selftest *t, int done) {
    if (!t->win_ok) return;
    draw(t, done);
    present(t, 1);
}

/* ---- results ---- */

COLD static void begin(struct selftest *t, int i) {
    t->c[i].state = RUNNING;
    struct line l = {.n = 0};
    put_s(&l, "selftest: checking ");
    put_s(&l, check_names[i]);
    put_s(&l, "\n");
    flush(&l);
    show(t, 0);
}

/* The check's result: its line in the log, and in the window. */
COLD static void result(struct selftest *t, int i, int state, struct line *d) {
    struct check *c = &t->c[i];
    u64 n = d->n < sizeof c->detail - 1 ? d->n : sizeof c->detail - 1;
    for (u64 k = 0; k < n; k++) c->detail[k] = d->b[k];
    c->detail[n] = 0;
    c->state = state;
    struct line l = {.n = 0};
    put_s(&l, "selftest: ");
    put_s(&l, check_names[i]);
    put_s(&l, ": ");
    put_s(&l, state_names[state]);
    put_s(&l, " ");
    put_s(&l, c->detail);
    put_s(&l, "\n");
    flush(&l);
    show(t, 0);
}

/* ---- memory: every page of the spare run ---- */

static inline u64 mem_pattern(u64 addr, u64 seed) { return (addr * 0x9E3779B97F4A7C15UL) ^ seed; }

struct mem_err { u64 bad, addr, want, got; };

static void mem_note(struct mem_err *m, volatile u64 *p, u64 want, u64 got) {
    if (!m->bad) { m->addr = (u64)p; m->want = want; m->got = got; }
    m->bad++;
}

/* pages [first, first + n): words written everywhere, then read back everywhere (a page that
   shows up at two addresses, or a write that never reaches memory, reads wrong), then the
   complement; then bytes, one at a time, read back as whole words */
static void mem_test(u64 first, u64 n, u64 seed, struct mem_err *m) {
    volatile u64 *base = (volatile u64 *)PAGE(SPARE_PAGE + first);
    u64 words = n * 512;
    for (int pass = 0; pass < 2; pass++) {
        u64 flip = pass ? ~0UL : 0;
        for (u64 i = 0; i < words; i++) base[i] = mem_pattern((u64)&base[i], seed) ^ flip;
        for (u64 i = 0; i < words; i++) {
            u64 want = mem_pattern((u64)&base[i], seed) ^ flip, got = base[i];
            if (got != want) mem_note(m, &base[i], want, got);
        }
    }
    volatile unsigned char *b = (volatile unsigned char *)base;
    for (u64 i = 0; i < words * 8; i++) b[i] = (unsigned char)(mem_pattern(i >> 3, seed) >> (8 * (i & 7)));
    for (u64 i = 0; i < words; i++) {
        u64 want = mem_pattern(i, seed), got = base[i];
        if (got != want) mem_note(m, &base[i], want, got);
    }
}

static void page_copy(u64 to, u64 from) {
    volatile u64 *d = (volatile u64 *)PAGE(SPARE_PAGE + to), *s = (volatile u64 *)PAGE(SPARE_PAGE + from);
    for (int i = 0; i < 512; i++) d[i] = s[i];
}

COLD static void check_memory(struct selftest *t) {
    begin(t, C_MEMORY);
    struct mem_err m = {0, 0, 0, 0};
    u64 seed = micros() * 0x2545F4914F6CDD1DUL, t0 = micros();
    /* the pages after the fonts, all at once (nothing is in them yet: the window is not
       drawn, and the file server's buffer is not in use until the first request) */
    mem_test(ASSET_PAGES, SPARE_PAGES - ASSET_PAGES, seed, &m);
    /* the fonts' pages, one at a time: copied aside to the last page, tested, put back */
    u64 aside = SPARE_PAGES - 1, restored_bad = 0;
    for (u64 p = 0; p < ASSET_PAGES; p++) {
        page_copy(aside, p);
        mem_test(p, 1, seed ^ p, &m);
        page_copy(p, aside);
        volatile u64 *a = (volatile u64 *)PAGE(SPARE_PAGE + p), *b = (volatile u64 *)PAGE(SPARE_PAGE + aside);
        for (int i = 0; i < 512; i++) restored_bad += a[i] != b[i];
    }
    u64 us = micros() - t0;
    /* bytes moved: each page written 3 times and read 3 times; the fonts' pages also copied
       aside and back (a read and a write each) and compared (two reads) */
    u64 moved = (SPARE_PAGES * 6 + ASSET_PAGES * 6) * 4096UL;
    struct line d = {.n = 0};
    put_dec(&d, SPARE_PAGES);
    put_s(&d, " pages, 3 patterns: ");
    put_dec(&d, m.bad);
    put_s(&d, " bad words; ");
    put_ms(&d, us);
    put_s(&d, " ms, ");
    put_rate(&d, moved, us);
    if (m.bad) {
        put_s(&d, "; first at ");
        put_hex(&d, m.addr);
        put_s(&d, " wrote ");
        put_hex(&d, m.want);
        put_s(&d, " read ");
        put_hex(&d, m.got);
    }
    if (restored_bad) {
        put_s(&d, "; fonts not put back: ");
        put_dec(&d, restored_bad);
        put_s(&d, " words");
    }
    result(t, C_MEMORY, m.bad || restored_bad ? FAIL : PASS, &d);
}

/* ---- the SD card, through the file server ---- */

static void path_in(struct selftest *t, char *out, const char *name) {
    int n = 0;
    for (int i = 0; t->dir[i] && n < FS_PATH_MAX - 60; i++) out[n++] = t->dir[i];
    out[n++] = '/';
    for (int i = 0; name[i] && n < FS_PATH_MAX; i++) out[n++] = name[i];
    out[n] = 0;
}

static inline unsigned word_at(u64 w, unsigned seed) { return (unsigned)((w + 1) * 2654435761UL) ^ seed; }

/* `n` bytes (a multiple of 4) of the pattern for offset `off` into the request's data */
static void fill_pattern(struct selftest *t, u64 off, u64 n, unsigned seed) {
    unsigned *p = (unsigned *)(t->fs.buf + FS_DATA_OFF);
    for (u64 k = 0; k < n / 4; k++) p[k] = word_at(off / 4 + k, seed);
}

/* how many words of the data differ from the pattern; *first gets the first one's offset */
static u64 bad_words(struct selftest *t, u64 off, u64 n, unsigned seed, u64 *first) {
    const unsigned *p = (const unsigned *)(t->fs.buf + FS_DATA_OFF);
    u64 bad = 0;
    for (u64 k = 0; k < n / 4; k++)
        if (p[k] != word_at(off / 4 + k, seed)) {
            if (!bad) *first = off + 4 * k;
            bad++;
        }
    return bad;
}

COLD static struct res fs_req(struct selftest *t, u64 op, const char *path, u64 off, u64 arg) {
    fs_path(&t->fs, path);
    fs_offset(&t->fs, off);
    return fs_call(&t->fs, op, arg);
}

/* its folder: the first path it was given to write (Apps and Terminal give apps/NAME) */
COLD static int find_folder(struct selftest *t) {
    long n = fs_grants(&t->fs);
    const char *d = fs_data(&t->fs);
    for (long g = 0, at = 0; g < n && at < (long)FS_CHUNK; g++) {
        int rights = d[at++], k = 0;
        while (d[at] && at < (long)FS_CHUNK && k < FS_PATH_MAX) t->dir[k++] = d[at++];
        t->dir[k] = 0;
        at++;
        if ((rights & FS_W) && k) return 1;
    }
    t->dir[0] = 0;
    return 0;
}

COLD static void say_status(struct line *d, const char *what, u64 off, u64 status) {
    put_s(d, what);
    put_dec(d, off);
    put_s(d, " refused, status ");
    put_dec(d, status);
}

COLD static void check_sd(struct selftest *t) {
    begin(t, C_SD);
    struct line d = {.n = 0};
    struct fs_space s0, s1;
    if (!find_folder(t)) {
        put_s(&d, "no folder of its own on the card (start it from Apps or Terminal)");
        result(t, C_SD, FAIL, &d);
        return;
    }
    char path[FS_PATH_MAX + 1];
    path_in(t, path, "big.bin");
    fs_delete(&t->fs, path);                    /* a run cut short last time */
    /* A folder's first entry takes it a cluster, which it keeps when the entry goes: a file
       made and deleted first, so the free space after is the free space before. */
    fs_write(&t->fs, path, "x", 1);
    fs_delete(&t->fs, path);
    u64 sp = fs_space(&t->fs, &s0);
    unsigned seed = (unsigned)micros() | 1;
    u64 t0 = micros(), off = 0, status = FS_OK, over = 0;
    for (; off < BIG && status == FS_OK; off += CHUNK) {
        if (micros() - t0 > SD_BUDGET_US) { over = 1; break; }
        u64 n = BIG - off < CHUNK ? BIG - off : CHUNK;
        fill_pattern(t, off, n, seed);
        status = fs_req(t, FS_WRITE_AT, path, off, n).x[1];
    }
    u64 tw = micros() - t0;
    if (status != FS_OK || over) {
        if (over) {
            put_s(&d, "writing took over 90 s; stopped at byte ");
            put_dec(&d, off);
        } else say_status(&d, "the write at byte ", off - CHUNK, status);
        fs_delete(&t->fs, path);
        result(t, C_SD, FAIL, &d);
        return;
    }
    u64 bad = 0, first = 0, short_at = BIG, size = 0;
    t0 = micros();
    for (off = 0; off < BIG; off += CHUNK) {
        if (micros() - t0 > SD_BUDGET_US) { over = 1; break; }
        u64 n = BIG - off < CHUNK ? BIG - off : CHUNK, f = 0;
        long got = fs_read_at(&t->fs, path, off, &size);      /* up to FS_CHUNK bytes */
        if (got < (long)n || size != BIG) { short_at = off; break; }
        u64 b = bad_words(t, off, n, seed, &f);
        if (b && !bad) first = f;
        bad += b;
    }
    u64 tr = micros() - t0;
    u64 del = fs_delete(&t->fs, path);
    u64 sp1 = fs_space(&t->fs, &s1);
    int space_back = sp == FS_OK && sp1 == FS_OK && s0.free == s1.free;
    put_s(&d, "1 MiB written in ");
    put_ms(&d, tw);
    put_s(&d, " ms (");
    put_rate(&d, BIG, tw);
    put_s(&d, ")");
    if (short_at < BIG || over) {
        put_s(&d, over ? ", reading took over 90 s" : ", the read at byte ");
        if (!over) put_dec(&d, short_at);
        put_s(&d, over ? "" : " came short");
    } else {
        put_s(&d, ", read in ");
        put_ms(&d, tr);
        put_s(&d, " ms (");
        put_rate(&d, BIG, tr);
        put_s(&d, ")");
    }
    if (bad) {
        put_s(&d, "; ");
        put_dec(&d, bad);
        put_s(&d, " bad words, the first at byte ");
        put_dec(&d, first);
    } else if (short_at == BIG && !over) put_s(&d, ", every byte right");
    if (del != FS_OK) say_status(&d, "; delete ", 0, del);
    else if (!space_back) {
        put_s(&d, "; the free space did not come back: ");
        put_dec(&d, s0.free);
        put_s(&d, " clusters free before, ");
        put_dec(&d, s1.free);
        put_s(&d, " after");
    } else put_s(&d, "; deleted");
    result(t, C_SD, bad || short_at < BIG || over || del != FS_OK || !space_back ? FAIL : PASS, &d);
}

COLD static void small_name(struct selftest *t, char *path, int i) {
    char name[8] = {'f', (char)('0' + i / 10), (char)('0' + i % 10), 0};
    path_in(t, path, name);
}

COLD static void check_sdfiles(struct selftest *t) {
    begin(t, C_SDFILES);
    struct line d = {.n = 0};
    if (!t->dir[0]) {
        put_s(&d, "no folder of its own on the card");
        result(t, C_SDFILES, FAIL, &d);
        return;
    }
    char path[FS_PATH_MAX + 1];
    struct fs_space s0, s1;
    for (int i = 0; i < SMALL_N; i++) {       /* a run cut short last time */
        small_name(t, path, i);
        fs_delete(&t->fs, path);
    }
    u64 sp = fs_space(&t->fs, &s0);
    unsigned seed = (unsigned)micros() | 1;
    u64 t0 = micros(), status = FS_OK, bad = 0, missing = 0, undeleted = 0;
    int i = 0;
    for (; i < SMALL_N && status == FS_OK && micros() - t0 < SD_BUDGET_US; i++) {
        small_name(t, path, i);
        fill_pattern(t, (u64)i * SMALL, SMALL, seed);
        status = fs_req(t, FS_WRITE, path, 0, SMALL).x[1];
    }
    u64 tw = micros() - t0;
    int written = status == FS_OK ? i : i - 1;
    t0 = micros();
    for (int k = 0; k < written && micros() - t0 < SD_BUDGET_US; k++) {
        small_name(t, path, k);
        u64 f = 0;
        u64 size = 0;
        if (fs_read_at(&t->fs, path, 0, &size) != (long)SMALL || size != SMALL) missing++;
        else bad += bad_words(t, (u64)k * SMALL, SMALL, seed, &f) != 0;
    }
    u64 tr = micros() - t0;
    t0 = micros();
    for (int k = 0; k < SMALL_N; k++) {
        small_name(t, path, k);
        u64 r = fs_delete(&t->fs, path);
        undeleted += k < written && r != FS_OK;
    }
    u64 td = micros() - t0;
    u64 sp1 = fs_space(&t->fs, &s1);
    int space_back = sp == FS_OK && sp1 == FS_OK && s0.free == s1.free && s0.files == s1.files;
    put_dec(&d, SMALL_N);
    put_s(&d, " x 1 KiB: written in ");
    put_ms(&d, tw);
    put_s(&d, " ms, read ");
    put_ms(&d, tr);
    put_s(&d, " ms, deleted ");
    put_ms(&d, td);
    put_s(&d, " ms");
    if (written < SMALL_N) {
        put_s(&d, "; only ");
        put_dec(&d, (u64)written);
        put_s(&d, " written");
        if (status != FS_OK) {
            put_s(&d, ", status ");
            put_dec(&d, status);
        }
    }
    if (missing) {
        put_s(&d, "; unreadable: ");
        put_dec(&d, missing);
    }
    if (bad) {
        put_s(&d, "; wrong: ");
        put_dec(&d, bad);
    }
    if (undeleted) {
        put_s(&d, "; not deleted: ");
        put_dec(&d, undeleted);
    }
    if (!space_back) put_s(&d, "; the free space did not come back");
    if (written == SMALL_N && !missing && !bad && !undeleted && space_back) put_s(&d, "; all right");
    result(t, C_SDFILES, written == SMALL_N && !missing && !bad && !undeleted && space_back ? PASS : FAIL, &d);
}

/* ---- time ---- */

COLD static void check_clock(struct selftest *t) {
    begin(t, C_CLOCK);
    /* start just after a tick, so the kernel's 10 ms steps cost nothing at the start */
    u64 k0 = sys0(SYS_TIME).x[2], deadline = micros() + 100000, k;
    while ((k = sys0(SYS_TIME).x[2]) == k0 && micros() < deadline) {}
    u64 c0 = micros();
    k0 = k;
    sleep_ms(3000);
    u64 k1 = sys0(SYS_TIME).x[2], c1 = micros();
    u64 kms = k1 - k0, cus = c1 - c0, off = absdiff(kms * 1000, cus);
    struct line d = {.n = 0};
    put_s(&d, "over ");
    put_ms(&d, cus);
    put_s(&d, " ms by the counter, the kernel's clock moved ");
    put_dec(&d, kms);
    put_s(&d, " ms (");
    put_ms(&d, off);
    put_s(&d, " ms apart, at most 30)");
    result(t, C_CLOCK, k1 >= k0 && off <= 30000 ? PASS : FAIL, &d);
}

COLD static void check_sleep(struct selftest *t) {
    begin(t, C_SLEEP);
    u64 v[10];
    for (int i = 0; i < 10; i++) {
        u64 c0 = micros();
        sleep_ms(100);
        v[i] = micros() - c0;
    }
    sort(v, 10);
    u64 median = (v[4] + v[5]) / 2;
    struct line d = {.n = 0};
    put_s(&d, "100 ms x 10: min ");
    put_ms(&d, v[0]);
    put_s(&d, ", median ");
    put_ms(&d, median);
    put_s(&d, ", max ");
    put_ms(&d, v[9]);
    put_s(&d, " ms");
    result(t, C_SLEEP, v[0] >= 80000 && median >= 90000 && median <= 130000 ? PASS : FAIL, &d);
}

/* ---- the screen ---- */

/* the whole window, a different picture each frame: bands that move, over a gradient */
static void pattern(struct selftest *t, u64 f) {
    unsigned *px = t->win.px;
    for (int y = 0; y < WH; y++) {
        unsigned *row = px + y * WW, g = (unsigned)(y * 255 / WH) << 8;
        for (int x = 0; x < WW; x++) {
            unsigned band = (unsigned)(x + y + (int)f * 8) >> 5 & 3;
            row[x] = g | (band == 0 ? 0xe04000u : band == 1 ? 0x2000e0u : band == 2 ? 0xe000e0u : 0x000000u)
                   | (unsigned)(x * 255 / WW) >> 1;
        }
    }
}

COLD static void check_screen(struct selftest *t) {
    begin(t, C_SCREEN);
    struct line d = {.n = 0};
    if (!t->win_ok) {
        put_s(&d, "no window: the display refused it, or it was closed");
        result(t, C_SCREEN, FAIL, &d);
        return;
    }
    u64 t0 = micros(), drawing = 0, showing = 0, refused = 0;
    int f = 0;
    for (; f < SCREEN_FRAMES && t->win_ok && micros() - t0 < SCREEN_BUDGET_US; f++) {
        u64 a = micros();
        pattern(t, (u64)f);
        u64 b = micros();
        refused += present(t, 1).status != OK;
        u64 c = micros();
        drawing += b - a;
        showing += c - b;
        t->sample[f] = c - b;
    }
    u64 total = micros() - t0;
    sort(t->sample, f);
    put_dec(&d, (u64)f);
    put_s(&d, " frames of 480x340 in ");
    put_ms(&d, total);
    put_s(&d, " ms: ");
    put_ms(&d, f ? total / (u64)f : 0);
    put_s(&d, " ms each (drawing ");
    put_ms(&d, f ? drawing / (u64)f : 0);
    put_s(&d, ", showing ");
    put_ms(&d, f ? showing / (u64)f : 0);
    put_s(&d, ", slowest show ");
    put_ms(&d, f ? t->sample[f - 1] : 0);
    put_s(&d, ")");
    if (refused) {
        put_s(&d, "; the display refused ");
        put_dec(&d, refused);
    }
    if (!t->win_ok) put_s(&d, "; the window was closed");
    result(t, C_SCREEN, f == SCREEN_FRAMES && !refused ? PASS : FAIL, &d);
}

/* ---- what the system calls say ---- */

COLD static void check_cpu(struct selftest *t) {
    begin(t, C_CPU);
    u64 a = micros();
    spin(10000000);
    u64 loop = micros() - a;
    u64 yields = 0;
    a = micros();
    while (yields < 1000 && micros() - a < 200000) {
        sys0(SYS_YIELD);
        yields++;
    }
    u64 yus = micros() - a;
    int alive = 0;
    for (u64 k = 0; k < NSLOTS; k++) {
        struct res r = sys1(SYS_BOOTINFO, k);
        alive += r.status == OK && r.x[4] == 1;
    }
    struct res tm = sys0(SYS_TIME);
    struct line d = {.n = 0};
    put_s(&d, "10M-step loop ");
    put_ms(&d, loop);
    put_s(&d, " ms; a yield ");
    put_dec(&d, yields ? yus / yields : 0);
    put_s(&d, " us; counter ");
    put_dec(&d, tick_rate());
    put_s(&d, " Hz; up ");
    put_ms(&d, tm.x[2]);                     /* milliseconds as seconds, one decimal */
    put_s(&d, " s, tick ");
    put_dec(&d, tm.x[1]);
    put_s(&d, "; ");
    put_dec(&d, (u64)alive);
    put_s(&d, " tasks alive; it runs in slot ");
    put_dec(&d, sys0(SYS_WHOAMI).x[1]);
    result(t, C_CPU, INFO, &d);
}

COLD static void check_usb(struct selftest *t) {
    begin(t, C_USB);
    struct line d = {.n = 0};
    put_s(&d, "a program cannot ask the USB driver: see the usb: lines in the serial log");
    result(t, C_USB, INFO, &d);
}

COLD static void check_time(struct selftest *t) {
    begin(t, C_TIME);
    u64 wall = sys0(SYS_TIME).x[6];
    struct line d = {.n = 0};
    if (wall) {
        put_date(&d, wall);
        put_s(&d, " (Unix ");
        put_dec(&d, wall);
        put_s(&d, "), from the network");
    } else put_s(&d, "the time of day is not known (no network time yet)");
    result(t, C_TIME, INFO, &d);
}

COLD static void input_detail(struct selftest *t, struct line *d, u64 left_ms) {
    d->n = 0;
    if (t->keys) {
        put_s(d, "a key (");
        u64 k = t->last_key;
        if (k > 32 && k < 127) {
            char c[2] = {(char)k, 0};
            put_s(d, c);
        } else {
            put_s(d, "code ");
            put_dec(d, k);
        }
        put_s(d, ")");
    } else put_s(d, "no key");
    if (t->clicks) {
        put_s(d, " and a click at ");
        put_dec(d, t->click_x);
        put_s(d, ",");
        put_dec(d, t->click_y);
    } else put_s(d, ", no click");
    if (left_ms) {
        put_s(d, "; click here, then press a key (");
        put_dec(d, left_ms / 1000);
        put_s(d, " s)");
    }
}

COLD static void check_input(struct selftest *t) {
    begin(t, C_INPUT);
    struct line d = {.n = 0};
    if (!t->win_ok) {
        put_s(&d, "no window to type into");
        result(t, C_INPUT, INFO, &d);
        return;
    }
    t->keys = t->clicks = 0;
    struct line l = {.n = 0};
    put_s(&l, "selftest: input: waiting 20 s for a key and a click in its window\n");
    flush(&l);
    u64 end = millis() + INPUT_WAIT_MS, said = ~0UL;
    while (t->win_ok && !(t->keys && t->clicks)) {
        u64 now = millis();
        if (now >= end) break;
        u64 left = (end - now + 999) / 1000;
        if (left != said) {
            said = left;
            input_detail(t, &d, end - now + 999);
            u64 n = d.n < sizeof t->c[C_INPUT].detail - 1 ? d.n : sizeof t->c[C_INPUT].detail - 1;
            for (u64 k = 0; k < n; k++) t->c[C_INPUT].detail[k] = d.b[k];
            t->c[C_INPUT].detail[n] = 0;
            show(t, 0);
        } else present(t, 0);
        sleep_ms(50);
    }
    input_detail(t, &d, 0);
    put_s(&d, t->keys && t->clicks ? ", through the display" : " in 20 s (see the usb: lines)");
    result(t, C_INPUT, t->keys && t->clicks ? PASS : INFO, &d);
}

COLD __attribute__((section(".text.start"))) void _start(void) {
    struct selftest *t = (struct selftest *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    for (int i = 0; i < NCHECK; i++) {
        t->c[i].state = WAITING;
        t->c[i].detail[0] = 0;
    }
    t->win_ok = 0;
    t->keys = t->clicks = t->last_key = t->click_x = t->click_y = 0;
    t->dir[0] = 0;
    u64 started = micros();
    put_s(&l, "selftest: started; counter ");
    put_dec(&l, tick_rate());
    put_s(&l, " Hz\n");
    flush(&l);
    /* first, while nothing is in the spare run but the fonts */
    check_memory(t);
    ui_load(&t->ui, assets);
    t->win = app_surface(WW, WH);
    fs_init(&t->fs, SPARE_PAGE);
    draw(t, 0);
    u64 opened = app_open(WW, WH, "Selftest");
    t->win_ok = opened == OK;
    put_s(&l, "selftest: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    show(t, 0);
    check_sd(t);
    check_sdfiles(t);
    check_clock(t);
    check_sleep(t);
    check_screen(t);
    show(t, 0);
    check_cpu(t);
    check_usb(t);
    check_time(t);
    check_input(t);
    u64 pass, fail, info;
    counts(t, &pass, &fail, &info);
    put_s(&l, "selftest: done: ");
    put_dec(&l, pass);
    put_s(&l, " passed, ");
    put_dec(&l, fail);
    put_s(&l, " failed, ");
    put_dec(&l, info);
    put_s(&l, " info\n");
    flush(&l);
    put_s(&l, "selftest: all of it took ");
    put_ms(&l, micros() - started);
    put_s(&l, " ms\n");
    flush(&l);
    if (!t->win_ok) exit_task();
    draw(t, 1);
    int dirty = 1;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "selftest: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
    }
}
