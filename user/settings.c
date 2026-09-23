/* Settings: the desktop's background, and the Raspberry Pi itself.

   The background goes to the display server, which takes the request only from the badge
   the manifest gives Settings. The Pi's own settings go to the kernel, through the board
   capability (its capability 5), which only Settings holds and which cannot be passed on
   (only frames can be granted). The kernel lets it read the board and its sensors, set the
   CPU clock to 600, 1000 or 1500 MHz (never above what a Pi 4 is rated for), and switch the
   green activity LED on or off; LeanOS/Proofs.lean proves those are the only requests that
   ever reach the hardware, and only from here. */
#include "app.h"

#define SW 480
#define SH 340             /* 160 pages of pixels: an app has 164 after its assets */
enum { F_UI = 1, F_BOLD = 2, F_SMALL = 3 };
#define BOARD 5              /* the board capability */
enum { BOARD_INFO = 0, BOARD_SENSORS = 1, BOARD_CPU = 2, BOARD_LED = 3 };

#define NBG 3
static const char *const bg_names[NBG] = {"Indigo", "Graphite", "Dawn"};
static const unsigned bg_top[NBG] = {0x1e204e, 0x24262c, 0x3a2a5a};
static const unsigned bg_bottom[NBG] = {0x0e4656, 0x0c0d10, 0xd98a5c};

#define SWATCH_W 80
#define SWATCH_H 40
#define SWATCH_Y 42
static int swatch_x(int i) { return 24 + i * (SWATCH_W + 16); }

#define NSPEED 3
static const char *const speed_names[NSPEED] = {"Power saver", "Balanced", "Full speed"};
static const unsigned speed_mhz[NSPEED] = {600, 1000, 1500};
#define PI_Y 140             /* the Raspberry Pi section: facts on the left, controls on the right */
#define ROW_H 18
#define VALUE_X 116
#define CTL_X 318
#define CTL_W 138
#define SEG_H 28
static int seg_y(int i) { return PI_Y + 12 + i * (SEG_H + 6); }
#define LED_Y (PI_Y + 146)

struct settings {
    struct font ui, bold, small;
    struct surface win;
    int chosen;
    int speed;               /* which speed button is lit, or -1 until one is chosen */
    int led;                 /* 1 on, 0 off, -1 not known */
    int have_board;
    u64 revision, serial_lo, serial_hi, memory_mb, firmware;
    int have_sensors;
    u64 millideg, arm_hz, arm_max_hz, throttled;
    u64 refreshed;           /* when the sensors were last read, in the kernel's ms */
};

static void put_fixed1(struct line *l, u64 thousandths) {   /* 45123 -> "45.1" */
    put_dec(l, thousandths / 1000);
    put_s(l, ".");
    put_dec(l, thousandths / 100 % 10);
}

/* The firmware's revision is the time it was built, in seconds since 1970: a date. (An
   emulator may report a small number instead; that is shown as it is.) */
static void put_firmware(struct line *l, u64 t) {
    if (t < 1000000000) { put_dec(l, t); return; }
    long z = (long)(t / 86400) + 719468;            /* days to a civil date (Hinnant) */
    long era = z / 146097, doe = z - era * 146097;
    long yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    long doy = doe - (365 * yoe + yoe / 4 - yoe / 100), mp = (5 * doy + 2) / 153;
    long d = doy - (153 * mp + 2) / 5 + 1, m = mp < 10 ? mp + 3 : mp - 9, y = yoe + era * 400 + (m <= 2);
    static const char *const month[12] = {"January", "February", "March", "April", "May", "June", "July",
                                          "August", "September", "October", "November", "December"};
    put_s(l, month[m - 1]);
    put_s(l, " ");
    put_dec(l, (u64)d);
    put_s(l, ", ");
    put_dec(l, (u64)y);
}

/* The model, from the revision code's new-style fields (type in bits 4-11). */
static const char *model_of(u64 rev) {
    if (!(rev & (1u << 23))) return "an older Raspberry Pi";
    switch ((rev >> 4) & 0xff) {
    case 0x11: return "Raspberry Pi 4 Model B";
    case 0x13: return "Raspberry Pi 400";
    case 0x14: return "Compute Module 4";
    case 0x17: return "Raspberry Pi 5";
    default: return "a Raspberry Pi";
    }
}
static u64 rev_memory_mb(u64 rev) { return rev & (1u << 23) ? 256UL << ((rev >> 20) & 7) : 0; }

static void read_board(struct settings *st) {
    struct res r = sys(SYS_BOARD, BOARD, BOARD_INFO, 0, 0, 0);
    st->have_board = r.status == OK;
    if (!st->have_board) return;
    st->revision = r.x[1];
    st->serial_lo = r.x[2];
    st->serial_hi = r.x[3];
    st->memory_mb = r.x[4];
    st->firmware = r.x[5];
}

static void read_sensors(struct settings *st) {
    struct res r = sys(SYS_BOARD, BOARD, BOARD_SENSORS, 0, 0, 0);
    st->have_sensors = r.status == OK;
    if (!st->have_sensors) return;
    st->millideg = r.x[1];
    st->arm_hz = r.x[2];
    st->arm_max_hz = r.x[3];
    st->throttled = r.x[4];
    if (st->speed < 0)
        for (int i = 0; i < NSPEED; i++)
            if (st->arm_hz / 1000000 == speed_mhz[i]) st->speed = i;
}

static void row(struct settings *st, int y, const char *key, const char *value) {
    font_text(&st->win, &st->ui, 24, y, key, rgb(110, 110, 120));
    font_text(&st->win, &st->ui, VALUE_X, y, value, rgb(30, 30, 36));
}

static void button(struct settings *st, int x, int y, int w, const char *label, int lit) {
    struct surface *s = &st->win;
    round_rect(s, x, y, w, SEG_H, 8, lit ? rgb(58, 110, 230) : rgb(232, 233, 238), 255);
    int lw = font_width(&st->ui, label);
    font_text(s, &st->ui, x + w / 2 - lw / 2, y + 20, label, lit ? rgb(255, 255, 255) : rgb(40, 40, 50));
}

static void draw(struct settings *st) {
    struct surface *s = &st->win;
    fill(s, 0, 0, SW, SH, rgb(246, 246, 248));
    font_text(s, &st->bold, 24, 32, "Background", rgb(30, 30, 36));
    for (int i = 0; i < NBG; i++) {
        int x = swatch_x(i);
        if (i == st->chosen) round_rect(s, x - 4, SWATCH_Y - 4, SWATCH_W + 8, SWATCH_H + 8, 13, rgb(58, 110, 230), 255);
        round_rect(s, x - 1, SWATCH_Y - 1, SWATCH_W + 2, SWATCH_H + 2, 10, rgb(246, 246, 248), 255);
        round_gradient(s, x, SWATCH_Y, SWATCH_W, SWATCH_H, 9, bg_top[i], bg_bottom[i]);
        int lw = font_width(&st->ui, bg_names[i]);
        font_text(s, &st->ui, x + SWATCH_W / 2 - lw / 2, SWATCH_Y + SWATCH_H + 20, bg_names[i],
                  i == st->chosen ? rgb(30, 30, 36) : rgb(110, 110, 120));
    }

    fill(s, 24, PI_Y - 24, SW - 48, 1, rgb(224, 224, 230));
    font_text(s, &st->bold, 24, PI_Y, "This Raspberry Pi", rgb(30, 30, 36));
    struct line l = {.n = 0};
    int y = PI_Y + 28;
    if (!st->have_board) row(st, y, "Board", "the firmware did not answer");
    else {
        row(st, y, "Model", model_of(st->revision));
        y += ROW_H;
        l.n = 0;
        u64 mb = rev_memory_mb(st->revision);
        if (mb >= 1024) { put_dec(&l, mb / 1024); put_s(&l, " GB"); }
        else if (mb) { put_dec(&l, mb); put_s(&l, " MB"); }
        else { put_dec(&l, st->memory_mb); put_s(&l, " MB for the CPU"); }
        l.b[l.n] = 0;
        row(st, y, "Memory", l.b);
        y += ROW_H;
        l.n = 0;
        put_hex(&l, st->serial_hi << 32 | st->serial_lo);
        l.b[l.n] = 0;
        row(st, y, "Serial", l.b);
        y += ROW_H;
        l.n = 0;
        put_hex(&l, st->revision);
        l.b[l.n] = 0;
        row(st, y, "Revision", l.b);
        y += ROW_H;
        l.n = 0;
        put_firmware(&l, st->firmware);
        l.b[l.n] = 0;
        row(st, y, "Firmware", l.b);
    }
    y += ROW_H;
    if (st->have_sensors) {
        l.n = 0;
        put_fixed1(&l, st->millideg);
        put_s(&l, " C");
        l.b[l.n] = 0;
        row(st, y, "Temperature", l.b);
        y += ROW_H;
        l.n = 0;
        put_dec(&l, st->arm_hz / 1000000);
        put_s(&l, " MHz of ");
        put_dec(&l, st->arm_max_hz / 1000000);
        l.b[l.n] = 0;
        row(st, y, "CPU clock", l.b);
        y += ROW_H;
        const char *t = "none";
        if (st->throttled & 1) t = "weak power now";
        else if (st->throttled & 4) t = "too hot now";
        else if (st->throttled & 0x10000) t = "weak power earlier";
        else if (st->throttled & 0x40000) t = "too hot earlier";
        row(st, y, "Throttling", t);
    } else row(st, y, "Sensors", "the firmware did not answer");

    font_text(s, &st->bold, CTL_X, PI_Y, "CPU speed", rgb(30, 30, 36));
    for (int i = 0; i < NSPEED; i++) {
        int by = seg_y(i), lit = st->speed == i;
        round_rect(s, CTL_X, by, CTL_W, SEG_H, 8, lit ? rgb(58, 110, 230) : rgb(232, 233, 238), 255);
        font_text(s, &st->ui, CTL_X + 10, by + 19, speed_names[i], lit ? rgb(255, 255, 255) : rgb(40, 40, 50));
        struct line m = {.n = 0};
        put_dec(&m, speed_mhz[i]);
        m.b[m.n] = 0;
        font_text(s, &st->small, CTL_X + CTL_W - 10 - font_width(&st->small, m.b), by + 19, m.b,
                  lit ? rgb(220, 230, 255) : rgb(120, 120, 130));
    }
    font_text(s, &st->bold, CTL_X, LED_Y - 12, "Activity light", rgb(30, 30, 36));
    button(st, CTL_X, LED_Y, 66, "On", st->led == 1);
    button(st, CTL_X + 72, LED_Y, 66, "Off", st->led == 0);
    font_text(s, &st->small, 24, SH - 12,
              "Only Settings can change these, and only to these choices: proved in Lean.",
              rgb(120, 120, 130));
}

static void log_board(struct line *l, const char *what, struct res r) {
    put_s(l, "settings: ");
    put_s(l, what);
    put_s(l, outcome(r.status));
    put_s(l, "\n");
    flush(l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct settings *st = (struct settings *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->bold = font_of(assets, F_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->win = app_surface(SW, SH);
    st->chosen = 0;
    st->speed = -1;
    st->led = -1;
    read_board(st);
    read_sensors(st);
    st->refreshed = sys0(SYS_TIME).x[2];
    draw(st);
    u64 opened = app_open(SW, SH, "Settings");
    put_s(&l, "settings: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    put_s(&l, "settings: ");
    if (st->have_board) {
        put_s(&l, model_of(st->revision));
        put_s(&l, ", revision ");
        put_hex(&l, st->revision);
    } else put_s(&l, "the board did not answer");
    if (st->have_sensors) {
        put_s(&l, ", ");
        put_fixed1(&l, st->millideg);
        put_s(&l, " C, CPU at ");
        put_dec(&l, st->arm_hz / 1000000);
        put_s(&l, " MHz");
    }
    put_s(&l, "\n");
    flush(&l);

    int dirty = 0;
    for (;;) {
        /* Poll, so the temperature and clock can refresh every two seconds. */
        struct event e = app_poll(dirty);
        dirty = 0;
        if (e.kind == EV_NONE) {
            u64 now = sys0(SYS_TIME).x[2];
            if (now - st->refreshed >= 2000) {
                read_sensors(st);
                st->refreshed = now;
                draw(st);
                dirty = 1;
            } else sleep_ms(100);
            continue;
        }
        if (e.kind == EV_CLOSE) {
            put_s(&l, "settings: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind != EV_DOWN) continue;
        int x = (int)e.a, y = (int)e.b;
        for (int i = 0; i < NBG; i++) {
            if (x < swatch_x(i) || x >= swatch_x(i) + SWATCH_W || y < SWATCH_Y || y >= SWATCH_Y + SWATCH_H) continue;
            struct res r = sys(SYS_CALL, ENDPOINT, OP_SET, SET_BACKGROUND, (u64)i, 0);
            u64 ok = r.status == OK && r.x[1] == 0 ? OK : BAD_ARG;
            put_s(&l, "settings: background set to ");
            put_s(&l, bg_names[i]);
            put_s(&l, outcome(ok));
            put_s(&l, "\n");
            flush(&l);
            if (ok == OK) {
                st->chosen = i;
                draw(st);
                dirty = 1;
            }
        }
        for (int i = 0; i < NSPEED; i++) {
            if (x < CTL_X || x >= CTL_X + CTL_W || y < seg_y(i) || y >= seg_y(i) + SEG_H) continue;
            struct res r = sys(SYS_BOARD, BOARD, BOARD_CPU, (u64)i, 0, 0);
            put_s(&l, "CPU speed ");
            put_dec(&l, speed_mhz[i]);
            put_s(&l, " MHz");
            l.b[l.n] = 0;
            char what[32];
            for (u64 k = 0; k <= l.n && k < sizeof what; k++) what[k] = l.b[k];
            l.n = 0;
            log_board(&l, what, r);
            if (r.status == OK) {
                st->speed = i;
                read_sensors(st);
                put_s(&l, "settings: the firmware reports the CPU at ");
                put_dec(&l, r.x[1] / 1000000);
                put_s(&l, " MHz\n");
                flush(&l);
                draw(st);
                dirty = 1;
            }
        }
        for (int on = 1; on >= 0; on--) {
            int bx = on ? CTL_X : CTL_X + 72;
            if (x < bx || x >= bx + 66 || y < LED_Y || y >= LED_Y + SEG_H) continue;
            struct res r = sys(SYS_BOARD, BOARD, BOARD_LED, (u64)on, 0, 0);
            log_board(&l, on ? "activity light on" : "activity light off", r);
            if (r.status == OK) {
                st->led = on;
                draw(st);
                dirty = 1;
            }
        }
    }
}
