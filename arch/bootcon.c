/*
 * Boot progress, for the first boot on a board: every step kmain takes is announced before
 * it runs, on each output that may work, so whatever works shows where the boot is or where
 * it stopped.
 *
 *   - Serial: "leanos: [n/13] what" before step n; the kernel's own lines give the results.
 *   - Screen: once the framebuffer exists, everything the kernel prints during boot is drawn
 *     as text (the panic screen's 5x7 font), until the display server takes the screen.
 *   - The green activity LED (GPIO 42 on a Pi 4, plain GPIO: no mailbox, no MMU, no UART):
 *     on from kmain's first line until the display server takes over; a panic blinks its
 *     step forever. In a bring-up build (make pi-bringup) each step also blinks its number
 *     before it runs. QEMU's normal build has no LED code at all, so its timing is untouched.
 *     arch/boot.S lights the same LED, steady, when the kernel finds itself loaded at the
 *     wrong address and parks; the bring-up build's dark second and first blink at step 1
 *     tell that from a kernel that runs.
 *
 * Trusted, not proved (TRUST.md), and it decides nothing: it only reports. It draws only
 * before the first task runs and while stopping, as the panic screen does, and it pushes
 * every pixel it draws out of the cache at once, so no dirty line of the kernel's cached
 * view of the framebuffer is left to land over what the display server draws later.
 */
#include "arch.h"
#include "bootcon.h"
#include "font.h"

static const char *const stage_names[BOOT_STAGES + 1] = {
    "",
    "serial console: PL011 on GPIO 14/15, 115200 8N1",
    "board: the firmware's mailbox; revisions, RAM, USB power",
    "Lean runtime: initializing the kernel's Lean code",
    "framebuffer: asking the firmware's mailbox for the screen",
    "MMU: kernel page tables, then the caches",
    "SD card: EMMC2, then EMMC; the partition table",
    "Lean kernel: the first state, from the boot manifest",
    "memory: clearing the task frames; SHA-256 self-test",
    "programs: loading each, checking it against the manifest",
    "page tables: every task's address space",
    "interrupts: the GIC-400 and the 10 ms timer",
    "cores 1-3: releasing them from the spin table",
    "first task: the display server takes the screen",
};

static unsigned stage;          /* the step the boot is in: 0 before the first */
int bootcon_on = 1;             /* the kernel's lines are recorded until the boot ends */

/* ---- the clock and the green LED ---- */

#if !defined(LEANOS_QEMU) || defined(LEANOS_BRINGUP)
#define HAVE_LED 1
#define GPFSEL4 (PERIPHERAL_BASE + 0x200010)
#define GPSET1 (PERIPHERAL_BASE + 0x200020)
#define GPCLR1 (PERIPHERAL_BASE + 0x20002C)

static void led(int on) {
    mmio_w32(GPFSEL4, (mmio_r32(GPFSEL4) & ~(7u << 6)) | (1u << 6));   /* GPIO 42: output */
    mmio_w32(on ? GPSET1 : GPCLR1, 1u << 10);
}

static void wait_ms(uint64_t ms) { delay_us(ms * 1000); }
#endif

void boot_led_on(void) {
#ifdef HAVE_LED
    led(1);
#endif
}

#ifdef LEANOS_BRINGUP
/* Bring-up builds: a second dark, `n` short blinks, then on while the step runs. */
static unsigned led_shown;
static uint64_t step_began;

/* Bring-up builds: how long the step that just ended took (its blinks not counted). */
static void step_time(unsigned n) {
    if (!step_began) return;
    kputs("leanos: step ");
    kputdec(n);
    kputs(" took ");
    kputdec((timer_now() - step_began) * 1000 / timer_hz());
    kputs(" ms\n");
}

void boot_led_code(unsigned n) {
    led(0);
    wait_ms(1000);
    for (unsigned k = 0; k < n; k++) {
        led(1);
        wait_ms(150);
        led(0);
        wait_ms(250);
    }
    led(1);
    led_shown = n;
}
#else
void boot_led_code(unsigned n) { (void)n; }
#endif

/* ---- the screen ---- */

#define SCALE 2
#define CHAR_W (6 * SCALE)
#define ROW_H 18
#define LEFT 40
#define TOP 114                 /* the first row of the log */
#define MAX_ROWS 32             /* 26 fit on a 600-line screen */
#define ROW_CHARS 78            /* (1024 - 2 * LEFT) / CHAR_W, for a 1024-wide screen */

#define BG 0x14161e
#define FG_TITLE 0xffffff
#define FG_NOTE 0x9aa0b4
#define FG_STAGE 0xf2f3f7
#define FG_TEXT 0xb4b9c8
#define FG_OK 0x5fd38d
#define FG_BAD 0xff7a6b

enum { ROW_TEXT, ROW_STAGE, ROW_BAD };
static struct { char t[ROW_CHARS + 1]; uint8_t kind, done; } rows[MAX_ROWS];
static unsigned nrows;
static int stage_row = -1;      /* the row of the step now running, while it is on screen */

static char line[160];          /* the line being printed */
static unsigned line_len;

static uint32_t *fb;            /* 0 until the framebuffer exists */
static uint32_t fb_w, fb_h, fb_stride;
static unsigned fit = MAX_ROWS;     /* rows that fit on the screen */

/* Push a band of screen rows out to where the display reads them, and drop them from
   the cache (with the MMU off this only waits for the writes). */
static void flush_rows(uint32_t y0, uint32_t y1) {
    if (y1 > fb_h) y1 = fb_h;
    if (y0 >= y1) return;
    uint64_t a = (uint64_t)(fb + (uint64_t)y0 * fb_stride) & ~63UL;
    uint64_t end = (uint64_t)(fb + (uint64_t)y1 * fb_stride);
    for (; a < end; a += 64) __asm__ volatile("dc civac, %0" :: "r"(a) : "memory");
    DSB(sy);
}

static void fill(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t c) {
    if (x >= fb_w || y >= fb_h) return;
    if (x + w > fb_w) w = fb_w - x;
    if (y + h > fb_h) h = fb_h - y;
    for (uint32_t j = y; j < y + h; j++)
        for (uint32_t i = x; i < x + w; i++) fb[(uint64_t)j * fb_stride + i] = c;
}

/* Text on one line, cut at the screen's right margin. */
static void text(uint32_t x, uint32_t y, uint32_t scale, const char *t, uint32_t c) {
    for (; *t; t++, x += 6 * scale) {
        if (x + 6 * scale > fb_w || y + 7 * scale > fb_h) return;
        unsigned ch = (unsigned char)*t;
        if (ch < 32 || ch > 126) ch = '?';
        const unsigned char *g = font5x7[ch - 32];
        for (uint32_t r = 0; r < 7 * scale; r++)
            for (uint32_t k = 0; k < 5 * scale; k++)
                if (g[r / scale] & (16 >> (k / scale))) fb[(uint64_t)(y + r) * fb_stride + x + k] = c;
    }
}

static uint32_t row_y(unsigned r) { return TOP + r * ROW_H; }

static void draw_row(unsigned r) {
    uint32_t y = row_y(r);
    fill(0, y, fb_w, ROW_H, BG);
    uint32_t color = rows[r].kind == ROW_STAGE ? FG_STAGE : rows[r].kind == ROW_BAD ? FG_BAD : FG_TEXT;
    text(rows[r].kind == ROW_STAGE ? LEFT : LEFT + 2 * CHAR_W, y + 2, SCALE, rows[r].t, color);
    if (rows[r].done) text(fb_w - LEFT - 2 * CHAR_W, y + 2, SCALE, "ok", FG_OK);
}

/* "WORDS n of 13" into s (n below 100). */
static void step_of(char *s, const char *words, unsigned n) {
    unsigned k = 0;
    while (*words) s[k++] = *words++;
    if (n >= 10) s[k++] = (char)('0' + n / 10);
    s[k++] = (char)('0' + n % 10);
    const char *of = " of ";
    while (*of) s[k++] = *of++;
    s[k++] = (char)('0' + BOOT_STAGES / 10);
    s[k++] = (char)('0' + BOOT_STAGES % 10);
    s[k] = 0;
}

static void draw_progress(void) {
    char s[24];
    step_of(s, "step ", stage);
    fill(fb_w - LEFT - 13 * CHAR_W, 34, 13 * CHAR_W, 7 * SCALE, BG);
    text(fb_w - LEFT - 13 * CHAR_W, 34, SCALE, s, FG_NOTE);
    uint32_t bar = fb_w - 2 * LEFT;
    fill(LEFT, 100, bar, 4, 0x2a2e3a);
    fill(LEFT, 100, bar * stage / BOOT_STAGES, 4, FG_OK);
}

static void draw_all(void) {
    fill(0, 0, fb_w, fb_h, BG);
    text(LEFT, 26, 3, "leanos is starting", FG_TITLE);
    text(LEFT, 66, SCALE, "Each step shows before it runs: the last one is where the boot is.", FG_NOTE);
    draw_progress();
    for (unsigned r = 0; r < nrows; r++) draw_row(r);
    flush_rows(0, fb_h);
}

/* Make room for one more row: a full screen keeps its last three quarters, moved up. */
static void scroll(void) {
    unsigned keep = fit * 3 / 4, drop = nrows - keep;
    for (unsigned r = 0; r < keep; r++) rows[r] = rows[drop + r];
    stage_row = stage_row >= (int)drop ? stage_row - (int)drop : -1;
    nrows = keep;
    if (fb) {
        for (unsigned r = 0; r < fit; r++) fill(0, row_y(r), fb_w, ROW_H, BG);
        for (unsigned r = 0; r < nrows; r++) draw_row(r);
        flush_rows(row_y(0), row_y(fit));
    }
}

/* A row of the log: kept, and drawn if the screen is up. */
static void add_row(const char *t, unsigned n, uint8_t kind) {
    if (nrows >= fit) scroll();
    unsigned r = nrows++;
    for (unsigned k = 0; k < n; k++) rows[r].t[k] = t[k];
    rows[r].t[n] = 0;
    rows[r].kind = kind;
    rows[r].done = 0;
    if (kind == ROW_STAGE) stage_row = (int)r;
    if (fb) {
        draw_row(r);
        flush_rows(row_y(r), row_y(r) + ROW_H);
    }
}

static int has(const char *s, unsigned n, const char *w) {
    for (unsigned i = 0; i < n; i++) {
        unsigned k = 0;
        while (w[k] && i + k < n && s[i + k] == w[k]) k++;
        if (!w[k]) return 1;
    }
    return 0;
}

/* A whole line printed: without its "leanos: ", in rows of ROW_CHARS. */
static void end_line(void) {
    const char *s = line;
    unsigned n = line_len;
    line_len = 0;
    const char *pre = "leanos: ";
    unsigned k = 0;
    while (pre[k] && k < n && s[k] == pre[k]) k++;
    if (!pre[k]) { s += k; n -= k; }
    if (n == 0) return;
    uint8_t kind = s[0] == '[' ? ROW_STAGE
                 : has(s, n, "PANIC") || has(s, n, "exception") || has(s, n, "refused") || has(s, n, "no ") ||
                   has(s, n, "stopped") || has(s, n, "not ") ? ROW_BAD : ROW_TEXT;
    unsigned width = ROW_CHARS - 3;         /* stages leave room for "ok", the rest are indented */
    while (n > 0) {
        unsigned m = n < width ? n : width;
        add_row(s, m, kind);
        s += m;
        n -= m;
    }
}

/* Every character the kernel prints while bootcon_on is set (kputc). */
void bootcon_putc(char c) {
    if (c == '\r') return;
    if (c == '\n') { end_line(); return; }
    if ((unsigned char)c == 0xc2) return;                   /* the first byte of the copyright sign */
    if ((unsigned char)c == 0xa9 && line_len + 3 <= sizeof line) {   /* the sign itself */
        line[line_len++] = '(';
        line[line_len++] = 'c';
        c = ')';
    }
    if (line_len < sizeof line) line[line_len++] = c;
}

void bootcon_start(uint32_t *base, uint32_t w, uint32_t h, uint32_t stride) {
    fb_w = w;
    fb_h = h;
    fb_stride = stride;
    fb = base;
    fit = h > TOP + ROW_H ? (h - TOP - 4) / ROW_H : 1;
    if (fit > MAX_ROWS) fit = MAX_ROWS;
    while (nrows > fit) scroll();
    draw_all();
}

/* The display server takes the screen: the kernel draws no more (the display server paints
   every pixel with its boot screen), and the LED goes dark. */
void bootcon_end(void) {
#ifdef LEANOS_BRINGUP
    step_time(stage);
#endif
    if (stage_row >= 0 && fb) {
        rows[stage_row].done = 1;
        draw_row((unsigned)stage_row);
        flush_rows(row_y((unsigned)stage_row), row_y((unsigned)stage_row) + ROW_H);
    }
    fb = 0;
    bootcon_on = 0;
    stage = STAGE_RUNNING;
#ifdef HAVE_LED
    led(0);
#endif
}

/* ---- the steps ---- */

void boot_stage(unsigned n) {
#ifdef LEANOS_BRINGUP
    step_time(stage);
    if (led_shown != n) boot_led_code(n);
#endif
    if (stage_row >= 0) {                   /* the step before is done */
        rows[stage_row].done = 1;
        if (fb) {
            draw_row((unsigned)stage_row);
            flush_rows(row_y((unsigned)stage_row), row_y((unsigned)stage_row) + ROW_H);
        }
    }
    stage = n;
    if (fb) {
        draw_progress();
        flush_rows(0, TOP);
    }
    kputs("leanos: [");
    kputdec(n);
    kputs("/");
    kputdec(BOOT_STAGES);
    kputs("] ");
    kputs(stage_names[n]);
    kputs("\n");
#ifndef LEANOS_QEMU
    /* Wait (10 ms at most: 16 characters take 1.4) until the line has left the UART, so it
       is out even if the step hangs the machine (a bus that locks up takes the UART's clock
       with it). */
    for (uint64_t d = deadline_us(10000); (mmio_r32(UART0 + 0x18) & (1u << 3)) && !passed(d);) {}
#endif
#ifdef LEANOS_BRINGUP
    step_began = timer_now();
#endif
}

/* kputc gave up on the UART (its transmit FIFO stayed full for 20 ms): the screen says so,
   once, since the serial line will not. */
void bootcon_uart_stuck(void) {
    static int said;
    if (said || !bootcon_on) return;
    said = 1;
    const char *m = "serial: the UART takes no characters; serial output is dropped";
    unsigned n = 0;
    while (m[n]) n++;
    add_row(m, n, ROW_BAD);
}

/* ---- bring-up builds: what the firmware says about the board ---- */

#ifdef LEANOS_BRINGUP
static void put_tag(const char *what, uint32_t tag, uint32_t in, int nin, int word, int dec) {
    uint32_t o[2] = {0, 0};
    kputs(what);
    if (!mbox_tag(tag, &in, nin, o, 2)) kputs("(no answer)");
    else if (dec) kputdec(o[word]);
    else kputhex(o[word]);
}

void boot_board_info(void) {
    kputs("leanos: bring-up build: MIDR ");
    kputhex(SYSREG_READ(midr_el1));
    kputs(", SCTLR ");
    kputhex(SYSREG_READ(sctlr_el1));
    kputs("\n");
    put_tag("leanos: clocks, Hz: EMMC2 ", 0x00030002, 12, 1, 1, 1);
    put_tag(", ARM ", 0x00030002, 3, 1, 1, 1);
    put_tag(", core ", 0x00030002, 4, 1, 1, 1);
    put_tag(", ARM max ", 0x00030004, 3, 1, 1, 1);
    kputs("\n");
    uint32_t id = 0, t[2];
    kputs("leanos: SoC temperature ");
    if (mbox_tag(0x00030006, &id, 1, t, 2)) {
        kputdec(t[1] / 1000);
        kputs(" C\n");
    } else kputs("(no answer)\n");
}
#else
void boot_board_info(void) {}
#endif

/* ---- stopping ---- */

static char msg[200];
static unsigned msg_len;

static void m_s(const char *s) {
    while (*s && msg_len < sizeof msg - 1) msg[msg_len++] = *s++;
    msg[msg_len] = 0;
}
static void m_hex(uint64_t v) {
    m_s("0x");
    int started = 0;
    for (int i = 60; i >= 0; i -= 4) {
        int d = (v >> i) & 15;
        if (d || started || i == 0) {
            char c[2] = {"0123456789abcdef"[d], 0};
            m_s(c);
            started = 1;
        }
    }
}

/* Exception classes (ESR_EL1 bits 31-26) and fault status codes (bits 5-0, for aborts),
   as tables: tools/stackcheck.py follows no jump through a register it cannot resolve. */
static const struct { uint8_t code; const char *name; } ec_names[] = {
    {0x00, "undefined instruction"}, {0x01, "WFI or WFE trapped"},
    {0x07, "floating point or SIMD trapped"}, {0x0e, "illegal execution state"},
    {0x15, "system call (SVC)"}, {0x18, "system register access trapped"},
    {0x20, "instruction abort from user mode"}, {0x21, "instruction abort"},
    {0x22, "misaligned PC"}, {0x24, "data abort from user mode"}, {0x25, "data abort"},
    {0x26, "misaligned stack pointer"}, {0x2f, "SError (asynchronous external abort)"},
    {0x3c, "BRK instruction"},
};
static const struct { uint8_t code, levels; const char *name; } fault_names[] = {
    {0x00, 1, "address size fault"}, {0x04, 1, "translation fault"}, {0x08, 1, "access flag fault"},
    {0x0c, 1, "permission fault"}, {0x14, 1, "external abort on a table walk"},
    {0x10, 0, "external abort: no answer at that address"}, {0x18, 0, "parity or ECC error"},
    {0x21, 0, "alignment fault"}, {0x30, 0, "TLB conflict"},
};

/* An exception in the kernel: the details on serial, and the message kpanic shows. */
const char *boot_exception(uint64_t kind, uint64_t esr, uint64_t elr, uint64_t far) {
    uint64_t ec = esr >> 26, fsc = esr & 0x3f;
    const char *name = 0;
#pragma clang loop unroll(disable)
    for (unsigned i = 0; i < sizeof ec_names / sizeof ec_names[0]; i++)
        if (ec_names[i].code == ec) name = ec_names[i].name;
    msg_len = 0;
    m_s("exception in the kernel: ");
    m_s(kind == 2 ? "" : kind == 3 ? "IRQ; " : "FIQ, SError or unused vector; ");
    if (name) m_s(name);
    else { m_s("exception class "); m_hex(ec); }
    if ((ec & ~5UL) == 0x20) {                  /* 0x20, 0x21, 0x24, 0x25: the aborts */
        m_s(" (");
        const char *what = "fault";
        int level = 0;
#pragma clang loop unroll(disable)
        for (unsigned i = 0; i < sizeof fault_names / sizeof fault_names[0]; i++)
            if (fault_names[i].levels ? (fsc & ~3UL) == fault_names[i].code : fsc == fault_names[i].code) {
                what = fault_names[i].name;
                level = fault_names[i].levels;
            }
        m_s(what);
        if (level) {
            char l[] = ", level 0";
            l[8] = (char)('0' + (fsc & 3));
            m_s(l);
        }
        if (ec >= 0x24) m_s(esr & (1 << 6) ? ", on a write" : ", on a read");
        m_s(")");
    }
    m_s(", ELR ");
    m_hex(elr);
    m_s(", FAR ");
    m_hex(far);
    m_s(", ESR ");
    m_hex(esr);
    return msg;
}

static int stopping;

/* kpanic starts: the boot console draws no more (the panic screen takes the screen), but
   still keeps the lines. A fault while stopping (a bad framebuffer, say) stops at once. */
void boot_panic_begin(void) {
    stopping++;
    if (stopping > 2) for (;;) __asm__ volatile("wfi");
    if (stopping == 2) {
        kputs("\nleanos: a fault while stopping; halted\n");
        boot_halt();
    }
    fb = 0;
}

void boot_panic_where(void) {
    if (stage == 0 || stage > BOOT_STAGES) {
        kputs(stage == 0 ? "leanos: stopped before the first boot step\n"
                         : "leanos: stopped after boot, while running tasks\n");
        return;
    }
    kputs("leanos: stopped in boot step [");
    kputdec(stage);
    kputs("/");
    kputdec(BOOT_STAGES);
    kputs("] ");
    kputs(stage_names[stage]);
    kputs("\n");
}

/* Below the panic screen's message: the step, and the last lines the boot printed. */
void boot_panic_screen(uint32_t *base, uint32_t w, uint32_t h, uint32_t stride, uint32_t y) {
    fb = base;
    fb_w = w;
    fb_h = h;
    fb_stride = stride;
    if (stage >= 1 && stage <= BOOT_STAGES) {
        char s[32];
        step_of(s, "In boot step ", stage);
        text(40, y, SCALE, s, 0xffffff);
        text(40, y + 24, SCALE, stage_names[stage], 0xffffff);
        unsigned first = nrows > 10 ? nrows - 10 : 0;
        for (unsigned r = first; r < nrows; r++)
            text(rows[r].kind == ROW_STAGE ? 40 : 40 + 2 * CHAR_W, y + 64 + (r - first) * ROW_H, SCALE, rows[r].t,
                 rows[r].kind == ROW_BAD ? 0xffb4a8 : 0x9aa0b4);
    } else if (stage > BOOT_STAGES) {
        text(40, y, SCALE, "After boot, while running tasks.", 0xc8cad4);
    }
    fb = 0;
}

/* Stop for good. On a Pi, the LED says which step: a burst of fast flickers, then one slow
   blink per step number (13 after boot), over and over. QEMU ends the run instead. */
void boot_halt(void) {
#ifdef LEANOS_QEMU
    poweroff();
#else
    unsigned n = stage ? stage : 1;
    for (;;) {
        for (int k = 0; k < 10; k++) {
            led(1);
            wait_ms(50);
            led(0);
            wait_ms(50);
        }
        wait_ms(1000);
        for (unsigned k = 0; k < n; k++) {
            led(1);
            wait_ms(400);
            led(0);
            wait_ms(400);
        }
        wait_ms(2000);
    }
#endif
}
