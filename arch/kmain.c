/*
 * The machine layer: boots the board, owns the hardware, and carries out what the Lean
 * kernel decides. It makes no access decisions of its own. The only state it keeps
 * beyond hardware is each task's saved registers.
 *
 * Trusted, not proved (see TRUST.md). The rule for this file: if a check here would ever
 * change an outcome, the check belongs in LeanOS/Kernel.lean instead. The checks it does
 * make (frame and page bounds when writing page tables) are there only to stop the
 * machine if this layer and the Lean kernel ever disagree.
 */
#include <lean/lean.h>
#include "arch.h"
#include "bootcon.h"

/* ---- the Lean kernel (LeanOS/Kernel.lean) ---- */
lean_object *initialize_leanos_LeanOS_Kernel(uint8_t builtin);
lean_object *leanos_init(lean_object *fb_base);
lean_object *leanos_syscall(lean_object *s, lean_object *num, lean_object *a0, lean_object *a1,
                            lean_object *a2, lean_object *a3, lean_object *a4);
lean_object *leanos_tick(lean_object *s);
lean_object *leanos_fault(lean_object *s);
lean_object *leanos_clear_result(lean_object *s, lean_object *j);
lean_object *leanos_verify(lean_object *s, lean_object *i, lean_object *w0, lean_object *w1, lean_object *w2,
                           lean_object *w3, lean_object *w4, lean_object *w5, lean_object *w6, lean_object *w7);
lean_object *leanos_cur(lean_object *s);
uint8_t leanos_ready(lean_object *s, lean_object *i);
uint8_t leanos_dead(lean_object *s, lean_object *i);
lean_object *leanos_ntasks(lean_object *s);
lean_object *leanos_result_len(lean_object *s, lean_object *j);
lean_object *leanos_result(lean_object *s, lean_object *j, lean_object *k);
lean_object *leanos_kernel_l1(lean_object *k);
lean_object *leanos_l1(lean_object *l2, lean_object *k);
lean_object *leanos_l2(lean_object *l3, lean_object *k);
lean_object *leanos_l3_table(lean_object *s, lean_object *i);
lean_object *leanos_reply_out_va(lean_object *r);
lean_object *leanos_reply_out_len(lean_object *r);
uint8_t leanos_reply_remap(lean_object *r);
lean_object *leanos_reply_load(lean_object *r);
lean_object *leanos_reply_io(lean_object *r);
lean_object *leanos_reply_load_len(lean_object *r);
lean_object *leanos_reply_power(lean_object *r);
uint8_t leanos_open_slot(lean_object *i);
lean_object *leanos_reply_io_block(lean_object *r);
lean_object *leanos_io_failed(lean_object *s);
lean_object *leanos_reply_board(lean_object *r);
lean_object *leanos_reply_usb_op(lean_object *r);
lean_object *leanos_reply_usb_a(lean_object *r);
lean_object *leanos_reply_usb_b(lean_object *r);
lean_object *leanos_reply_usb_c(lean_object *r);
lean_object *leanos_reply_usb_d(lean_object *r);
lean_object *leanos_usb_done(lean_object *s, lean_object *v);
lean_object *leanos_enter(lean_object *s, lean_object *c, lean_object *b0, lean_object *b1, lean_object *b2);
lean_object *leanos_schedule(lean_object *s);
lean_object *leanos_rotate(lean_object *s);
uint8_t leanos_runnable(lean_object *s, lean_object *j);
lean_object *leanos_board_done(lean_object *s, lean_object *a, lean_object *b, lean_object *c,
                               lean_object *d, lean_object *e);
int sd_init(void);
uint64_t sd_partition(void);
int sd_part_read(uint64_t block, void *dst);
int sd_part_write(uint64_t block, const void *src);
uint8_t leanos_autostart(lean_object *i);
lean_object *leanos_reply_state(lean_object *r);
lean_object *leanos_reply_unmask(lean_object *r);
lean_object *leanos_irq(lean_object *s, lean_object *n);
lean_object *leanos_irq_line_count(lean_object *unused);
lean_object *leanos_irq_line(lean_object *k);
lean_object *leanos_fb_width(lean_object *unused);
lean_object *leanos_fb_height(lean_object *unused);
lean_object *leanos_fb_pages(lean_object *unused);

uint64_t rt_heap_live(void);
uint64_t rt_heap_peak(void);

/* The kernel state. This layer holds one reference to it; exported Lean functions consume
   their arguments, so a query passes a fresh reference (`K1`) and an update hands the
   state over and takes the new one back. */
static lean_object *K;
#define K1 (lean_inc(K), K)

/* Lean returns numbers as boxed scalars. Every number the kernel returns is small; a
   big one would mean the runtime and the kernel disagree, so stop. */
static uint64_t nat(lean_object *o) {
    if (!lean_is_scalar(o)) kpanic("kernel returned a number outside the small range");
    return lean_unbox(o);
}

/* A user register becomes a Lean Nat, which this runtime keeps as a small number: below
   2^63, with no big numbers behind it (rt/runtime.c stops the machine on one). So what a
   task passes must not only fit, but keep fitting through whatever the kernel computes
   from it, or one system call with a huge argument would stop the machine.

   Message words (send and call: x1-x3; reply: x1-x3) are data the kernel only carries,
   never computes with: they keep their low 63 bits. Every other argument is an index, an
   address, a count, a length, a time or a set of rights, and none is valid at 2^40 or
   more; those clamp to 2^40, which every call refuses (a 2^40 ms sleep is 34 years), and
   which keeps every sum and product the kernel makes from arguments far below 2^63.
   test/fuzz.sh throws such arguments at every call. */
#define ARG_MAX (1ULL << 40)
static lean_object *arg(uint64_t v) { return lean_box(v < ARG_MAX ? v : ARG_MAX); }
static lean_object *msg_word(uint64_t v) { return lean_box(v & ~(1ULL << 63)); }
static int carries_words(uint64_t num) { return num == 8 || num == 10 || num == 11; }

static uint64_t cur_task(void) { return nat(leanos_cur(K1)); }
static int ready(uint64_t i) { return leanos_ready(K1, lean_box(i)); }

/* ---- console ---- */

/* Route the PL011 to the header's pins 8 and 10 (GPIO 14 TXD, 15 RXD): function ALT0, no
   pull on TX, a pull-up on RX so an unconnected line reads idle (BCM2711 datasheet, 5.3:
   GPFSEL1, GPIO_PUP_PDN_CNTRL_REG0). A Pi 4's firmware wires the PL011 to the Bluetooth
   chip on GPIO 30-33 (ALT3) and the mini UART to 14 and 15; leanos loads no device tree,
   so the disable-bt overlay that would move it cannot, and this does it instead. Pins 30-33
   are also taken off the PL011 (made inputs), so its receive line has one source, the
   header, and not the Bluetooth chip's transmit line too. */
#define GPIO_BASE (PERIPHERAL_BASE + 0x200000)
static void uart_pins(void) {
    uint32_t sel = mmio_r32(GPIO_BASE + 0x04);                 /* GPFSEL1: pins 10-19 */
    sel &= ~((7u << 12) | (7u << 15));
    sel |= (4u << 12) | (4u << 15);                            /* ALT0 for 14 and 15 */
    mmio_w32(GPIO_BASE + 0x04, sel);
    uint32_t pull = mmio_r32(GPIO_BASE + 0xe4);                /* pulls, pins 0-15 */
    pull &= ~((3u << 28) | (3u << 30));
    pull |= 1u << 30;                                          /* 15: pull-up */
    mmio_w32(GPIO_BASE + 0xe4, pull);
    uint32_t sel3 = mmio_r32(GPIO_BASE + 0x0c);                /* GPFSEL3: pins 30-39 */
    for (uint32_t k = 0; k < 4; k++)                           /* 30-33: ALT3 is the PL011 */
        if (((sel3 >> (3 * k)) & 7u) == 7u) sel3 &= ~(7u << (3 * k));
    mmio_w32(GPIO_BASE + 0x0c, sel3);
}

/* PL011 at 115200 8N1. Its clock is the firmware's UART clock (clock 2 in the mailbox's
   property interface): 48 MHz on a Pi 4 (config.txt: init_uart_clock=48000000), 3 MHz on
   QEMU, which ignores the divisor anyway. The divisor is clock / (16 x 115200), in 1/64ths:
   at 48 MHz, 26 + 3/64 (PL011 TRM, 3.3.6). If the firmware does not say, 48 MHz. */
#define UART_BAUD 115200
#define UART_CLOCK_DEFAULT 48000000u
static uint32_t uart_clock;
static int uart_clock_asked;        /* 1 if the firmware said what the clock is */

static void uart_init(void) {
    const uint32_t uart_clock_id = 2;
    uint32_t o[2] = {0, 0};
    uart_clock = UART_CLOCK_DEFAULT;
    if (mbox_tag(0x00030002, &uart_clock_id, 1, o, 2) && o[1] >= 1843200 && o[1] <= 200000000) {
        uart_clock = o[1];
        uart_clock_asked = 1;
    }
    uint32_t div64 = (uint32_t)(((uint64_t)uart_clock * 4 + UART_BAUD / 2) / UART_BAUD);
    /* PL011 TRM 3.3.8: disable, let the character being sent finish, flush the FIFOs (FEN
       off), then program. The divisor takes effect with the LCRH write after it. */
    mmio_w32(UART0 + 0x30, 0);                  /* CR: off while configuring */
    for (uint64_t d = deadline_us(10000); (mmio_r32(UART0 + 0x18) & (1u << 3)) && !passed(d);) {}
    mmio_w32(UART0 + 0x2c, 0);                  /* LCRH: FIFOs off, which empties them */
    mmio_w32(UART0 + 0x44, 0x7ff);              /* ICR: clear pending interrupts */
    mmio_w32(UART0 + 0x24, div64 >> 6);         /* IBRD */
    mmio_w32(UART0 + 0x28, div64 & 63);         /* FBRD */
    mmio_w32(UART0 + 0x2c, 0x70);               /* LCRH: 8 bits, FIFOs on */
    uart_pins();
    mmio_w32(UART0 + 0x30, 0x301);              /* CR: UART, transmit, receive on */
}

/* One character out. 32-bit writes only, as Linux's earlycon uses on the BCM2711 PL011
   (pl011,mmio32). The wait for room is bounded (at 115200 baud the 16-deep FIFO drains in
   under 2 ms): a UART that never takes a character (its clock off, say) drops the text
   instead of stopping the boot, so the screen can still say what happened; after one such
   drop it no longer waits at all. */
static int uart_stuck;
void kputc(char c) {
    if (bootcon_on) bootcon_putc(c);                 /* the boot console (arch/bootcon.c) */
    for (uint64_t d = deadline_us(20000); mmio_r32(UART0 + 0x18) & (1 << 5);)
        if (uart_stuck || passed(d)) {
            if (!uart_stuck) bootcon_uart_stuck();   /* said once, on the screen */
            uart_stuck = 1;
            return;
        }
    uart_stuck = 0;
    mmio_w32(UART0, (uint8_t)c);
}
void kputs(const char *s) {
    while (*s) {
        if (*s == '\n') kputc('\r');
        kputc(*s++);
    }
}
void kputhex(uint64_t v) {
    kputs("0x");
    int started = 0;
    for (int i = 60; i >= 0; i -= 4) {
        int d = (v >> i) & 15;
        if (d || started || i == 0) { kputc("0123456789abcdef"[d]); started = 1; }
    }
}
void kputdec(uint64_t v) {
    char b[21];
    int i = 20;
    b[i] = 0;
    do { b[--i] = '0' + v % 10; v /= 10; } while (v);
    kputs(b + i);
}

void poweroff(void) {
#ifdef LEANOS_QEMU
    /* Semihosting SYS_EXIT, so a test run under QEMU ends with a status. */
    static const uint64_t block[2] = {0x20026 /* ADP_Stopped_ApplicationExit */, 0};
    register uint64_t x0 __asm__("x0") = 0x18;
    register const uint64_t *x1 __asm__("x1") = block;
    __asm__ volatile("hlt #0xf000" :: "r"(x0), "r"(x1) : "memory");
#endif
    /* A Pi has no power switch the kernel can reach; stop here. */
    for (;;) __asm__ volatile("wfi");
}

/* Restart the whole machine through the power-management block's watchdog: a full reset
   in a few ticks. The same on a Pi 4 and on QEMU's model of it. */
#define PM_BASE (PERIPHERAL_BASE + 0x100000)
#define PM_RSTC (PM_BASE + 0x1c)
#define PM_WDOG (PM_BASE + 0x24)
#define PM_PASSWORD 0x5a000000u
static void restart(void) {
    mmio_w32(PM_WDOG, PM_PASSWORD | 10);
    mmio_w32(PM_RSTC, PM_PASSWORD | (mmio_r32(PM_RSTC) & ~0x30u) | 0x20u);
    for (;;) __asm__ volatile("wfi");
}

/* ---- the panic screen ----
 * A Pi on a desk has a monitor, not a serial cable: when the kernel stops, it says why on
 * the screen too, in the same 5x7 font the programs use, drawn straight into the
 * framebuffer. Nothing else runs by then, so nothing else is drawing. It draws with the
 * geometry the firmware returned (`fb_alloc`), row pitch included, so it can also say why
 * a framebuffer that is not the one asked for was refused. */
#include "font.h"

static uint32_t *panic_fb;
static uint32_t panic_w, panic_h, panic_stride;     /* pixels; the stride is the pitch / 4 */

static void panic_text(uint32_t x, uint32_t y, uint32_t scale, const char *t, uint32_t c) {
    for (; *t; t++, x += 6 * scale) {
        unsigned ch = (unsigned char)*t;
        if (ch < 32 || ch > 126) ch = '?';
        if (x + 6 * scale > panic_w - 40) { x = 40; y += 10 * scale; }
        if (y + 7 * scale > panic_h) return;
        const unsigned char *g = font5x7[ch - 32];
        for (uint32_t r = 0; r < 7 * scale; r++)
            for (uint32_t k = 0; k < 5 * scale; k++)
                if (g[r / scale] & (16 >> (k / scale))) panic_fb[(y + r) * panic_stride + x + k] = c;
    }
}

static void panic_screen(const char *msg) {
    if (!panic_fb) return;
    for (uint32_t y = 0; y < panic_h; y++)
        for (uint32_t x = 0; x < panic_w; x++) panic_fb[y * panic_stride + x] = y < 6 ? 0xe0483e : 0x1a1c26;
    panic_text(40, 60, 4, "leanos stopped", 0xffffff);
    panic_text(40, 120, 2, msg, 0xffb4a8);
    panic_text(40, 200, 2, "The kernel met something it cannot safely go on from,", 0xc8cad4);
    panic_text(40, 224, 2, "and stopped rather than guess. It wrote nothing after this.", 0xc8cad4);
    panic_text(40, 248, 2, "Switch the Pi off and on to start again.", 0xc8cad4);
    boot_panic_screen(panic_fb, panic_w, panic_h, panic_stride, 296);   /* the step, the boot's last lines */
    /* The kernel maps the framebuffer as cached memory: push the picture out to where the
       GPU reads it. */
    for (uint64_t a = (uint64_t)panic_fb & ~63UL; a < (uint64_t)(panic_fb + panic_stride * panic_h); a += 64)
        __asm__ volatile("dc cvac, %0" :: "r"(a) : "memory");
    __asm__ volatile("dsb sy" ::: "memory");
}

void kpanic(const char *msg) {
    boot_panic_begin();
    kputs("\nleanos: PANIC: ");
    kputs(msg);
    kputs("\n");
    boot_panic_where();
    panic_screen(msg);
    boot_halt();
}

/* ---- the firmware's mailbox ----
 * The VideoCore firmware's property interface (github.com/raspberrypi/firmware, wiki
 * "Mailbox property interface"): a buffer of tags in RAM, its address written to mailbox 1
 * on channel 8, the same word read back from mailbox 0 when the firmware has answered in
 * place. The firmware reads and writes RAM behind the ARM's caches, so the buffer is
 * cleaned out before and invalidated after, and it has 64-byte cache lines to itself (its
 * own alignment and size): a line shared with other data could be written back over the
 * answer. The address is given as the VideoCore sees RAM, through its uncached alias at
 * 0xC0000000, as Linux's firmware driver gives it (its dma-ranges on a Pi 4). Waits are
 * bounded in time: a firmware that never answers is reported, not waited for forever. */
#define MBOX (PERIPHERAL_BASE + 0xB880)
#define MBOX_WORDS 48

static volatile uint32_t mbox_buf[MBOX_WORDS] __attribute__((aligned(64)));

static void mbox_cache(void) {
    for (uint64_t a = (uint64_t)mbox_buf; a < (uint64_t)(mbox_buf + MBOX_WORDS); a += 64)
        __asm__ volatile("dc civac, %0" :: "r"(a) : "memory");
    __asm__ volatile("dsb sy" ::: "memory");
}

/* Send what is in mbox_buf and wait for the answer: 1 if the firmware answered and says
   the request as a whole succeeded. */
static int mbox_call(void) {
    mbox_cache();
    uint32_t msg = (0xC0000000u | (uint32_t)(uint64_t)mbox_buf) | 8;   /* channel 8: properties */
    uint64_t d = deadline_us(100000);
    while (mmio_r32(MBOX + 0x38) & 0x80000000)                          /* mailbox 1 full */
        if (passed(d)) return 0;
    mmio_w32(MBOX + 0x20, msg);
    d = deadline_us(1000000);
    for (;;) {
        if (passed(d)) return 0;
        if (mmio_r32(MBOX + 0x18) & 0x40000000) continue;               /* mailbox 0 empty */
        if (mmio_r32(MBOX) == msg) break;
    }
    mbox_cache();
    return mbox_buf[1] == 0x80000000;
}

/* Append a tag with up to two value words at word i of mbox_buf; returns the index of its
   first value word. The tag's response code is the word before it. */
static int mbox_put(int *i, uint32_t tag, uint32_t nwords, uint32_t a, uint32_t b) {
    int at = *i;
    mbox_buf[at] = tag;
    mbox_buf[at + 1] = nwords * 4;
    mbox_buf[at + 2] = 0;
    mbox_buf[at + 3] = a;
    if (nwords > 1) mbox_buf[at + 4] = b;
    *i = at + 3 + (int)nwords;
    return at + 3;
}
static int mbox_answered(int v) { return (mbox_buf[v - 1] & 0x80000000u) != 0; }

/* One property tag: `in` words go in, up to `nout` words come back in `out`. 1 if the
   firmware answered it. */
int mbox_tag(uint32_t tag, const uint32_t *in, int nin, uint32_t *out, int nout) {
    int n = nin > nout ? nin : nout, i = 0;
    if (n > MBOX_WORDS - 6) return 0;
    mbox_buf[i++] = 0;
    mbox_buf[i++] = 0;
    mbox_buf[i++] = tag;
    mbox_buf[i++] = (uint32_t)n * 4;
    mbox_buf[i++] = 0;
    for (int k = 0; k < n; k++) mbox_buf[i++] = k < nin ? in[k] : 0;
    mbox_buf[i++] = 0;
    mbox_buf[0] = (uint32_t)i * 4;
    if (!mbox_call() || !(mbox_buf[4] & 0x80000000)) return 0;
    for (int k = 0; k < nout; k++) out[k] = mbox_buf[5 + k];
    return 1;
}

/* ---- framebuffer ----
 * Asked of the VideoCore firmware through the mailbox, once, at boot, before anything
 * else runs. The mailbox is a DMA path (the firmware writes wherever the request says), so
 * it never leaves this layer: user space only ever sees the resulting pages, as frame
 * capabilities the Lean kernel hands out. The request is fixed: `fbWidth` x `fbHeight`,
 * 32 bits per pixel, from LeanOS/Kernel.lean.
 *
 * The display server draws `fbWidth` x 4 bytes per row into `fbPages` contiguous pages, so
 * the firmware's answer is checked, not assumed: the virtual size, the depth, a row pitch
 * of exactly `fbWidth` x 4 bytes (the firmware may pad rows; QEMU never does), the size,
 * and the address. What it returned is printed either way. If it gave a framebuffer that
 * is not the one asked for, but that can be drawn on, the machine stops with the reason on
 * the serial console and on that screen, drawn at the pitch the firmware gave; if it gave
 * none, leanos runs without a screen and says why. Also asked, and only reported if not
 * honored: pixel order BGR (tag 0x48006: 0), which is what makes a word 0x00RRGGBB, and
 * the alpha channel ignored (tag 0x48007: 2), since the display writes 0 in the top byte,
 * which with alpha in use could mean transparent. The address comes back as a VideoCore
 * bus address (0xC0000000 alias on a Pi 4): its low 30 bits are the ARM physical address,
 * in the first GiB, where the firmware keeps its own memory (gpu_mem). */
static char why_buf[160];
static int why_n;
static void why_s(const char *s) { while (*s && why_n < (int)sizeof why_buf - 1) why_buf[why_n++] = *s++; }
static void why_d(uint64_t v) {
    char b[21];
    int i = 20;
    b[i] = 0;
    do { b[--i] = (char)('0' + v % 10); v /= 10; } while (v);
    why_s(b + i);
}
static void why_x(uint64_t v) {
    char b[19];
    int i = 18;
    b[i] = 0;
    do { b[--i] = "0123456789abcdef"[v & 15]; v >>= 4; } while (v);
    b[--i] = 'x';
    b[--i] = '0';
    why_s(b + i);
}

static uint64_t fb_alloc(void) {
    const uint32_t FB_W = (uint32_t)nat(leanos_fb_width(lean_box(0)));
    const uint32_t FB_H = (uint32_t)nat(leanos_fb_height(lean_box(0)));
    const uint64_t FB_PAGES = nat(leanos_fb_pages(lean_box(0)));
    int i = 2;
    const int phys = mbox_put(&i, 0x48003, 2, FB_W, FB_H);     /* physical (screen) size */
    const int virt = mbox_put(&i, 0x48004, 2, FB_W, FB_H);     /* virtual size: what is drawn */
    const int offs = mbox_put(&i, 0x48009, 2, 0, 0);           /* virtual offset: none */
    const int depth = mbox_put(&i, 0x48005, 1, 32, 0);         /* bits per pixel */
    const int order = mbox_put(&i, 0x48006, 1, 0, 0);          /* pixel order: BGR */
    const int alpha = mbox_put(&i, 0x48007, 1, 2, 0);          /* alpha channel ignored */
    const int alloc = mbox_put(&i, 0x40001, 2, PAGE_SIZE, 0);  /* allocate, page-aligned */
    const int pitch = mbox_put(&i, 0x40008, 1, 0, 0);          /* bytes per row */
    mbox_buf[i++] = 0;                                          /* end tag */
    mbox_buf[0] = (uint32_t)i * 4;
    mbox_buf[1] = 0;
    if (!mbox_call() || !mbox_answered(alloc)) {
        kputs("leanos: no framebuffer: the firmware did not answer the request for one\n");
        return 0;
    }
    const uint32_t vw = mbox_buf[virt], vh = mbox_buf[virt + 1], bpp = mbox_buf[depth];
    const uint32_t bus = mbox_buf[alloc], size = mbox_buf[alloc + 1], row = mbox_buf[pitch];
    const uint64_t base = bus & 0x3FFFFFFF;                     /* bus address to ARM physical */
    kputs("leanos: the firmware's framebuffer: ");
    kputdec(vw); kputs("x"); kputdec(vh);
    kputs(" (screen "); kputdec(mbox_buf[phys]); kputs("x"); kputdec(mbox_buf[phys + 1]);
    kputs("), "); kputdec(bpp); kputs(" bits, pitch "); kputdec(row);
    kputs(mbox_buf[order] == 0 ? ", BGR" : ", RGB");
    kputs(", alpha mode "); kputdec(mbox_buf[alpha]);
    kputs(", "); kputdec(size); kputs(" bytes at bus address "); kputhex(bus); kputs("\n");
    if (bus == 0 || bpp != 32 || !mbox_answered(pitch)) {
        kputs("leanos: no framebuffer: the firmware did not give a 32-bit framebuffer\n");
        return 0;
    }
    /* Can it be drawn on (for the panic screen), whatever else is wrong with it? */
    if (vw >= 320 && vh >= 240 && row % 4 == 0 && row >= vw * 4 && (uint64_t)row * vh <= size &&
        base + size <= 0x40000000) {
        panic_fb = (uint32_t *)base;
        panic_w = vw;
        panic_h = vh;
        panic_stride = row / 4;
    }
    why_n = 0;
    if (vw != FB_W || vh != FB_H) {
        why_s("the firmware gave a ");
        why_d(vw); why_s("x"); why_d(vh); why_s(" framebuffer, not ");
        why_d(FB_W); why_s("x"); why_d(FB_H);
    } else if (row != FB_W * 4) {
        why_s("the firmware's framebuffer has rows of "); why_d(row);
        why_s(" bytes, not "); why_d(FB_W * 4); why_s(" (padding the display cannot draw with)");
    } else if (size < FB_PAGES * PAGE_SIZE) {
        why_s("the firmware's framebuffer is "); why_d(size); why_s(" bytes, not ");
        why_d(FB_PAGES * PAGE_SIZE);
    } else if (base & (PAGE_SIZE - 1)) {
        why_s("the firmware's framebuffer at "); why_x(base); why_s(" is not page-aligned");
    } else if (base < FRAME_BASE + NFRAMES * PAGE_SIZE || base + FB_PAGES * PAGE_SIZE > 0x40000000) {
        why_s("the firmware's framebuffer at "); why_x(base);
        why_s(" is not between the frame pool's end ("); why_x(FRAME_BASE + NFRAMES * PAGE_SIZE);
        why_s(") and 1 GiB");
    }
    if (why_n) {
        why_buf[why_n] = 0;
        kpanic(why_buf);
    }
    if (mbox_buf[order] != 0)
        kputs("leanos: the firmware kept RGB pixel order: red and blue will look swapped\n");
    if (mbox_answered(alpha) && mbox_buf[alpha] == 1)
        kputs("leanos: the firmware kept alpha reversed: leanos's pixels may be transparent, the screen black\n");
    if (mbox_buf[offs] != 0 || mbox_buf[offs + 1] != 0)
        kputs("leanos: the firmware kept a virtual offset: the picture may be shifted\n");
    panic_fb = (uint32_t *)base;
    return base;
}

/* ---- the board, checked at boot ----
 * What the rest of this layer relies on and QEMU would never show wrong, asked of the
 * firmware and printed, so a first boot on a real Pi says what it found: the board and
 * firmware (and that the mailbox answers at all), the UART's clock, the system counter's
 * rate, the RAM the firmware left the ARM (the kernel, its heap and the frame pool must
 * fit in it), and the USB controller's power. The DWC2 is in a power domain the firmware
 * controls (Linux's bcm2711 device tree: power-domains = <&power RPI_POWER_DOMAIN_USB>),
 * so it is switched on here (tag 0x28001, device 3, "on" and "wait"), before the USB
 * driver touches its registers. */
static void board_check(void) {
    uint32_t o[2] = {0, 0};
    if (mbox_tag(0x00010002, 0, 0, o, 1)) {
        kputs("leanos: board revision ");
        kputhex(o[0]);
        if (mbox_tag(0x00000001, 0, 0, o, 1)) { kputs(", firmware "); kputhex(o[0]); }
        kputs("\n");
    } else kputs("leanos: the firmware does not answer the mailbox\n");
    kputs("leanos: serial console: PL011, 115200 baud from a ");
    kputdec(uart_clock);
    kputs(uart_clock_asked ? " Hz clock (the firmware's)\n" : " Hz clock (assumed: the firmware did not say)\n");
    kputs("leanos: system counter: ");
    kputdec(timer_hz());
    kputs(SYSREG_READ(cntfrq_el0) ? " Hz\n" : " Hz (assumed: CNTFRQ_EL0 was not set)\n");
    if (mbox_tag(0x00010005, 0, 0, o, 2)) {
        kputs("leanos: RAM for the ARM: ");
        kputhex(o[0]);
        kputs(" to ");
        kputhex((uint64_t)o[0] + o[1]);
        kputs("\n");
        if (o[0] != 0 || o[1] < FRAME_BASE + NFRAMES * PAGE_SIZE) {
            why_n = 0;
            why_s("the firmware left the ARM RAM from ");
            why_x(o[0]);
            why_s(" to ");
            why_x((uint64_t)o[0] + o[1]);
            why_s("; leanos needs 0x0 to ");
            why_x(FRAME_BASE + NFRAMES * PAGE_SIZE);
            why_buf[why_n] = 0;
            kpanic(why_buf);
        }
    }
    const uint32_t usb_on[2] = {3, 3};
    if (mbox_tag(0x00028001, usb_on, 2, o, 2) && (o[1] & 3) == 1) kputs("leanos: USB controller powered on\n");
    else kputs("leanos: the firmware did not power the USB controller on; USB will not work\n");
}

/* ---- the board's settings ----
 * What Settings may ask of the Raspberry Pi, through the Lean kernel (`boardRequests`,
 * proved to be the only requests that ever arrive, and only from Settings): read the board,
 * read its sensors, switch the green activity light off or on, set the CPU clock to 600,
 * 1000 or 1500 MHz. Everything but the light goes through the firmware's mailbox, one tag
 * at a time; the light is GPIO 42 on a Pi 4. */


#define GPFSEL4 (PERIPHERAL_BASE + 0x200010)
#define GPSET1 (PERIPHERAL_BASE + 0x200020)
#define GPCLR1 (PERIPHERAL_BASE + 0x20002C)

/* Carry out board request `req` for the current task: 1 if done, with five numbers. */
static int board_request(uint64_t req, uint64_t v[5]) {
    uint32_t o[2] = {0, 0};
    for (int k = 0; k < 5; k++) v[k] = 0;
    if (req == 1) {                                  /* the board */
        if (!mbox_tag(0x00010002, 0, 0, o, 1)) return 0;
        v[0] = o[0];                                 /* revision code */
        if (mbox_tag(0x00010004, 0, 0, o, 2)) { v[1] = o[0]; v[2] = o[1]; }   /* serial */
        if (mbox_tag(0x00010005, 0, 0, o, 2)) v[3] = o[1] >> 20;               /* MB for the ARM */
        if (mbox_tag(0x00000001, 0, 0, o, 1)) v[4] = o[0];                     /* firmware */
        return 1;
    }
    if (req == 2) {                                  /* the sensors */
        const uint32_t id0 = 0, arm = 3;
        if (!mbox_tag(0x00030006, &id0, 1, o, 2)) return 0;
        v[0] = o[1];                                 /* thousandths of a degree C */
        if (mbox_tag(0x00030002, &arm, 1, o, 2)) v[1] = o[1];   /* the CPU clock, Hz */
        if (mbox_tag(0x00030004, &arm, 1, o, 2)) v[2] = o[1];   /* its maximum */
        if (mbox_tag(0x00030046, 0, 0, o, 1)) v[3] = o[0];      /* throttling flags */
        if (mbox_tag(0x0003000a, &id0, 1, o, 2)) v[4] = o[1];   /* the limit, thousandths */
        return 1;
    }
    if (req == 3 || req == 4) {                      /* the activity light: GPIO 42 */
        mmio_w32(GPFSEL4, (mmio_r32(GPFSEL4) & ~(7u << 6)) | (1u << 6));
        mmio_w32(req == 4 ? GPSET1 : GPCLR1, 1u << 10);
        return 1;
    }
    if (req == 600 || req == 1000 || req == 1500) {  /* the CPU clock, never above 1500 MHz */
        const uint32_t in[3] = {3, (uint32_t)req * 1000000u, 0};
        uint32_t out[2];
        if (!mbox_tag(0x00038002, in, 3, out, 2)) return 0;
        v[0] = out[1];
        return 1;
    }
    kpanic("a board request the kernel should never have made");
}

/* ---- the USB host controller ----
 * The Pi 4's DWC2 (behind the USB-C port; the USB-A ports are the VL805's, over PCIe). The
 * Lean kernel decides every access (`sysUsb`): this code only carries out a register read,
 * a register write it passed, or a channel start whose whole DMA range it checked lies in
 * the USB driver's own frames (`usb_dma_own_memory`). Two things are this layer's:
 *   - the controller sees RAM at bus address 0xC0000000 + physical (the VideoCore's
 *     uncached alias; QEMU's model maps it too), so a checked physical address is written
 *     with that offset;
 *   - the frames are cached memory, and the controller reads and writes RAM behind the
 *     cache: a started range is cleaned and invalidated before the start, and invalidated
 *     again just after the driver next reads that channel's interrupt register (which it
 *     does to learn the transfer is done, before it looks at the data). */
#define USB_BASE (PERIPHERAL_BASE + 0x980000)
#define USB_BUS 0xC0000000u

static struct { uint64_t pa, len; } usb_last[8];

static void cache_range(uint64_t pa, uint64_t len) {
    for (uint64_t a = pa & ~63UL; a < pa + len; a += 64) __asm__ volatile("dc civac, %0" :: "r"(a) : "memory");
    __asm__ volatile("dsb sy" ::: "memory");
}

/* Carry out a USB request the Lean kernel returned; for a read, hand the value back. */
static void usb_request(uint64_t op, uint64_t a, uint64_t b, uint64_t c, uint64_t d) {
    if (op == 1) {
        mmio_w32(USB_BASE + a, (uint32_t)b);
    } else if (op == 2) {
        if (a >= 8) kpanic("a USB channel the kernel should never have started");
        uint64_t len = (c & 0x7ffff) + 1024;          /* the size the kernel checked, slack included */
        cache_range(b, len);
        usb_last[a].pa = b;
        usb_last[a].len = len;
        mmio_w32(USB_BASE + 0x514 + 0x20 * a, USB_BUS | (uint32_t)b);
        mmio_w32(USB_BASE + 0x510 + 0x20 * a, (uint32_t)c);
        mmio_w32(USB_BASE + 0x500 + 0x20 * a, (uint32_t)d);
    } else if (op == 3) {
        /* The register first, then the invalidate: lines the CPU fetched (speculatively)
           while the transfer ran are dropped only after the register says it is done, so
           the driver cannot read data older than what the register told it. */
        uint32_t v = mmio_r32(USB_BASE + a);
        if (a >= 0x508 && a < 0x600 && (a - 0x508) % 0x20 == 0) {
            uint64_t n = (a - 0x508) / 0x20;
            DSB(sy);
            if (usb_last[n].len) cache_range(usb_last[n].pa, usb_last[n].len);
        }
        K = leanos_usb_done(K, lean_box(v));
    }
}

/* ---- memory management unit ----
 * The Lean kernel computes every translation-table word (`l1Word`, `l2Word`, and a task's
 * whole level-3 table at once, `l3Table`, in LeanOS/Kernel.lean); this layer only stores
 * them (`Stored` in LeanOS/Tables.lean). LeanOS/Tables.lean proves that, stored this way,
 * the tables give user mode exactly the task's mappings (`walk_eq_view`),
 * assuming the MMU is configured as LeanOS/Arm.lean describes, which `mmu_init` does:
 * 4 KiB granule, 39-bit addresses (T0SZ = 25), TTBR0 only (EPD1 = 1), WXN off.
 * Every task has its own tables and address-space number (ASID = task + 1). Kernel
 * addresses are identity-mapped, so a table's address here is its physical address. */

static uint64_t kl1[512] __attribute__((aligned(4096)));
static uint64_t tl1[MAX_TASKS][512] __attribute__((aligned(4096)));
static uint64_t tl2[MAX_TASKS][512] __attribute__((aligned(4096)));
static uint64_t tl3[MAX_TASKS][USER_PAGES] __attribute__((aligned(4096))); /* 16 tables each */

static uint64_t word(lean_object *w) {
    if (!lean_is_scalar(w)) kpanic("table word outside the small range");
    return lean_unbox(w);
}

static void tlb_flush_all(void) {
    DSB(ishst);
    __asm__ volatile("tlbi vmalle1is" ::: "memory");
    DSB(ish);
    ISB();
}

/* Every core turns its own MMU on, with the same kernel tables. Core 0 does it here;
   cores 1-3 do it in arch/boot.S (`secondary`), with the values this leaves in `mmu_regs`
   (MAIR, TCR, TTBR0, SCTLR), before they touch their stacks: until its MMU is on, a core's
   loads and stores bypass the caches, and core 0 has been running with them on, so a
   line of a new core's stack could be in a cache, older than what that core stored. */
uint64_t mmu_regs[8] __attribute__((aligned(64)));

static void mmu_enable_this_core(void) {
    /* Memory attribute 0: device nGnRE. 1: normal, write-back. 2: normal, not cached. */
    const uint64_t mair = (0x04UL << 0) | (0xffUL << 8) | (0x44UL << 16);
    SYSREG_WRITE(mair_el1, mair);
    uint64_t tcr = 25                /* T0SZ: 39-bit addresses */
                 | (1UL << 8)        /* inner write-back walks */
                 | (1UL << 10)       /* outer write-back walks */
                 | (3UL << 12)       /* inner shareable */
                 | (0UL << 14)       /* 4 KiB granule */
                 | (1UL << 23)       /* EPD1: no TTBR1 walks, the kernel lives in the low half */
                 | (1UL << 32);      /* 36-bit physical addresses */
    SYSREG_WRITE(tcr_el1, tcr);
    SYSREG_WRITE(ttbr0_el1, (uint64_t)kl1);
    ISB();
    tlb_flush_all();
    uint64_t sctlr = SYSREG_READ(sctlr_el1);
    sctlr &= ~(1UL << 19);                    /* WXN off, as the model assumes */
    sctlr |= (1 << 0) | (1 << 2) | (1 << 12); /* MMU, data cache, instruction cache */
    mmu_regs[0] = mair;
    mmu_regs[1] = tcr;
    mmu_regs[2] = (uint64_t)kl1;
    mmu_regs[3] = sctlr;
    SYSREG_WRITE(sctlr_el1, sctlr);
    ISB();
    /* Instructions fetched before, from memory, are dropped (as Linux does after turning
       the MMU on). */
    __asm__ volatile("ic iallu" ::: "memory");
    DSB(nsh);
    ISB();
}

static void mmu_init(void) {
    for (uint64_t k = 0; k < 512; k++) kl1[k] = word(leanos_kernel_l1(lean_box(k)));
    mmu_enable_this_core();
}

/* Task i's level-1 and level-2 tables never change. Set once at boot. */
static void tables_init(uint64_t i) {
    uint64_t l2 = (uint64_t)tl2[i], l3 = (uint64_t)tl3[i];
    for (uint64_t k = 0; k < 512; k++) {
        tl1[i][k] = word(leanos_l1(lean_box(l2), lean_box(k)));
        tl2[i][k] = word(leanos_l2(lean_box(l3), lean_box(k)));
    }
}

/* Rewrite task i's level-3 tables from the Lean state: one call returns all 8192 words
   (`l3Table`, made in one pass over the task's mappings), and word k goes to index k.
   `l3Table_spec` proves word k is `l3Word`'s, and `l3Table_size` that there are 8192, so
   the check below never fires unless this layer and the runtime disagree. Only level 3
   changes, so the kernel's own entries stay valid even when i is the task whose address
   space is live. */
static void build_user_pages(uint64_t i) {
    lean_object *t = leanos_l3_table(K1, lean_box(i));
    if (lean_is_scalar(t) || !lean_is_array(t) || lean_array_size(t) != USER_PAGES)
        kpanic("level-3 table of the wrong size");
    for (uint64_t k = 0; k < USER_PAGES; k++) tl3[i][k] = word(lean_array_get_core(t, k));
    lean_dec(t);
    tlb_flush_all();
}

static void switch_to(uint64_t i) {
    SYSREG_WRITE(ttbr0_el1, (uint64_t)tl1[i] | ((i + 1) << 48));
    ISB();
}

/* ---- interrupts and the timer ---- */

static uint64_t timer_interval;

static void timer_rearm(void) {
    SYSREG_WRITE(cntp_tval_el0, timer_interval);
    SYSREG_WRITE(cntp_ctl_el0, 1);
}

static void gic_enable(uint32_t id) { mmio_w32(GICD + 0x100 + 4 * (id / 32), 1u << (id % 32)); }
static void gic_disable(uint32_t id) { mmio_w32(GICD + 0x180 + 4 * (id / 32), 1u << (id % 32)); }

/* This core's own part of the controller: its timer's line and the wake-up interrupt
   (SGI 0) are banked per core, as is the CPU interface. */
#define SGI_WAKE 0
static void gic_this_core(void) {
    mmio_w8(GICD + 0x400 + TIMER_IRQ, 0x80);            /* priority */
    mmio_w8(GICD + 0x400 + SGI_WAKE, 0x80);
    gic_enable(TIMER_IRQ);
    gic_enable(SGI_WAKE);
    mmio_w32(GICC + 0x004, 0xff);                       /* accept every priority */
    mmio_w32(GICC + 0x000, 1);                          /* CPU interface on */
}

static void irq_init(void) {
    mmio_w32(GICD + 0x000, 1);                          /* distributor on */
    /* The lines the manifest hands to tasks as interrupt capabilities. */
    uint64_t lines = nat(leanos_irq_line_count(lean_box(0)));
    for (uint64_t k = 0; k < lines; k++) {
        uint32_t id = (uint32_t)nat(leanos_irq_line(lean_box(k)));
        if (id < 32 || id >= 1020) kpanic("interrupt line out of range");
        mmio_w8(GICD + 0x400 + id, 0x80);               /* priority */
        mmio_w8(GICD + 0x800 + id, 1);                  /* deliver to core 0 */
        gic_enable(id);
    }
    gic_this_core();
    timer_interval = timer_hz() / 100;                  /* 10 ms time slice, from CNTFRQ_EL0 */
    timer_rearm();
}

/* ---- tasks ---- */

static struct frame saved[MAX_TASKS];
static uint64_t code_len[MAX_TASKS], asset_len[MAX_TASKS];
static int started[MAX_TASKS];      /* loaded at least once */
static uint64_t ntasks;
static uint64_t syscalls, ticks, device_irqs;

/* ---- the cores ----
 * All four cores run tasks. The Lean kernel is one state, so one core at a time is in it:
 * a core takes the kernel lock as it enters from user mode and lets go just before it
 * returns. On the way in it tells the kernel which task it runs and which tasks the other
 * cores run (`enter`), so the kernel's decisions are about the right task, and it never
 * picks a task another core is running (`runnable`). */
#define NCORES 4
#define NONE MAX_TASKS                         /* a core running no task */
static volatile uint64_t core_task[NCORES];   /* what each core runs */
static volatile int core_in_user[NCORES];     /* the core is in user mode, running it */
static uint64_t cores_up = 1;
uint64_t core_stack_top[NCORES];               /* boot.S: each core's kernel stack */
static volatile uint32_t klock;
static uint64_t core_runs[NCORES];             /* times each core has left for a task */

static uint64_t this_core(void) { return SYSREG_READ(mpidr_el1) & 0xff; }

static void lock(void) {
    uint32_t t;
    __asm__ volatile("   sevl\n"
                     "1: wfe\n"
                     "2: ldaxr %w0, [%1]\n"
                     "   cbnz  %w0, 1b\n"
                     "   stxr  %w0, %w2, [%1]\n"
                     "   cbnz  %w0, 2b\n"
                     : "=&r"(t) : "r"(&klock), "r"(1) : "memory");
}

static void unlock(void) {
    __asm__ volatile("stlr wzr, [%0]\n sev" :: "r"(&klock) : "memory");
}

static void send_wake(uint64_t core) { mmio_w32(GICD + 0xf00, (1u << (16 + core)) | SGI_WAKE); }

/* Tell the Lean kernel what core `c` runs and what the others run. */
static void enter_lean(uint64_t c) {
    uint64_t b[NCORES - 1], n = 0;
    for (uint64_t o = 0; o < NCORES; o++)
        if (o != c) b[n++] = core_task[o];
    K = leanos_enter(K, lean_box(core_task[c]), lean_box(b[0]), lean_box(b[1]), lean_box(b[2]));
}

/* Take one interrupt from the controller. The timer ends a time slice, round robin (core
   0's also advances the clock); the wake-up interrupt only brings a core into the kernel; any
   other line is masked until its holder acknowledges it, and the Lean kernel decides who to
   wake (the task waiting for it, which then runs on this core at once). */
static void handle_irq(uint64_t c) {
    uint32_t iar = mmio_r32(GICC + 0x00c);
    uint32_t id = iar & 0x3ff;
    if (id == TIMER_IRQ) {
        timer_rearm();
        if (c == 0) {
            ticks++;
            K = leanos_tick(K);
        } else K = leanos_rotate(K);
    } else if (id < 16) {
    } else if (id < 1020) {
        device_irqs++;
        gic_disable(id);
        K = leanos_irq(K, lean_box(id));
    }
    if (id < 1020) mmio_w32(GICC + 0x010, iar);
}

extern const uint64_t user_progs[], user_prog_ends[];
extern const uint64_t user_assets[], user_asset_ends[];
extern const uint64_t open_assets[], open_assets_end[];   /* the fonts for the open slots */

static void sync_icache(uint64_t start, uint64_t len) {
    for (uint64_t a = start & ~63UL; a < start + len; a += 64)
        __asm__ volatile("dc cvau, %0" :: "r"(a) : "memory");
    DSB(ish);
    __asm__ volatile("ic iallu" ::: "memory");
    DSB(ish);
    ISB();
}

/* Load an open slot with the `len` bytes at `va` in the current task's memory (the task
   that started it): the Lean kernel checked every page of them is mapped readable there,
   in the address space as rebuilt after the start. Frames cleared first, as for any start. */
static void load_image(uint64_t i, uint64_t va, uint64_t len) {
    uint64_t base = FRAME_BASE + FRAMES_PER_TASK * i * PAGE_SIZE;
    memset((void *)base, 0, FRAMES_PER_TASK * PAGE_SIZE);
    if (len > CODE_PAGES * PAGE_SIZE) kpanic("program image larger than the code run");
    memcpy((void *)base, (const void *)va, len);
    sync_icache(base, len);
    code_len[i] = len;
    /* the shared fonts, at the start of the spare run, where built-in programs find theirs */
    uint64_t alen = open_assets_end[0] - open_assets[0];
    if (alen > SPARE_PAGES * PAGE_SIZE) kpanic("the open slots' assets are larger than the spare run");
    memcpy((void *)(base + SPARE_FIRST * PAGE_SIZE), (const void *)open_assets[0], alen);
    asset_len[i] = alen;
    memset(&saved[i], 0, sizeof saved[i]);
    saved[i].elr = USER_BASE;
    saved[i].sp = USER_BASE + USER_PAGES * PAGE_SIZE;
    saved[i].spsr = 0;
    started[i] = 1;
}

/* Load slot i's program into its frames, fresh: every frame cleared (nothing of a previous
   run survives), the code, the assets, and registers that start at the program's entry. */
static void load_program(uint64_t i) {
    uint64_t base = FRAME_BASE + FRAMES_PER_TASK * i * PAGE_SIZE; /* frame 256i, as `frameCaps` says */
    memset((void *)base, 0, FRAMES_PER_TASK * PAGE_SIZE);
    uint64_t len = user_prog_ends[i] - user_progs[i];
    code_len[i] = len;
    if (len > CODE_PAGES * PAGE_SIZE) kpanic("user program larger than its code run");
    memcpy((void *)base, (const void *)user_progs[i], len);
    sync_icache(base, len);
    /* The task's assets (fonts, icons, pictures), if any, at the start of its spare run,
       where `frameCaps` in LeanOS/Kernel.lean puts capability 3. */
    uint64_t alen = user_asset_ends[i] - user_assets[i];
    asset_len[i] = alen;
    if (alen > SPARE_PAGES * PAGE_SIZE) kpanic("assets larger than the spare run");
    memcpy((void *)(base + SPARE_FIRST * PAGE_SIZE), (const void *)user_assets[i], alen);
    memset(&saved[i], 0, sizeof saved[i]);
    saved[i].elr = USER_BASE;
    saved[i].sp = USER_BASE + USER_PAGES * PAGE_SIZE;
    saved[i].spsr = 0; /* EL0, interrupts on */
    started[i] = 1;
}

static const char *const names[] = {"alice", "display", "mallory", "carol", "input",
                                    "terminal", "settings", "security", "fs", "files",
                                    "slot 10", "slot 11", "slot 12", "slot 13", "slot 14", "slot 15",
                                    "apps", "usb"};
#define NPROGS 18   /* the kernel image's program table: slots 0-17 (empty for the open slots) */

/* SHA-256 of "abc", from FIPS 180-4: the hash must be right before anything relies on it. */
static void sha256_self_test(void) {
    static const uint32_t want[8] = {0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
                                     0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad};
    struct sha256 h;
    uint32_t got[8];
    sha256_init(&h);
    sha256_update(&h, "abc", 3);
    sha256_final(&h, got);
    for (int i = 0; i < 8; i++)
        if (got[i] != want[i]) kpanic("SHA-256 self-test failed");
}

/* Measure exactly what task i was loaded with, its code then its assets, where they now sit
   in its own frames, and let the Lean kernel decide whether it may run. */
static void measure_and_verify(uint64_t i) {
    struct sha256 h;
    uint32_t d[8];
    sha256_init(&h);
    sha256_update(&h, (const void *)(FRAME_BASE + FRAMES_PER_TASK * i * PAGE_SIZE), code_len[i]);
    sha256_update(&h, (const void *)(FRAME_BASE + (FRAMES_PER_TASK * i + SPARE_FIRST) * PAGE_SIZE), asset_len[i]);
    sha256_final(&h, d);
    K = leanos_verify(K, lean_box(i), lean_box(d[0]), lean_box(d[1]), lean_box(d[2]), lean_box(d[3]),
                      lean_box(d[4]), lean_box(d[5]), lean_box(d[6]), lean_box(d[7]));
    kputs("leanos: ");
    kputs(names[i]);
    if (ready(i) && leanos_open_slot(lean_box(i))) {
        kputs(" runs a program from its starter, not the manifest; sha256 ");
        kputhex(d[0]);
        kputs("...\n");
    } else if (ready(i)) {
        kputs(" verified, sha256 ");
        kputhex(d[0]);
        kputs("...\n");
    } else {
        kputs(" refused: what was loaded does not match the boot manifest\n");
    }
}

/* Slot k is about to be loaded: no other core may still be running what was there. Each
   one that is gets the wake-up interrupt and leaves user mode (it waits for the lock, and
   drops what it was doing, since it runs nothing now). */
static void evict(uint64_t k) {
    uint64_t c = this_core();
    for (uint64_t o = 0; o < NCORES; o++)
        if (o != c && core_task[o] == k) {
            core_task[o] = NONE;
            DSB(ish);
            send_wake(o);
            while (core_in_user[o]) {}
            DSB(ish);
        }
}

static void report(const char *what);

static void do_syscall(uint64_t cur) {
    struct frame *f = &saved[cur];
    syscalls++;
    lean_object *(*w)(uint64_t) = carries_words(f->x[8]) ? msg_word : arg;
    lean_object *r = leanos_syscall(K, arg(f->x[8]), arg(f->x[0]), w(f->x[1]), w(f->x[2]),
                                    w(f->x[3]), arg(f->x[4]));
    uint64_t out_va = nat(leanos_reply_out_va((lean_inc(r), r)));
    uint64_t out_len = nat(leanos_reply_out_len((lean_inc(r), r)));
    int remap = leanos_reply_remap((lean_inc(r), r));
    uint64_t unmask = nat(leanos_reply_unmask((lean_inc(r), r)));
    uint64_t load = nat(leanos_reply_load((lean_inc(r), r)));
    uint64_t load_len = nat(leanos_reply_load_len((lean_inc(r), r)));
    uint64_t power = nat(leanos_reply_power((lean_inc(r), r)));
    uint64_t io = nat(leanos_reply_io((lean_inc(r), r)));
    uint64_t io_block = nat(leanos_reply_io_block((lean_inc(r), r)));
    uint64_t board = nat(leanos_reply_board((lean_inc(r), r)));
    uint64_t usb_op = nat(leanos_reply_usb_op((lean_inc(r), r)));
    uint64_t usb_a = nat(leanos_reply_usb_a((lean_inc(r), r)));
    uint64_t usb_b = nat(leanos_reply_usb_b((lean_inc(r), r)));
    uint64_t usb_c = nat(leanos_reply_usb_c((lean_inc(r), r)));
    uint64_t usb_d = nat(leanos_reply_usb_d((lean_inc(r), r)));
    K = leanos_reply_state(r);
    if (unmask) gic_enable((uint32_t)(unmask - 1));

    /* Still in `cur`'s address space, so the range the kernel checked is readable here. */
    for (uint64_t k = 0; k < out_len; k++) {
        char c = ((volatile const char *)out_va)[k];
        if (c == '\n') kputc('\r');
        kputc(c);
    }
    /* Block I/O, still in `cur`'s address space: the kernel checked the 512 bytes at out_va
       are in a page `cur` has mapped writable (read) or readable (write). */
    if (io) {
        int ok = io == 1 ? sd_part_read(io_block, (void *)out_va) : sd_part_write(io_block, (const void *)out_va);
        if (!ok) K = leanos_io_failed(K);
    }
    /* Settings asked (only it can: `only_settings_touches_board`), for one of the listed
       requests (`board_requests_listed`). */
    if (board) {
        uint64_t v[5];
        if (board_request(board, v))
            K = leanos_board_done(K, lean_box(v[0]), lean_box(v[1]), lean_box(v[2]), lean_box(v[3]), lean_box(v[4]));
        else K = leanos_io_failed(K);
    }
    /* The USB driver asked (only it can: `only_usb_driver_drives_usb`). */
    if (usb_op) usb_request(usb_op, usb_a, usb_b, usb_c, usb_d);
    /* The display server asked (only it can: `only_display_powers`). Every file is already
       on the card: the file server writes each change through before it answers. */
    if (power == 1) {
        kputs("leanos: switching off, as the display server asked\n");
        report("leanos: switched off");
        poweroff();
    } else if (power == 2) {
        kputs("leanos: restarting, as the display server asked\n");
        restart();
    }
    if (load) {
        /* `start`: the Lean kernel has already taken back every capability and mapping that
           reached the slot's frames. Rebuild every task's tables from that state before the
           frames are cleared and loaded, then measure what was loaded. Every task, not only
           those that lost a mapping: the kernel does not say which did, and with one pass
           over each task's mappings all 18 take a few milliseconds under QEMU. */
        uint64_t k = load - 1;
        if (k >= ntasks || k == cur) kpanic("start of a slot the kernel should have refused");
        evict(k);
        for (uint64_t i = 0; i < ntasks; i++) build_user_pages(i);
        if (load_len) load_image(k, out_va, load_len);
        else if (k < NPROGS && !leanos_open_slot(lean_box(k))) load_program(k);
        else kpanic("start of an open slot without a program");
        kputs("leanos: ");
        kputs(names[k]);
        kputs(" started\n");
        measure_and_verify(k);
        build_user_pages(k);
        /* The heap once a start is done: the same programs in the same slots must give the
           same number, however often a slot was restarted (test/chaos.sh). */
        kputs("leanos: kernel heap ");
        kputdec(rt_heap_live());
        kputs(" bytes live, ");
        kputdec(rt_heap_peak());
        kputs(" peak, after starting ");
        kputs(names[k]);
        kputs("\n");
    } else if (remap) build_user_pages(cur);
}

/* Load the result registers the Lean kernel left for task j (the outcome of its last
   system call, or a message it was waiting for), then tell the kernel they are loaded. */
static void load_result(uint64_t j) {
    uint64_t n = nat(leanos_result_len(K1, lean_box(j)));
    if (n == 0) return;
    if (n > 31) kpanic("too many result registers");
    for (uint64_t k = 0; k < n; k++) saved[j].x[k] = nat(leanos_result(K1, lean_box(j), lean_box(k)));
    K = leanos_clear_result(K, lean_box(j));
}

/* ---- the kernel stack ----
 * 64 KiB per core (arch/kernel.ld). The Lean kernel's walks over a task's mappings and
 * capabilities run as loops (the `@[csimp]` theorems in LeanOS/Kernel.lean), so how deep the
 * stack goes no longer depends on how many a task holds. What recursion is left walks short
 * lists: the 18 tasks, a task's reply slots (at most 8), the pending interrupt lines (at most
 * one of each). tools/stackcheck.py computes the worst case from the code (clang's frame
 * sizes, the calls in the linked image, and a bound for each of those recursions): 6,976
 * bytes, with a kernel exception on top of the deepest system call, and `make test` fails if
 * it passes half the stack. The deepest measured is 2,160 bytes, at boot (the boot console);
 * a task holding all 8192 mappings needs no more (test/stack.sh). The computation trusts
 * clang, the call graph it reads and the recursion bounds it is given (TRUST.md), so the
 * stack is still checked as well: it is painted at boot, and every return to user mode
 * checks that the bottom of the paint is intact. Running past it stops the machine rather than letting the stack grow into the
 * kernel's other data. */
extern char __stack_bottom[], __stack_top[], __core_stacks[], __core_stacks_end[];
#define STACK_SIZE 0x10000UL
static char *stack_bottom(uint64_t c) { return c == 0 ? __stack_bottom : __core_stacks + (c - 1) * STACK_SIZE; }
#define STACK_PAINT 0x5a5a5a5a5a5a5a5aUL
#define STACK_GUARD 512   /* bytes at the bottom that must stay painted */

static void stack_paint(void) {
    uint64_t sp;
    __asm__ volatile("mov %0, sp" : "=r"(sp));
    for (uint64_t *p = (uint64_t *)__stack_bottom; (uint64_t)p < sp - 256; p++) *p = STACK_PAINT;
}

static void stack_check(uint64_t c) {
    char *b = stack_bottom(c);
    for (uint64_t *p = (uint64_t *)b; (char *)p < b + STACK_GUARD; p++)
        if (*p != STACK_PAINT) kpanic("kernel stack overflow");
}

static uint64_t stack_peak(void) {
    uint64_t peak = 0;
    for (uint64_t c = 0; c < cores_up; c++) {
        char *b = stack_bottom(c);
        uint64_t *p = (uint64_t *)b;
        while ((char *)p < b + STACK_SIZE && *p == STACK_PAINT) p++;
        if ((uint64_t)(b + STACK_SIZE - (char *)p) > peak) peak = (uint64_t)(b + STACK_SIZE - (char *)p);
    }
    return peak;
}

static void report(const char *what) {
    kputs(what);
    kputs(" (");
    kputdec(syscalls);
    kputs(" system calls, ");
    kputdec(ticks);
    kputs(" timer ticks, ");
    kputdec(device_irqs);
    kputs(" device interrupts, kernel heap ");
    kputdec(rt_heap_live());
    kputs(" bytes live, ");
    kputdec(rt_heap_peak());
    kputs(" peak, stack ");
    kputdec(stack_peak());
    kputs(" bytes peak; tasks ran on ");
    uint64_t used = 0;
    for (uint64_t c = 0; c < NCORES; c++) used += core_runs[c] != 0;
    kputdec(used);
    kputs(used == 1 ? " core)\n" : " cores)\n");
}

/* The task core `c` runs next: the one the kernel chose, if this core may run it, or the
   next one it may. If there is none, the core waits for an interrupt (its timer, the wake-up
   interrupt, or, on core 0, a device), without the lock. If every task has stopped, power
   off. WFI wakes on a pending interrupt even though the kernel runs with them masked. */
static uint64_t pick(uint64_t c) {
    static int reported;
    for (;;) {
        uint64_t next = cur_task();
        if (!leanos_runnable(K1, lean_box(next))) {
            K = leanos_schedule(K);
            next = cur_task();
        }
        if (leanos_runnable(K1, lean_box(next))) return next;
        core_task[c] = NONE;
        uint64_t waiting = 0, idle = 0;
        for (uint64_t i = 0; i < ntasks; i++)
            if (started[i] && !leanos_dead(K1, lean_box(i))) waiting++;
        if (waiting == 0) {
            report("leanos: every task has finished");
            poweroff();
        }
        for (uint64_t o = 0; o < cores_up; o++) idle += core_task[o] == NONE;
        if (!reported && idle == cores_up) {
            reported = 1;
            kputs("leanos: idle, ");
            kputdec(waiting);
            report(waiting == 1 ? " task waiting" : " tasks waiting");
        }
        unlock();
        __asm__ volatile("wfi");
        lock();
        enter_lean(c);
        handle_irq(c);
    }
}

/* On the way out: an idle core gets the wake-up interrupt if a task is ready that no core
   runs, and a core whose task was stopped from here gets it so that it stops now. */
static void wake_others(uint64_t c) {
    int spare = 0;
    for (uint64_t j = 0; j < ntasks && !spare; j++) {
        if (!ready(j)) continue;
        spare = 1;
        for (uint64_t o = 0; o < cores_up; o++) spare &= core_task[o] != j;
    }
    for (uint64_t o = 0; o < cores_up; o++) {
        if (o == c) continue;
        uint64_t t = core_task[o];
        if (t == NONE ? spare : core_in_user[o] && !ready(t)) {
            send_wake(o);
            if (t == NONE) spare = 0;
        }
    }
}

/* Leave the kernel on core `c`, running task `next` (its registers go into `f`). */
static void leave(uint64_t c, uint64_t next, struct frame *f) {
    core_task[c] = next;
    core_runs[c]++;
    load_result(next);
    switch_to(next);
    *f = saved[next];
    stack_check(c);
    wake_others(c);
    core_in_user[c] = 1;
    unlock();
}

static const char *fault_name(uint64_t ec) {
    switch (ec) {
    case 0x07: return "floating point use";
    case 0x20: return "instruction fetch not allowed";
    case 0x24: return "data access not allowed";
    case 0x22: return "misaligned program counter";
    case 0x26: return "misaligned stack pointer";
    case 0x0e: return "illegal execution state";
    case 0x00: return "undefined instruction";
    default: return "exception";
    }
}

void trap(struct frame *f, uint64_t kind) {
    uint64_t c = this_core();
    DSB(ish);                   /* what the task wrote is visible before it counts as out */
    core_in_user[c] = 0;
    DSB(ish);
    if (kind >= 2) {
        kputs("\nleanos: exception in the kernel, kind ");
        kputdec(kind);
        kputs(" esr ");
        kputhex(SYSREG_READ(esr_el1));
        kputs(" elr ");
        kputhex(SYSREG_READ(elr_el1));
        kputs(" far ");
        kputhex(SYSREG_READ(far_el1));
        kpanic(boot_exception(kind, SYSREG_READ(esr_el1), SYSREG_READ(elr_el1), SYSREG_READ(far_el1)));
    }
    lock();
    uint64_t cur = core_task[c];
    enter_lean(c);
    /* A task stopped (or its slot restarted) from another core while this one ran it: what
       it was doing is dropped. */
    int running = cur < ntasks && ready(cur);
    if (running) saved[cur] = *f;

    if (kind == 0 && running) {
        uint64_t esr = SYSREG_READ(esr_el1), ec = esr >> 26;
        if (ec == 0x15) {
            do_syscall(cur);
        } else {
            kputs("leanos: ");
            kputs(cur < ntasks ? names[cur] : "task");
            kputs(" stopped: ");
            kputs(fault_name(ec));
            kputs(" at ");
            kputhex(ec == 0x20 || ec == 0x24 ? SYSREG_READ(far_el1) : f->elr);
            kputs("\n");
            K = leanos_fault(K);
        }
    } else if (kind == 1) {
        handle_irq(c);
    }
    leave(c, pick(c), f);
}

/* The first task each core runs; enter_user copies it onto the core's stack. */
static struct frame first_frame[NCORES];

/* Cores 1-3 start here (boot.S: secondary), once core 0 has the kernel up, with their MMUs
   and caches already on. */
void secondary_main(uint64_t c) {
    SYSREG_WRITE(cntkctl_el1, 1UL << 1);
    lock();
    gic_this_core();
    timer_rearm();
    cores_up++;
    kputs("leanos: core ");
    kputdec(c);
    kputs(" up\n");
    core_task[c] = NONE;
    enter_lean(c);
    leave(c, pick(c), &first_frame[c]);
    enter_user(&first_frame[c], core_stack_top[c]);
}

/* Hand cores 1-3 `secondary` through the boot stub's spin table: on a Pi 4 the firmware's
   armstub (raspberrypi/tools, armstubs/armstub8.S) parks them at EL2, each waiting (WFE)
   for a nonzero entry address at 0xd8 + 8 x core (0xe0, 0xe8, 0xf0), which it reads with
   its MMU and caches off; QEMU's own boot stub does the same. So the entries, and what the
   cores read before their MMUs are on (`mmu_regs`), are cleaned out to memory (to the
   point of coherency) before the SEV that wakes them. */
static void clean_range(const void *p, uint64_t len) {
    for (uint64_t a = (uint64_t)p & ~63UL; a < (uint64_t)p + len; a += 64)
        __asm__ volatile("dc civac, %0" :: "r"(a) : "memory");
    DSB(sy);
}

static void start_cores(void) {
    extern char secondary[];
    for (uint64_t c = 1; c < NCORES; c++) {
        core_task[c] = NONE;
        core_stack_top[c] = (uint64_t)stack_bottom(c) + STACK_SIZE;
        for (uint64_t *p = (uint64_t *)stack_bottom(c); (uint64_t)p < core_stack_top[c]; p++) *p = STACK_PAINT;
    }
    clean_range(mmu_regs, sizeof mmu_regs);
    clean_range(core_stack_top, sizeof core_stack_top);
    clean_range(__core_stacks, (NCORES - 1) * STACK_SIZE);
    for (uint64_t c = 1; c < NCORES; c++) {
        volatile uint64_t *slot = (volatile uint64_t *)(0xd8 + 8 * c);
        *slot = (uint64_t)secondary;
        clean_range((const void *)slot, 8);
    }
    __asm__ volatile("sev");
}

void kmain(void) {
    boot_led_on();                      /* the first sign of life: the green LED (Pi only) */
    stack_paint();
    boot_led_code(STAGE_UART);
    uart_init();
    kputs("leanos \xc2\xa9 2026 Keith Adler\n");
    boot_stage(STAGE_UART);
    if ((uint64_t)(__stack_top - __stack_bottom) != STACK_SIZE ||
        (uint64_t)(__core_stacks_end - __core_stacks) != (NCORES - 1) * STACK_SIZE)
        kpanic("the kernel stacks in arch/kernel.ld are not STACK_SIZE each");
    kputs("leanos: Raspberry Pi 4, booting on ");
    uint64_t el = SYSREG_READ(CurrentEL) >> 2;
    kputs(el == 1 ? "EL1" : "EL?");
    kputs("\n");
    boot_stage(STAGE_BOARD);
    board_check();
    boot_board_info();
    /* User mode may read the virtual counter (and its frequency) to keep time: animations
       need it, and a task could already time itself by counting loops. */
    SYSREG_WRITE(cntkctl_el1, 1UL << 1);

    /* The Lean kernel comes up first: it says what screen to ask for, and computes the
       tables the MMU is turned on with. */
    boot_stage(STAGE_LEAN);
    lean_object *res = initialize_leanos_LeanOS_Kernel(1);
    if (!lean_io_result_is_ok(res)) kpanic("Lean module initialization failed");
    lean_dec(res);

    boot_stage(STAGE_FB);
    uint64_t fb = fb_alloc();
    panic_fb = (uint32_t *)fb;
    if (fb) {
        bootcon_start((uint32_t *)fb, panic_w, panic_h, panic_stride);
        kputs("leanos: framebuffer ");
        kputdec(nat(leanos_fb_width(lean_box(0))));
        kputs("x");
        kputdec(nat(leanos_fb_height(lean_box(0))));
        kputs(" at ");
        kputhex(fb);
        kputs("\n");
    } else kputs("leanos: no framebuffer\n");

    boot_stage(STAGE_MMU);
    mmu_init();
    kputs("leanos: MMU on\n");
    boot_stage(STAGE_SD);
    if (!sd_init()) kputs("leanos: no SD card\n");
    else {
        uint64_t blocks = sd_partition();
        if (blocks) {
            kputs("leanos: SD card ready, data partition of ");
            kputdec(blocks / 2048);
            kputs(" MiB\n");
        } else kputs("leanos: SD card has no data partition (type 0xDA); files stay in memory\n");
    }

    boot_stage(STAGE_STATE);
    K = leanos_init(lean_box(fb));
    ntasks = nat(leanos_ntasks(K1));
    if (ntasks > MAX_TASKS || ntasks > sizeof names / sizeof names[0]) kpanic("the manifest has more tasks than the machine layer supports");
    kputs("leanos: Lean kernel initialized, ");
    kputdec(ntasks);
    kputs(" tasks\n");

    boot_stage(STAGE_MEMORY);
    memset((void *)FRAME_BASE, 0, NFRAMES * PAGE_SIZE);
    sha256_self_test();
    boot_stage(STAGE_PROGRAMS);
    /* The programs that start at boot. The apps wait in their slots until started. */
    for (uint64_t i = 0; i < ntasks; i++)
        if (leanos_autostart(lean_box(i))) {
            load_program(i);
            measure_and_verify(i);
        }
    boot_stage(STAGE_TABLES);
    for (uint64_t i = 0; i < ntasks; i++) {
        tables_init(i);
        build_user_pages(i);
    }
    boot_stage(STAGE_IRQ);
    irq_init();

    lock();
    core_task[0] = NONE;
    core_stack_top[0] = (uint64_t)__stack_top;
    boot_stage(STAGE_CORES);
    start_cores();
    boot_stage(STAGE_FIRST);
    enter_lean(0);
    bootcon_end();                      /* from here the display server owns the screen */
    leave(0, pick(0), &first_frame[0]);
    enter_user(&first_frame[0], (uint64_t)__stack_top);
}
