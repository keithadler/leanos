/* The input driver. It holds the UART's registers (capability 5) and its receive interrupt
   (capability 6), and may send to the display server with badge 3. It sleeps until the
   interrupt fires, drains the receive FIFO, turns the bytes into events, sends each to the
   display, and acknowledges the interrupt.

   What arrives on the serial line: ordinary bytes are keys. A mouse report is ESC 'm',
   then 'd' (the left button down), 'u' (up), 'D' (the right button down), 'U' (up) or 'v'
   (moved), then x and y as three decimal digits each: "\x1bmd320240". The arrow keys come as a terminal sends them, ESC [ A (up), B
   (down), C (right), D (left), and become keys 128 to 131. So do the keys above them (their
   codes are in user/app.h), in each way terminals send them: Home as ESC [ H, ESC O H,
   ESC [ 1 ~ or ESC [ 7 ~; End as ESC [ F, ESC O F, ESC [ 4 ~ or ESC [ 8 ~; Delete (forward)
   as ESC [ 3 ~; Page Up and Page Down as ESC [ 5 ~ and ESC [ 6 ~ (ESC O A..D are the arrows
   too). The function keys: F1 to F4 as ESC O P..S (or ESC [ 11 ~ to ESC [ 14 ~), F5 as
   ESC [ 15 ~, F6 to F10 as ESC [ 17 ~ to ESC [ 21 ~, F11 and F12 as ESC [ 23 ~ and ESC [ 24 ~.
   A key held with a modifier comes with it after a ';': ESC [ 1 ; 2 A is Shift+Up,
   ESC [ 5 ; 2 ~ Shift+Page Up, ESC [ 1 ; 2 P Shift+F1. With Shift (2), the arrows, Home, End,
   Page Up and Page Down become their Shift keys (137 to 144), and any other key is itself;
   with any other modifier (Control, Alt: 3 and up) the key is dropped, as leanos has no such
   keys. Any other sequence, ESC [ then digits, ';' and the like up to its last byte (@ to
   ~), is a key leanos does not have, and all of it is dropped, as is the byte after an ESC
   that starts none of these. On QEMU the browser console writes these; on a real Pi, any
   serial terminal can. */
#include "lib.h"

#define UART_REGS 5
#define UART_IRQ 6
#define UART_PAGE 3000

enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4, EV_RDOWN = 9, EV_RUP = 10 };   /* user/app.h */
enum { KEY_UP = 128, KEY_HOME = 132, KEY_END = 133, KEY_DELETE = 134, KEY_PGUP = 135, KEY_PGDN = 136,
       KEY_F1 = 145 };                                                                 /* user/app.h */

/* Key k held with Shift (user/app.h): the arrows, Home and End are 9 on, Page Up and Page
   Down 8 (Delete, between them, has no Shift key); any other key is itself. */
static u64 shifted(u64 k) { return k >= KEY_UP && k <= KEY_END ? k + 9 : k == KEY_PGUP || k == KEY_PGDN ? k + 8 : k; }

/* The key ESC [ num ~ is (0: none). */
static u64 tilde_key(u64 num) {
    if (num == 1 || num == 7) return KEY_HOME;
    if (num == 4 || num == 8) return KEY_END;
    if (num == 3) return KEY_DELETE;
    if (num == 5 || num == 6) return KEY_PGUP + (num - 5);
    if (num >= 11 && num <= 15) return KEY_F1 + (num - 11);        /* F1..F5 */
    if (num >= 17 && num <= 21) return KEY_F1 + 5 + (num - 17);    /* F6..F10 */
    if (num == 23 || num == 24) return KEY_F1 + 10 + (num - 23);   /* F11, F12 */
    return 0;
}

static volatile unsigned *uart;
#define DR (uart[0x00 / 4])
#define FR (uart[0x18 / 4])
#define IMSC (uart[0x38 / 4])
#define ICR (uart[0x44 / 4])

static void event(u64 type, u64 a, u64 b) { sys(SYS_SEND, ENDPOINT, type, a, b, 0); }

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    if (sys2(SYS_MAP, UART_REGS, UART_PAGE).status != OK) {
        put_s(&l, "input: cannot map the UART\n");
        flush(&l);
        exit_task();
    }
    uart = (volatile unsigned *)PAGE(UART_PAGE);
    IMSC = (1 << 4) | (1 << 6); /* receive and receive-timeout interrupts */
    put_s(&l, "input: listening on the UART\n");
    flush(&l);

    /* 0 plain, 1 after ESC, 2 after ESC m, 3.. its digits; 10 after ESC [, 11 after ESC O,
       12 after ESC [ and digits (num), 13 in a sequence no key has, until its last byte,
       14 after ESC [ digits ; and the modifier's digits (mod) */
    int state = 0;
    u64 kind = 0, x = 0, y = 0, num = 0, mod = 0;
    /* Each round: clear the UART's interrupt status, take every byte already waiting
       (bytes can be waiting before the first round: the tail of a mouse report sent while
       the machine restarted, say, whose interrupt nobody will see again), then let the
       line fire again and wait. A byte that arrives after the drain raises a fresh
       interrupt, which the kernel keeps pending until the wait. */
    for (;;) {
        ICR = 0x7ff;
        while (!(FR & (1 << 4))) {        /* receive FIFO not empty */
            unsigned char c = (unsigned char)DR;
            if (state == 0) {
                if (c == 27) state = 1;
                else event(EV_KEY, c, 0);
            } else if (state == 1) {
                state = c == 'm' ? 2 : c == '[' ? 10 : c == 'O' ? 11 : 0;
                num = mod = 0;
            } else if (state >= 10) {        /* a key's sequence, after ESC [ or ESC O */
                u64 key = 0;
                int next = 0;
                if (c == 27) next = 1;                              /* cut short by another */
                else if (c >= '0' && c <= '9' && state != 11 && state != 13) {
                    u64 *v = state == 14 ? &mod : &num;
                    *v = *v * 10 + (c - '0');
                    if (*v > 99) *v = 99;
                    next = state == 14 ? 14 : 12;
                } else if (c == ';' && state == 12) next = 14;     /* the modifier comes */
                else if (c >= 0x20 && c < 0x40) next = 13;          /* ';' and the like */
                else if (c >= 0x40 && c <= 0x7e && state != 13) {   /* its last byte */
                    if (state == 10 || state == 11 || num == 1) {   /* ESC [ A, ESC O A, ESC [ 1 ; 2 A */
                        key = c >= 'A' && c <= 'D' ? KEY_UP + (u64)(c - 'A') : c == 'H' ? KEY_HOME : c == 'F' ? KEY_END : 0;
                        if (c >= 'P' && c <= 'S' && state != 10) key = KEY_F1 + (u64)(c - 'P');
                    }
                    if (c == '~' && state != 10 && state != 11) key = tilde_key(num);
                    if (mod == 2) key = shifted(key);                /* Shift */
                    else if (mod > 1) key = 0;                       /* Control, Alt: no such keys */
                }                                                   /* a control byte ends it */
                if (key) event(EV_KEY, key, 0);
                state = next;
            } else if (state == 2) {
                kind = c == 'd' ? EV_DOWN : c == 'u' ? EV_UP : c == 'D' ? EV_RDOWN : c == 'U' ? EV_RUP : EV_MOVE;
                x = y = 0;
                state = 3;
            } else {
                if (c < '0' || c > '9') { state = 0; continue; }
                if (state < 6) x = x * 10 + (c - '0');
                else y = y * 10 + (c - '0');
                if (++state == 9) {
                    event(kind, x, y);
                    state = 0;
                }
            }
        }
        sys1(SYS_IRQACK, UART_IRQ);
        sys1(SYS_IRQWAIT, UART_IRQ);
    }
}
