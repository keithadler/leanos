/* The input driver. It holds the UART's registers (capability 5) and its receive interrupt
   (capability 6), and may send to the display server with badge 3. It sleeps until the
   interrupt fires, drains the receive FIFO, turns the bytes into events, sends each to the
   display, and acknowledges the interrupt.

   What arrives on the serial line: ordinary bytes are keys. A mouse report is ESC 'm',
   then 'd' (button down), 'u' (up) or 'v' (moved), then x and y as three decimal digits
   each: "\x1bmd320240". The arrow keys come as a terminal sends them, ESC [ A (up), B
   (down), C (right), D (left), and become keys 128 to 131. So do the keys above them (their
   codes are in user/app.h), in each way terminals send them: Home as ESC [ H, ESC O H,
   ESC [ 1 ~ or ESC [ 7 ~; End as ESC [ F, ESC O F, ESC [ 4 ~ or ESC [ 8 ~; Delete (forward)
   as ESC [ 3 ~; Page Up and Page Down as ESC [ 5 ~ and ESC [ 6 ~ (ESC O A..D are the arrows
   too). Any other sequence, ESC [ then digits, ';' and the like up to its last byte (@ to
   ~), is a key leanos does not have, and all of it is dropped, as is the byte after an ESC
   that starts none of these. On QEMU the browser console writes these; on a real Pi, any
   serial terminal can. */
#include "lib.h"

#define UART_REGS 5
#define UART_IRQ 6
#define UART_PAGE 3000

enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4 };
enum { KEY_UP = 128, KEY_HOME = 132, KEY_END = 133, KEY_DELETE = 134, KEY_PGUP = 135, KEY_PGDN = 136 };  /* user/app.h */

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
       12 after ESC [ and digits (num), 13 in a sequence no key has, until its last byte */
    int state = 0;
    u64 kind = 0, x = 0, y = 0, num = 0;
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
            } else if (state >= 10) {        /* a key's sequence, after ESC [ or ESC O */
                u64 key = 0;
                int next = 0;
                if (c == 27) next = 1;                              /* cut short by another */
                else if (c >= '0' && c <= '9' && (state == 10 || state == 12)) {
                    num = (state == 12 ? num : 0) * 10 + (c - '0');
                    if (num > 99) num = 99;
                    next = 12;
                } else if (c >= 0x20 && c < 0x40) next = 13;       /* ';' and the like */
                else if (c >= 0x40 && c <= 0x7e) {                 /* its last byte */
                    if (state == 10 || state == 11)
                        key = c >= 'A' && c <= 'D' ? KEY_UP + (u64)(c - 'A') : c == 'H' ? KEY_HOME : c == 'F' ? KEY_END : 0;
                    else if (state == 12 && c == '~')
                        key = num == 1 || num == 7 ? KEY_HOME : num == 4 || num == 8 ? KEY_END : num == 3 ? KEY_DELETE
                            : num == 5 ? KEY_PGUP : num == 6 ? KEY_PGDN : 0;
                }                                                   /* a control byte ends it */
                if (key) event(EV_KEY, key, 0);
                state = next;
            } else if (state == 2) {
                kind = c == 'd' ? EV_DOWN : c == 'u' ? EV_UP : EV_MOVE;
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
