/* The input driver. It holds the UART's registers (capability 5) and its receive interrupt
   (capability 6), and may send to the display server with badge 3. It sleeps until the
   interrupt fires, drains the receive FIFO, turns the bytes into events, sends each to the
   display, and acknowledges the interrupt.

   What arrives on the serial line: ordinary bytes are keys. A mouse report is ESC 'm',
   then 'd' (button down), 'u' (up) or 'v' (moved), then x and y as three decimal digits
   each: "\x1bmd320240". On QEMU the browser console writes these; on a real Pi, any
   serial terminal can. */
#include "lib.h"

#define UART_REGS 5
#define UART_IRQ 6
#define UART_PAGE 3000

enum { EV_KEY = 1, EV_DOWN = 2, EV_UP = 3, EV_MOVE = 4 };

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
    ICR = 0x7ff;
    IMSC = (1 << 4) | (1 << 6); /* receive and receive-timeout interrupts */
    put_s(&l, "input: listening on the UART\n");
    flush(&l);

    int state = 0;      /* 0 plain, 1 after ESC, 2 after ESC m, 3.. digits */
    u64 kind = 0, x = 0, y = 0;
    for (;;) {
        sys1(SYS_IRQWAIT, UART_IRQ);
        while (!(FR & (1 << 4))) {        /* receive FIFO not empty */
            unsigned char c = (unsigned char)DR;
            if (state == 0) {
                if (c == 27) state = 1;
                else event(EV_KEY, c, 0);
            } else if (state == 1) {
                state = c == 'm' ? 2 : 0;
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
        ICR = 0x7ff;
        sys1(SYS_IRQACK, UART_IRQ);
    }
}
