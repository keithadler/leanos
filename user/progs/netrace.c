/* netrace: a test program (test/netsafe.sh), not on the card anyone gets. It is a program
   from the card that was allowed the network (`run -net netrace`) and turns on the network
   service: it sends requests as plain sends, which nobody waits for, so it keeps running
   while the service works on them, and it keeps changing the buffer it lent for the request.

   The service ended a request's text with a 0 at byte 239, once, and then read the text
   where it lay, in the sender's memory. Here the whole buffer is digits (a host name that
   never ends), and byte 239 is put back to a digit over and over: the service's scan for the
   end of the name ran off the buffer's four pages, and the USB driver stopped, and with it
   the keyboard, the mouse and the network. Now a plain send is not a request, and a
   request's text is copied out of the caller's memory before anything reads it.

   It ends by asking the service a question with a call. An answer means the service is
   still there. */
#include "../lib.h"
#include "../net.h"

#define SPARE 3
#define SPARE_PAGE 64
#define ROUNDS 200

__attribute__((section(".text.start"))) void _start(void) {
    struct line l = {.n = 0};
    struct net_client c;
    sys2(SYS_MAP, SPARE, SPARE_PAGE);
    net_init_open(&c, SPARE_PAGE);

    /* Terminal allows the program just after it starts it: ask until the service says yes. */
    u64 code = NET_DENIED;
    for (int i = 0; i < 300 && code == NET_DENIED; i++) {
        code = net_call(&c, NET_INFO, 0, 0).x[1];
        if (code == NET_DENIED) sleep_ms(10);
    }
    put_s(&l, "netrace: the network service answers a call with ");
    put_dec(&l, code);
    put_s(&l, "\n");
    flush(&l);
    if (code != NET_OK) exit_task();

    volatile char *b = (volatile char *)c.buf;
    u64 sent = 0;
    for (int round = 0; round < ROUNDS; round++) {
        for (u64 i = 0; i < NET_BUF_PAGES * 4096; i++) b[i] = '1';
        /* a ping, a time and a page by turns: each reads a name from the buffer */
        u64 op = round % 3 == 0 ? NET_PING : round % 3 == 1 ? NET_GET : NET_TIME;
        if (sys(SYS_SEND, c.ep, op, 0, 0, c.cap).status == OK) sent++;
        u64 until = millis() + 20;
        while (millis() < until) b[239] = '1';
    }
    put_s(&l, "netrace: ");
    put_dec(&l, sent);
    put_s(&l, " plain sends, the buffer changed under each\n");
    flush(&l);

    code = net_call(&c, NET_INFO, 0, 0).x[1];
    put_s(&l, "netrace: after them the network service answers a call with ");
    put_dec(&l, code);
    put_s(&l, "\n");
    flush(&l);
    exit_task();
}
