/* The network service's protocol, both sides. The USB driver serves it on endpoint 2
   (it owns the network adapter); Terminal calls it, as capability 12, granting its 4-page
   buffer with every request, as with the file server: a host name or URL at byte 0, data
   from byte 256. The reply: x1 = status, x2 and x3 as each request says. */
#pragma once
#include "lib.h"

enum {
    NET_INFO = 1,     /* the data area gets a struct net_info */
    NET_PING = 2,     /* ping the host at byte 0 once: x2 = milliseconds */
    NET_GET = 3,      /* fetch the http:// URL at byte 0: x2 = the body's size, x3 = the HTTP status */
    NET_READ = 4,     /* the body of the last GET, from offset `arg`, into the data area: x2 = bytes */
    NET_TIME = 5,     /* ask the time server at byte 0 (host[:port]) and set the kernel's time of
                         day from it: x2 = Unix seconds */
};
enum { NET_OK = 0, NET_NO_DEVICE = 1, NET_NO_ADDRESS = 2, NET_NO_HOST = 3, NET_NO_ANSWER = 4,
       NET_UNSUPPORTED = 5, NET_BAD = 6, NET_NO_SERVICE = 7 };

struct net_info {
    unsigned ip, mask, gateway, dns;
    unsigned char mac[6];
    unsigned char device, up;
};

#define NET_BUF_PAGES 4
#define NET_DATA_OFF 256
#define NET_CHUNK (NET_BUF_PAGES * 4096 - NET_DATA_OFF)
#define NET_BODY_MAX (512 * 1024)

#ifndef NET_SERVER
#define NET_ENDPOINT 12     /* Terminal's capability to endpoint 2 */

struct net_client { u64 cap; char *buf; };

/* The buffer: the same 4 pages of the spare run the file server's client uses (never both at
   once: each request is over before the next). */
static inline void net_init(struct net_client *c, u64 spare_page) {
    c->cap = 0;
    c->buf = (char *)PAGE(spare_page + 224);
}

static inline struct res net_call(struct net_client *c, u64 op, u64 arg, const char *text) {
    if (!c->cap) {
        struct res d = sys(SYS_DERIVE, 3, R | W, 224, NET_BUF_PAGES, 0);
        if (d.status != OK) { d.x[1] = NET_NO_SERVICE; return d; }
        c->cap = d.x[1] + 1;
    }
    int i = 0;
    for (; text && text[i] && i < 240; i++) c->buf[i] = text[i];
    c->buf[i] = 0;
    struct res r = sys(SYS_CALL, NET_ENDPOINT, op, arg, 0, c->cap);
    if (r.status != OK) r.x[1] = NET_NO_SERVICE;
    return r;
}

static inline const char *net_data(struct net_client *c) { return c->buf + NET_DATA_OFF; }
#endif
