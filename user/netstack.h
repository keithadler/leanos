/* A small network stack for the USB driver (user/usb.c), which owns the network adapter:
   Ethernet, ARP, IPv4, ICMP (answering pings, and pinging), UDP, a DHCP client, a DNS client,
   a TCP client (one connection at a time), and HTTP/1.0 GET on top of it.

   It is a client stack for a small computer on a friendly network (QEMU's user network,
   a home router): no IP options, no fragments, TCP data taken in order only (anything out
   of order is dropped and sent again by the other side), a fixed window. What it needs from
   usb.c: net_send(frame, length), net_now() in ms, and net_poll(), which receives whatever
   arrived (calling net_input) and keeps the keyboard and mouse going while an operation
   waits. */
#pragma once
#include "lib.h"

struct net {
    unsigned char mac[6];
    unsigned ip, mask, gw, dns, server;          /* host byte order; 0 = not yet */
    int up;                                      /* an address from DHCP */
    unsigned xid;
    int dhcp_state;                              /* 0 idle, 1 offered, 2 bound */
    unsigned offer;
    struct { unsigned ip; unsigned char mac[6]; } arp[8];
    int arp_next;
    /* ping */
    unsigned short ping_id, ping_seq;
    int ping_got;
    /* DNS */
    unsigned short dns_id;
    unsigned dns_answer;
    int dns_done;
    /* TCP */
    int tcp_state;                               /* 0 closed, 1 syn sent, 2 open, 3 closed by peer, 4 reset */
    unsigned tcp_ip;
    unsigned short tcp_lport, tcp_rport;
    unsigned tcp_snd, tcp_rcv;                   /* next sequence numbers to send and expect */
    unsigned tcp_una;                            /* the oldest byte not yet acknowledged */
    unsigned char *rx;                           /* where the data received goes */
    u64 rx_len, rx_max;
    unsigned rand;
    unsigned char frame[1600];                   /* what is being built to send */
    unsigned char aframe[64];                    /* an ARP packet: never over a frame being built */
};

/* From usb.c */
static int net_send(const unsigned char *frame, unsigned len);
static u64 net_now(void);
static void net_poll(void);

static unsigned short be16(const unsigned char *p) { return (unsigned short)(p[0] << 8 | p[1]); }
static unsigned be32(const unsigned char *p) { return (unsigned)p[0] << 24 | (unsigned)p[1] << 16 | (unsigned)p[2] << 8 | p[3]; }
static void put16(unsigned char *p, unsigned v) { p[0] = (unsigned char)(v >> 8); p[1] = (unsigned char)v; }
static void put32(unsigned char *p, unsigned v) { put16(p, v >> 16); put16(p + 2, v & 0xffff); }
static void mcopy(unsigned char *d, const unsigned char *s, u64 n) { for (u64 i = 0; i < n; i++) d[i] = s[i]; }
static void mzero(unsigned char *d, u64 n) { for (u64 i = 0; i < n; i++) d[i] = 0; }

static unsigned csum_add(unsigned sum, const unsigned char *p, unsigned n) {
    for (unsigned i = 0; i + 1 < n; i += 2) sum += (unsigned)(p[i] << 8 | p[i + 1]);
    if (n & 1) sum += (unsigned)(p[n - 1] << 8);
    return sum;
}
static unsigned short csum_end(unsigned sum) {
    while (sum >> 16) sum = (sum & 0xffff) + (sum >> 16);
    return (unsigned short)~sum;
}

static unsigned next_rand(struct net *n) {
    n->rand = n->rand * 1103515245u + 12345u + (unsigned)net_now();
    return n->rand >> 8;
}

/* ---- Ethernet and ARP ---- */

static const unsigned char BCAST[6] = {255, 255, 255, 255, 255, 255};

static int eth_send(struct net *n, unsigned char *f, const unsigned char *dst, unsigned type, unsigned len) {
    mcopy(f, dst, 6);
    mcopy(f + 6, n->mac, 6);
    put16(f + 12, type);
    unsigned total = 14 + len;
    if (total < 60) { mzero(f + total, 60 - total); total = 60; }
    return net_send(f, total);
}

static void arp_learn(struct net *n, unsigned ip, const unsigned char *mac) {
    for (int i = 0; i < 8; i++) if (n->arp[i].ip == ip) { mcopy(n->arp[i].mac, mac, 6); return; }
    n->arp[n->arp_next].ip = ip;
    mcopy(n->arp[n->arp_next].mac, mac, 6);
    n->arp_next = (n->arp_next + 1) % 8;
}

static const unsigned char *arp_find(struct net *n, unsigned ip) {
    for (int i = 0; i < 8; i++) if (n->arp[i].ip == ip && ip) return n->arp[i].mac;
    return 0;
}

static void arp_packet(struct net *n, unsigned op, const unsigned char *tmac, unsigned tip, const unsigned char *dst) {
    unsigned char *a = n->aframe + 14;
    put16(a, 1); put16(a + 2, 0x0800); a[4] = 6; a[5] = 4; put16(a + 6, op);
    mcopy(a + 8, n->mac, 6); put32(a + 14, n->ip);
    mcopy(a + 18, tmac, 6); put32(a + 24, tip);
    eth_send(n, n->aframe, dst, 0x0806, 28);
}

/* The MAC for an IP address on this network: asked for, and waited for (up to a second). */
static const unsigned char *arp_resolve(struct net *n, unsigned ip) {
    const unsigned char *m = arp_find(n, ip);
    if (m) return m;
    for (int tries = 0; tries < 3 && !m; tries++) {
        static const unsigned char zero6[6] = {0, 0, 0, 0, 0, 0};
        arp_packet(n, 1, zero6, ip, BCAST);
        u64 until = net_now() + 400;
        while (!(m = arp_find(n, ip)) && net_now() < until) net_poll();
    }
    return m;
}

/* ---- IPv4 ---- */

static int ip_send(struct net *n, unsigned dst, unsigned proto, unsigned len) {
    unsigned hop = dst == 0xffffffffu || ((dst & n->mask) == (n->ip & n->mask) && n->ip) ? dst : n->gw;
    const unsigned char *mac = dst == 0xffffffffu ? BCAST : arp_resolve(n, hop);
    if (!mac) return 0;
    unsigned char dmac[6];
    mcopy(dmac, mac, 6);
    unsigned char *h = n->frame + 14;
    h[0] = 0x45; h[1] = 0; put16(h + 2, 20 + len); put16(h + 4, next_rand(n) & 0xffff);
    put16(h + 6, 0x4000); h[8] = 64; h[9] = (unsigned char)proto; put16(h + 10, 0);
    put32(h + 12, n->ip); put32(h + 16, dst);
    put16(h + 10, csum_end(csum_add(0, h, 20)));
    return eth_send(n, n->frame, dmac, 0x0800, 20 + len);
}

/* The payload area of an IP packet being built. */
static unsigned char *ip_payload(struct net *n) { return n->frame + 14 + 20; }

/* ---- UDP ---- */

static int udp_send(struct net *n, unsigned dst, unsigned sport, unsigned dport, unsigned len) {
    unsigned char *u = ip_payload(n);
    put16(u, sport); put16(u + 2, dport); put16(u + 4, 8 + len); put16(u + 6, 0);   /* no checksum */
    return ip_send(n, dst, 17, 8 + len);
}

/* ---- DHCP ---- */

static unsigned dhcp_options(struct net *n, unsigned char *o, int type) {
    unsigned k = 0;
    o[k++] = 99; o[k++] = 130; o[k++] = 83; o[k++] = 99;      /* the magic cookie */
    o[k++] = 53; o[k++] = 1; o[k++] = (unsigned char)type;
    if (type == 3) {
        o[k++] = 50; o[k++] = 4; put32(o + k, n->offer); k += 4;
        o[k++] = 54; o[k++] = 4; put32(o + k, n->server); k += 4;
    }
    o[k++] = 55; o[k++] = 3; o[k++] = 1; o[k++] = 3; o[k++] = 6;   /* mask, router, DNS */
    o[k++] = 255;
    return k;
}

static void dhcp_send(struct net *n, int type) {
    unsigned char *b = ip_payload(n) + 8;
    mzero(b, 240);
    b[0] = 1; b[1] = 1; b[2] = 6; put32(b + 4, n->xid); put16(b + 10, 0x8000);
    mcopy(b + 28, n->mac, 6);
    unsigned k = dhcp_options(n, b + 236, type);
    unsigned saved = n->ip;
    n->ip = 0;
    udp_send(n, 0xffffffffu, 68, 67, 236 + k);
    n->ip = saved;
}

static void dhcp_input(struct net *n, const unsigned char *b, unsigned len) {
    if (len < 240 || b[0] != 2 || be32(b + 4) != n->xid) return;
    int type = 0;
    unsigned mask = 0, gw = 0, dns = 0, server = 0;
    for (unsigned i = 240; i + 1 < len && b[i] != 255;) {
        if (b[i] == 0) { i++; continue; }
        unsigned code = b[i], l = b[i + 1];
        const unsigned char *v = b + i + 2;
        if (i + 2 + l > len) break;
        if (code == 53 && l >= 1) type = v[0];
        if (code == 1 && l >= 4) mask = be32(v);
        if (code == 3 && l >= 4) gw = be32(v);
        if (code == 6 && l >= 4) dns = be32(v);
        if (code == 54 && l >= 4) server = be32(v);
        i += 2 + l;
    }
    if (type == 2 && n->dhcp_state == 0) {          /* an offer */
        n->offer = be32(b + 16);
        n->server = server;
        n->dhcp_state = 1;
    } else if (type == 5 && n->dhcp_state == 1) {   /* acknowledged */
        n->ip = be32(b + 16);
        n->mask = mask ? mask : 0xffffff00u;
        n->gw = gw;
        n->dns = dns ? dns : gw;
        n->dhcp_state = 2;
        n->up = 1;
    }
}

/* Ask the network for an address: 1 if one came within a few seconds. */
static int dhcp(struct net *n) {
    for (int tries = 0; tries < 4 && !n->up; tries++) {
        n->xid = next_rand(n) ^ 0x4c65616e;         /* "Lean" */
        n->dhcp_state = 0;
        dhcp_send(n, 1);                            /* discover */
        u64 until = net_now() + 1500;
        while (n->dhcp_state == 0 && net_now() < until) net_poll();
        if (n->dhcp_state != 1) continue;
        dhcp_send(n, 3);                            /* request */
        until = net_now() + 1500;
        while (n->dhcp_state == 1 && net_now() < until) net_poll();
    }
    return n->up;
}

/* ---- DNS ---- */

static void dns_input(struct net *n, const unsigned char *b, unsigned len) {
    if (len < 12 || be16(b) != n->dns_id || !(b[2] & 0x80)) return;
    unsigned qd = be16(b + 4), an = be16(b + 6), i = 12;
    for (unsigned q = 0; q < qd; q++) {             /* skip the questions */
        while (i < len && b[i]) i += (b[i] & 0xc0) == 0xc0 ? 1 : (unsigned)b[i] + 1;
        i += (i < len && (b[i] & 0xc0) == 0xc0) ? 2 : 1;
        i += 4;
    }
    for (unsigned a = 0; a < an && i < len; a++) {
        if ((b[i] & 0xc0) == 0xc0) i += 2;
        else { while (i < len && b[i]) i += (unsigned)b[i] + 1; i++; }
        if (i + 10 > len) break;
        unsigned type = be16(b + i), rdl = be16(b + i + 8);
        if (type == 1 && rdl == 4 && i + 14 <= len) { n->dns_answer = be32(b + i + 10); break; }
        i += 10 + rdl;
    }
    n->dns_done = 1;
}

/* The address for `name`: a dotted quad, or asked of the DNS server. 0 if none. */
static unsigned resolve(struct net *n, const char *name) {
    unsigned parts[4] = {0, 0, 0, 0}, k = 0;
    int dotted = 1;
    for (int i = 0; name[i]; i++) {
        if (name[i] == '.') { if (++k > 3) { dotted = 0; break; } }
        else if (name[i] >= '0' && name[i] <= '9') parts[k] = parts[k] * 10 + (unsigned)(name[i] - '0');
        else { dotted = 0; break; }
    }
    if (dotted && k == 3) return parts[0] << 24 | parts[1] << 16 | parts[2] << 8 | parts[3];
    if (!n->dns) return 0;
    n->dns_id = (unsigned short)next_rand(n);
    for (int tries = 0; tries < 3; tries++) {
        /* built again each time: what arrives while waiting may use the same buffer */
        unsigned char *q = ip_payload(n) + 8;
        put16(q, n->dns_id); put16(q + 2, 0x0100); put16(q + 4, 1); put16(q + 6, 0); put16(q + 8, 0); put16(q + 10, 0);
        unsigned i = 12;
        for (const char *p = name; *p;) {
            unsigned l = 0;
            while (p[l] && p[l] != '.') l++;
            if (!l || l > 63 || i + l + 6 > 500) return 0;
            q[i++] = (unsigned char)l;
            for (unsigned j = 0; j < l; j++) q[i++] = (unsigned char)p[j];
            p += l;
            if (*p == '.') p++;
        }
        q[i++] = 0;
        put16(q + i, 1); put16(q + i + 2, 1); i += 4;
        n->dns_done = 0;
        n->dns_answer = 0;
        udp_send(n, n->dns, 40000 + (next_rand(n) % 20000), 53, i);
        u64 until = net_now() + 1500;
        while (!n->dns_done && net_now() < until) net_poll();
        if (n->dns_done) return n->dns_answer;
    }
    return 0;
}

/* ---- ICMP ---- */

static void icmp_input(struct net *n, unsigned src, const unsigned char *p, unsigned len) {
    if (len < 8) return;
    if (p[0] == 8) {                                /* someone pings us: answer */
        unsigned char *r = ip_payload(n);
        if (len > 1400) return;
        mcopy(r, p, len);
        r[0] = 0;
        put16(r + 2, 0);
        put16(r + 2, csum_end(csum_add(0, r, len)));
        ip_send(n, src, 1, len);
    } else if (p[0] == 0 && be16(p + 4) == n->ping_id && be16(p + 6) == n->ping_seq) {
        n->ping_got = 1;
    }
}

/* Ping `ip` once: the round trip in ms, or -1 if no answer within a second and a half. */
static long ping(struct net *n, unsigned ip) {
    unsigned char *p = ip_payload(n);
    n->ping_id = (unsigned short)next_rand(n);
    n->ping_seq++;
    p[0] = 8; p[1] = 0; put16(p + 2, 0); put16(p + 4, n->ping_id); put16(p + 6, n->ping_seq);
    for (int i = 0; i < 32; i++) p[8 + i] = (unsigned char)('a' + i % 26);
    put16(p + 2, csum_end(csum_add(0, p, 40)));
    n->ping_got = 0;
    u64 t0 = net_now();
    if (!ip_send(n, ip, 1, 40)) return -1;
    u64 until = t0 + 1500;
    while (!n->ping_got && net_now() < until) net_poll();
    return n->ping_got ? (long)(net_now() - t0) : -1;
}

/* ---- TCP ---- */

enum { FIN = 1, SYN = 2, RST = 4, PSH = 8, ACK = 16 };
#define WINDOW 8192

static int tcp_send(struct net *n, unsigned flags, const unsigned char *data, unsigned len) {
    unsigned char *t = ip_payload(n);
    put16(t, n->tcp_lport); put16(t + 2, n->tcp_rport);
    put32(t + 4, n->tcp_snd); put32(t + 8, n->tcp_rcv);
    t[12] = 5 << 4; t[13] = (unsigned char)flags; put16(t + 14, WINDOW); put16(t + 16, 0); put16(t + 18, 0);
    if (len) mcopy(t + 20, data, len);
    unsigned char pseudo[12];
    put32(pseudo, n->ip); put32(pseudo + 4, n->tcp_ip); pseudo[8] = 0; pseudo[9] = 6; put16(pseudo + 10, 20 + len);
    put16(t + 16, csum_end(csum_add(csum_add(0, pseudo, 12), t, 20 + len)));
    return ip_send(n, n->tcp_ip, 6, 20 + len);
}

static void tcp_input(struct net *n, unsigned src, const unsigned char *t, unsigned len) {
    if (len < 20 || n->tcp_state == 0 || src != n->tcp_ip || be16(t) != n->tcp_rport || be16(t + 2) != n->tcp_lport)
        return;
    unsigned seq = be32(t + 4), ack = be32(t + 8), off = (unsigned)(t[12] >> 4) * 4, flags = t[13];
    if (off < 20 || off > len) return;
    if (flags & RST) { n->tcp_state = 4; return; }
    if (n->tcp_state == 1) {
        if ((flags & (SYN | ACK)) == (SYN | ACK) && ack == n->tcp_snd + 1) {
            n->tcp_snd++;
            n->tcp_una = n->tcp_snd;
            n->tcp_rcv = seq + 1;
            n->tcp_state = 2;
            tcp_send(n, ACK, 0, 0);
        }
        return;
    }
    unsigned dlen = len - off;
    if (seq == n->tcp_rcv && dlen) {                /* in order: take it (as much as fits) */
        u64 room = n->rx_max - n->rx_len, take = dlen < room ? dlen : room;
        mcopy(n->rx + n->rx_len, t + off, take);
        n->rx_len += take;
        n->tcp_rcv += dlen;
    }
    if ((flags & FIN) && seq + dlen == n->tcp_rcv) {
        n->tcp_rcv++;
        n->tcp_state = 3;
    }
    if ((flags & ACK) && (int)(ack - n->tcp_una) > 0 && (int)(ack - n->tcp_snd) <= 0) n->tcp_una = ack;
    if (dlen || (flags & FIN)) tcp_send(n, ACK, 0, 0);
}

/* Connect to ip:port, send `req`, and take everything the other side sends until it
   closes, into `out` (up to `max`). The bytes received, or -1. */
static long tcp_exchange(struct net *n, unsigned ip, unsigned port, const unsigned char *req, unsigned rlen,
                         unsigned char *out, u64 max) {
    n->tcp_ip = ip;
    n->tcp_rport = (unsigned short)port;
    n->tcp_lport = (unsigned short)(49152 + next_rand(n) % 16000);
    n->tcp_snd = next_rand(n);
    n->rx = out;
    n->rx_len = 0;
    n->rx_max = max;
    n->tcp_state = 1;
    for (int tries = 0; tries < 4 && n->tcp_state == 1; tries++) {
        tcp_send(n, SYN, 0, 0);
        u64 until = net_now() + 1000;
        while (n->tcp_state == 1 && net_now() < until) net_poll();
    }
    if (n->tcp_state != 2) { n->tcp_state = 0; return -1; }
    /* the request: sent again until it is acknowledged or the answer starts */
    unsigned start = n->tcp_snd;
    for (int tries = 0; tries < 4 && n->tcp_state == 2; tries++) {
        n->tcp_snd = start;
        tcp_send(n, PSH | ACK, req, rlen);
        n->tcp_snd = start + rlen;
        u64 until = net_now() + 1000;
        while (n->tcp_state == 2 && n->tcp_una != start + rlen && !n->rx_len && net_now() < until) net_poll();
        if (n->tcp_una == start + rlen || n->rx_len || n->tcp_state != 2) break;
    }
    u64 idle = net_now(), seen = n->rx_len;
    while (n->tcp_state == 2 && net_now() - idle < 10000) {
        net_poll();
        if (n->rx_len != seen) { seen = n->rx_len; idle = net_now(); }
    }
    if (n->tcp_state == 3) tcp_send(n, FIN | ACK, 0, 0);
    int ok = n->tcp_state == 3 || n->tcp_state == 2;
    n->tcp_state = 0;
    return ok ? (long)n->rx_len : -1;
}

/* ---- what arrives ---- */

static void net_input(struct net *n, const unsigned char *f, unsigned len) {
    if (len < 14) return;
    unsigned type = be16(f + 12);
    if (type == 0x0806 && len >= 42) {              /* ARP */
        const unsigned char *a = f + 14;
        unsigned op = be16(a + 6), sip = be32(a + 14), tip = be32(a + 24);
        if (sip) arp_learn(n, sip, a + 8);
        if (op == 1 && tip == n->ip && n->ip) arp_packet(n, 2, a + 8, sip, a + 8);
        return;
    }
    if (type != 0x0800 || len < 34) return;
    const unsigned char *h = f + 14;
    unsigned ihl = (unsigned)(h[0] & 15) * 4, total = be16(h + 2), proto = h[9], src = be32(h + 12);
    if ((h[0] >> 4) != 4 || ihl < 20 || total < ihl || 14 + total > len || (be16(h + 6) & 0x3fff)) return;
    const unsigned char *p = h + ihl;
    unsigned plen = total - ihl;
    if (proto == 1) icmp_input(n, src, p, plen);
    else if (proto == 6) tcp_input(n, src, p, plen);
    else if (proto == 17 && plen >= 8) {
        unsigned dport = be16(p + 2), ulen = be16(p + 4);
        if (ulen < 8 || ulen > plen) return;
        if (dport == 68) dhcp_input(n, p + 8, ulen - 8);
        else if (be16(p) == 53) dns_input(n, p + 8, ulen - 8);
    }
}

/* ---- HTTP ---- */

/* GET http://host[:port]/path into `out`: the body's length, or -1; *http_status gets the HTTP
   status, *body the offset of the body in `out`. */
static long http_get(struct net *n, const char *url, unsigned char *out, u64 max, int *http_status, u64 *body) {
    const char *p = url;
    if (p[0] == 'h' && p[1] == 't' && p[2] == 't' && p[3] == 'p' && p[4] == ':' && p[5] == '/' && p[6] == '/') p += 7;
    else if (p[0] == 'h' && p[1] == 't' && p[2] == 't' && p[3] == 'p' && p[4] == 's' && p[5] == ':') return -2;
    char host[128];
    int h = 0;
    unsigned port = 80;
    while (*p && *p != '/' && *p != ':' && h < 127) host[h++] = *p++;
    host[h] = 0;
    if (*p == ':') { p++; port = 0; while (*p >= '0' && *p <= '9') port = port * 10 + (unsigned)(*p++ - '0'); }
    const char *path = *p ? p : "/";
    unsigned ip = resolve(n, host);
    if (!ip) return -3;
    unsigned char req[400];
    unsigned k = 0;
    const char *parts[] = {"GET ", path, " HTTP/1.0\r\nHost: ", host, "\r\nUser-Agent: leanos\r\nConnection: close\r\n\r\n"};
    for (int i = 0; i < 5; i++) for (const char *s = parts[i]; *s && k < sizeof req; s++) req[k++] = (unsigned char)*s;
    long got = tcp_exchange(n, ip, port, req, k, out, max);
    if (got < 12) return -1;
    *http_status = 0;
    for (int i = 9; i < 12; i++) *http_status = *http_status * 10 + (out[i] - '0');
    for (u64 i = 0; i + 3 < (u64)got; i++)
        if (out[i] == '\r' && out[i + 1] == '\n' && out[i + 2] == '\r' && out[i + 3] == '\n') {
            *body = i + 4;
            return got - (long)(i + 4);
        }
    return -1;
}
