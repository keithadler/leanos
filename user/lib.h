/* System calls for user programs. The numbers match `syscall` in LeanOS/Kernel.lean. */
#pragma once

typedef unsigned long u64;

/* x0 is the status (0 = ok); the rest depend on the call. */
struct res { u64 x[7]; };
#define status x[0]

enum { SYS_WRITE, SYS_YIELD, SYS_MAP, SYS_UNMAP, SYS_DERIVE, SYS_EXIT, SYS_CAPINFO, SYS_WHOAMI,
       SYS_SEND, SYS_RECV, SYS_CALL, SYS_REPLY, SYS_IRQWAIT, SYS_IRQACK };
enum { OK = 0, NO_CAP = 1, BAD_ARG = 2, NO_CALL = 3, FULL = 4 };
/* Frame rights: read, write, execute. Endpoint rights use the same bits for receive,
   send, grant. */
enum { R = 1, W = 2, X = 4 };
enum { RECV = 1, SEND = 2, GRANT = 4 };

/* Every task's window: code at pages 0-15, data at 16-23, stack at the top. Capabilities
   0-3 are runs of frames: code (16 pages), data (8), stack (4) and spare (36, unmapped).
   Capability 4, if any, is the task's endpoint. */
#define DATA PAGE(16)
#define PAGE(n) (0x80000000UL + (n) * 4096UL)
#define ENDPOINT 4

static inline struct res sys(u64 n, u64 a0, u64 a1, u64 a2, u64 a3, u64 a4) {
    register u64 x8 __asm__("x8") = n;
    register u64 x0 __asm__("x0") = a0;
    register u64 x1 __asm__("x1") = a1;
    register u64 x2 __asm__("x2") = a2;
    register u64 x3 __asm__("x3") = a3;
    register u64 x4 __asm__("x4") = a4;
    register u64 x5 __asm__("x5");
    register u64 x6 __asm__("x6");
    __asm__ volatile("svc #0"
                     : "+r"(x0), "+r"(x1), "+r"(x2), "+r"(x3), "+r"(x4), "=r"(x5), "=r"(x6)
                     : "r"(x8)
                     : "memory");
    return (struct res){{x0, x1, x2, x3, x4, x5, x6}};
}
#define sys0(n) sys(n, 0, 0, 0, 0, 0)
#define sys1(n, a) sys(n, a, 0, 0, 0, 0)
#define sys2(n, a, b) sys(n, a, b, 0, 0, 0)

static inline u64 slen(const char *s) { u64 n = 0; while (s[n]) n++; return n; }
static inline struct res print(const char *s) { return sys2(SYS_WRITE, (u64)s, slen(s)); }
static inline void exit_task(void) { sys0(SYS_EXIT); for (;;) {} }

/* Format into a stack buffer and print it in one call, so lines never interleave. */
struct line { char b[200]; u64 n; };
static inline void put_s(struct line *l, const char *s) { while (*s && l->n < sizeof l->b) l->b[l->n++] = *s++; }
static inline void put_hex(struct line *l, u64 v) {
    put_s(l, "0x");
    int started = 0;
    for (int i = 60; i >= 0; i -= 4) {
        int d = (v >> i) & 15;
        if ((d || started || i == 0) && l->n < sizeof l->b) { l->b[l->n++] = "0123456789abcdef"[d]; started = 1; }
    }
}
static inline void put_dec(struct line *l, u64 v) {
    char t[20]; int i = 0;
    do { t[i++] = '0' + v % 10; v /= 10; } while (v);
    while (i && l->n < sizeof l->b) l->b[l->n++] = t[--i];
}
static inline void put_rights(struct line *l, u64 r) {
    char s[4] = {r & R ? 'r' : '-', r & W ? 'w' : '-', r & X ? 'x' : '-', 0};
    put_s(l, s);
}
static inline void put_ep_rights(struct line *l, u64 r) {
    int any = 0;
    if (r & RECV) { put_s(l, "receive"); any = 1; }
    if (r & SEND) { put_s(l, any ? "+send" : "send"); any = 1; }
    if (r & GRANT) { put_s(l, any ? "+grant" : "grant"); any = 1; }
    if (!any) put_s(l, "nothing");
}
static inline const char *outcome(u64 st) {
    return st == OK ? " -> ok" : st == NO_CAP ? " -> refused, no such capability"
         : st == BAD_ARG ? " -> refused, not allowed" : st == FULL ? " -> refused, full"
         : " -> refused";
}
static inline void flush(struct line *l) { sys2(SYS_WRITE, (u64)l->b, l->n); l->n = 0; }

/* Burn time so the timer, not the program, decides when others run. */
static inline void spin(u64 n) { for (volatile u64 i = 0; i < n; i++) {} }

/* The time: the processor's virtual counter and how fast it counts. */
static inline u64 ticks(void) { u64 v; __asm__ volatile("isb; mrs %0, cntvct_el0" : "=r"(v)); return v; }
static inline u64 tick_rate(void) { u64 v; __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(v)); return v ? v : 54000000; }
static inline u64 millis(void) { return ticks() * 1000 / tick_rate(); }

/* The compiler may call these for struct copies and zeroing. */
void *memset(void *d, int c, unsigned long n) {
    unsigned char *p = d;
    while (n--) *p++ = (unsigned char)c;
    return d;
}
void *memcpy(void *d, const void *s, unsigned long n) {
    unsigned char *p = d;
    const unsigned char *q = s;
    while (n--) *p++ = *q++;
    return d;
}
