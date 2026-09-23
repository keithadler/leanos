/* calc: a calculator. Type an expression (digits, + - * / %, parentheses) and press Enter;
   Backspace deletes, Escape clears. Whole numbers, with the usual precedence. */
#include "../app.h"

#define CW 360
#define CH 150

struct calc {
    struct surface win;
    char in[40];
    int len;
    char out[40];
    const char *p;        /* the parser's position */
    int shown;            /* a result is on screen: the next key starts a new expression */
    int err;
};

static long expr(struct calc *c);

static void skip(struct calc *c) { while (*c->p == ' ') c->p++; }

static long factor(struct calc *c) {
    skip(c);
    if (*c->p == '-') { c->p++; return -factor(c); }
    if (*c->p == '(') {
        c->p++;
        long v = expr(c);
        skip(c);
        if (*c->p == ')') c->p++; else c->err = 1;
        return v;
    }
    if (*c->p < '0' || *c->p > '9') { c->err = 1; return 0; }
    long v = 0;
    while (*c->p >= '0' && *c->p <= '9') v = v * 10 + (*c->p++ - '0');
    return v;
}

static long term(struct calc *c) {
    long v = factor(c);
    for (;;) {
        skip(c);
        char op = *c->p;
        if (op != '*' && op != '/' && op != '%') return v;
        c->p++;
        long r = factor(c);
        if ((op == '/' || op == '%') && r == 0) { c->err = 2; return 0; }
        v = op == '*' ? v * r : op == '/' ? v / r : v % r;
    }
}

static long expr(struct calc *c) {
    long v = term(c);
    for (;;) {
        skip(c);
        char op = *c->p;
        if (op != '+' && op != '-') return v;
        c->p++;
        long r = term(c);
        v = op == '+' ? v + r : v - r;
    }
}

static void evaluate(struct calc *c) {
    c->in[c->len] = 0;
    c->p = c->in;
    c->err = 0;
    long v = expr(c);
    skip(c);
    if (*c->p) c->err = 1;
    struct line l = {.n = 0};
    if (c->err == 2) put_s(&l, "cannot divide by 0");
    else if (c->err) put_s(&l, "not an expression");
    else {
        put_s(&l, "= ");
        if (v < 0) { put_s(&l, "-"); v = -v; }
        put_dec(&l, (u64)v);
    }
    int n = (int)l.n < 39 ? (int)l.n : 39;
    for (int i = 0; i < n; i++) c->out[i] = l.b[i];
    c->out[n] = 0;
    struct line log = {.n = 0};
    put_s(&log, "calc: ");
    put_s(&log, c->in);
    put_s(&log, " ");
    put_s(&log, c->out);
    put_s(&log, "\n");
    flush(&log);
}

static void draw(struct calc *c) {
    struct surface *s = &c->win;
    fill(s, 0, 0, CW, CH, rgb(28, 30, 40));
    round_rect(s, 12, 14, CW - 24, 50, 10, rgb(40, 44, 58), 255);
    c->in[c->len] = 0;
    int w = text_width(c->in, 3);
    text(s, CW - 24 - w, 28, c->in, rgb(230, 234, 244), 3);
    fill(s, CW - 22, 26, 3, 24, rgb(126, 214, 255));
    int ow = text_width(c->out, 3);
    text(s, CW - 24 - ow, 84, c->out, c->out[0] == '=' ? rgb(126, 214, 255) : rgb(255, 150, 140), 3);
    text(s, 16, CH - 20, "Enter: work it out   Esc: clear", rgb(120, 126, 150), 1);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct calc *c = (struct calc *)DATA;
    struct line l = {.n = 0};
    app_assets();
    c->win = app_surface(CW, CH);
    c->len = 0;
    c->shown = 0;
    c->out[0] = 0;
    draw(c);
    u64 opened = app_open(CW, CH, "Calc");
    put_s(&l, "calc: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind != EV_KEY) continue;
        char k = (char)e.a;
        if (c->shown && e.a != '\r' && e.a != '\n' && e.a != '=') {
            c->shown = 0;
            c->len = 0;
            c->out[0] = 0;
        }
        if (e.a == '\r' || e.a == '\n' || e.a == '=') { evaluate(c); c->shown = 1; }
        else if ((e.a == 127 || e.a == 8) && c->len > 0) c->len--;
        else if (e.a == 27) { c->len = 0; c->out[0] = 0; }
        else if (c->len < 20 && ((k >= '0' && k <= '9') || k == '+' || k == '-' || k == '*' ||
                                 k == '/' || k == '%' || k == '(' || k == ')' || k == ' '))
            c->in[c->len++] = k;
        else continue;
        draw(c);
        dirty = 1;
    }
}
