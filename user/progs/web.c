/* web: a text web browser, from the SD card. It reads pages over http:// through the USB
   driver's network service, which answers it only if Terminal allowed it (`run -net web`);
   started any other way, it can show nothing from the network, and says so.

   Type an address and press Enter. A page shows as text: headings in bold, list items with a
   dash, links in blue with their number. Click a link, or type its number and press Enter.
   The up and down arrows scroll. No https yet, no pictures, no scripts (never). */
#include "../ui.h"
#include "../net.h"

#define WW 480
#define WH 300                    /* 141 pages of pixels, from page 64 of the spare run */
#define BAR 36                    /* the address bar */
#define PAD 12
#define LH 18
#define TEXT_PAGE (SPARE_PAGE + 205)            /* after the window, before the network buffer */
#define TEXT_MAX (19 * 4096 - 16)
#define MAX_LINES 1800
#define MAX_LINKS 48
#define URL_MAX 200

/* In the text: a link starts with LINK_ON and its number + 1, and ends with LINK_OFF; a
   paragraph that starts with HEAD is a heading. Paragraphs end with '\n'. */
enum { LINK_ON = 1, LINK_OFF = 2, HEAD = 3 };

struct web {
    struct ui ui;
    struct surface win;
    struct net_client net;
    char url[URL_MAX + 1];                 /* the page shown */
    char typed[URL_MAX + 1];               /* the address bar, while typing */
    int ntyped;
    char links[MAX_LINKS][URL_MAX + 1];
    int nlinks;
    char *text;
    long len;
    unsigned line[MAX_LINES];              /* where each line starts in the text */
    unsigned char line_link[MAX_LINES];    /* the link open at its start (number + 1), or 0 */
    unsigned char line_head[MAX_LINES];    /* bit 0: a heading; bit 1: the first line of a paragraph */
    int nlines, top;
    struct { short x0, x1, y0, n; } box[80];   /* where the links on screen are */
    int nbox;
    char note[120];                        /* the status line */
    char title[80];
    /* the HTML reader */
    int mode;                              /* 0 text, 1 tag, 2 entity, 3 comment */
    char tag[240];
    int ntag;
    char ent[12];
    int nent;
    int skip;                              /* inside script or style */
    int in_title, space, link_open, cut;
};

#define WEB ((struct web *)DATA)

/* ---- the text ---- */

static void put(struct web *w, char c) {
    if (w->len >= TEXT_MAX - 8) {
        w->cut = 1;
        return;
    }
    w->text[w->len++] = c;
}

static int at_para_start(struct web *w) { return w->len == 0 || w->text[w->len - 1] == '\n'; }

static void para(struct web *w) {
    if (w->link_open) { put(w, LINK_OFF); w->link_open = 0; }
    if (!at_para_start(w)) put(w, '\n');
    w->space = 0;
}

static void emit(struct web *w, char c) {
    if (w->in_title) {
        int n = 0;
        while (w->title[n]) n++;
        if (n < (int)sizeof w->title - 1 && !(c == ' ' && (n == 0 || w->title[n - 1] == ' '))) {
            w->title[n] = c;
            w->title[n + 1] = 0;
        }
        return;
    }
    if (w->skip) return;
    if (c == ' ' || c == '\n' || c == '\t' || c == '\r') { w->space = 1; return; }
    if (w->space && !at_para_start(w) && w->text[w->len - 1] != HEAD) put(w, ' ');
    w->space = 0;
    put(w, c);
}

static void emit_s(struct web *w, const char *s) { while (*s) emit(w, *s++); }

/* A character from an entity or a number: ASCII as is, the rest as UTF-8. */
static void emit_cp(struct web *w, unsigned cp) {
    if (cp == 0xA0) { emit(w, ' '); return; }
    if (cp < 0x80) { emit(w, (char)cp); return; }
    if (cp < 0x800) { emit(w, (char)(0xC0 | cp >> 6)); emit(w, (char)(0x80 | (cp & 63))); return; }
    if (cp < 0x10000) {
        emit(w, (char)(0xE0 | cp >> 12));
        emit(w, (char)(0x80 | (cp >> 6 & 63)));
        emit(w, (char)(0x80 | (cp & 63)));
        return;
    }
    emit(w, '?');
}

static int same(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == 0 && *b == 0;
}

static void entity(struct web *w) {
    const char *e = w->ent;
    if (e[0] == '#') {
        unsigned v = 0;
        if (e[1] == 'x' || e[1] == 'X')
            for (int i = 2; e[i]; i++) v = v * 16 + (unsigned)(e[i] <= '9' ? e[i] - '0' : (e[i] | 32) - 'a' + 10);
        else
            for (int i = 1; e[i]; i++) v = v * 10 + (unsigned)(e[i] - '0');
        emit_cp(w, v);
    } else if (same(e, "amp")) emit(w, '&');
    else if (same(e, "lt")) emit(w, '<');
    else if (same(e, "gt")) emit(w, '>');
    else if (same(e, "quot")) emit(w, '"');
    else if (same(e, "apos")) emit(w, '\'');
    else if (same(e, "nbsp")) emit(w, ' ');
    else if (same(e, "copy")) emit_cp(w, 0xA9);
    else if (same(e, "mdash")) emit_cp(w, 0x2014);
    else if (same(e, "ndash")) emit_cp(w, 0x2013);
    else { emit(w, '&'); emit_s(w, e); emit(w, ';'); }
}

/* The value of attribute `name` in the tag text, into `out`. */
static int attr(const char *tag, const char *name, char *out, int max) {
    for (int i = 0; tag[i]; i++) {
        int k = 0;
        while (name[k] && (tag[i + k] | 32) == name[k]) k++;
        if (name[k] || (i > 0 && tag[i - 1] != ' ' && tag[i - 1] != '\t' && tag[i - 1] != '\n')) continue;
        int j = i + k;
        while (tag[j] == ' ') j++;
        if (tag[j] != '=') continue;
        j++;
        while (tag[j] == ' ') j++;
        char q = tag[j] == '"' || tag[j] == '\'' ? tag[j++] : 0;
        int n = 0;
        while (tag[j] && (q ? tag[j] != q : tag[j] != ' ' && tag[j] != '>') && n < max) out[n++] = tag[j++];
        out[n] = 0;
        return 1;
    }
    return 0;
}

static void tag_done(struct web *w) {
    char *t = w->tag;
    t[w->ntag] = 0;
    int close = t[0] == '/';
    char name[12];
    int n = 0;
    for (int i = close; t[i] && t[i] != ' ' && t[i] != '/' && t[i] != '\t' && t[i] != '\n' && n < 11; i++)
        name[n++] = (char)(t[i] | 32);
    name[n] = 0;
    if (w->skip) {                          /* only the end of the script or style counts */
        if (close && (same(name, "script") || same(name, "style"))) w->skip = 0;
        return;
    }
    if (same(name, "script") || same(name, "style")) { if (!close) w->skip = 1; return; }
    if (same(name, "title")) { w->in_title = !close; return; }
    if (same(name, "br")) { if (w->link_open) put(w, LINK_OFF); put(w, '\n'); if (w->link_open) { put(w, LINK_ON); put(w, (char)w->link_open); } w->space = 0; return; }
    int heading = name[0] == 'h' && name[1] >= '1' && name[1] <= '6' && !name[2];
    if (heading) {
        para(w);
        if (!close) put(w, HEAD);
        return;
    }
    if (same(name, "li")) {
        para(w);
        if (!close) { emit(w, '-'); w->space = 1; }
        return;
    }
    static const char *const blocks[] = {"p", "div", "ul", "ol", "tr", "table", "section", "article", "header",
                                         "footer", "nav", "pre", "blockquote", "hr", "main", "dl", "dt", "dd", "form"};
    for (unsigned i = 0; i < sizeof blocks / sizeof blocks[0]; i++)
        if (same(name, blocks[i])) { para(w); return; }
    if (same(name, "a")) {
        if (close) {
            if (w->link_open) {
                put(w, LINK_OFF);
                /* its number after it */
                char num[8] = {'[', 0};
                int k = w->link_open, m = 1;
                if (k >= 10) num[m++] = (char)('0' + k / 10);
                num[m++] = (char)('0' + k % 10);
                num[m++] = ']';
                num[m] = 0;
                emit_s(w, num);
                w->link_open = 0;
            }
        } else if (w->nlinks < MAX_LINKS && attr(t, "href", w->links[w->nlinks], URL_MAX)) {
            if (w->space && !at_para_start(w)) put(w, ' ');
            w->space = 0;
            w->link_open = ++w->nlinks;
            put(w, LINK_ON);
            put(w, (char)w->link_open);
        }
    }
}

/* Read `n` more bytes of the page. */
static void feed(struct web *w, const char *p, long n) {
    for (long i = 0; i < n; i++) {
        char c = p[i];
        if (w->mode == 0) {
            if (c == '<') { w->mode = 1; w->ntag = 0; }
            else if (c == '&' && !w->skip) { w->mode = 2; w->nent = 0; }
            else emit(w, c);
        } else if (w->mode == 1) {
            if (w->ntag == 3 && w->tag[0] == '!' && w->tag[1] == '-' && w->tag[2] == '-') { w->mode = 3; w->ntag = 0; }
            if (w->mode == 3) continue;
            if (c == '>') { w->mode = 0; tag_done(w); }
            else if (w->ntag < (int)sizeof w->tag - 1) w->tag[w->ntag++] = c;
        } else if (w->mode == 2) {
            if (c == ';' || w->nent >= 10) { w->ent[w->nent] = 0; w->mode = 0; entity(w); }
            else if (((c | 32) >= 'a' && (c | 32) <= 'z') || (c >= '0' && c <= '9') || c == '#') w->ent[w->nent++] = c;
            else { w->ent[w->nent] = 0; w->mode = 0; emit(w, '&'); emit_s(w, w->ent); emit(w, c); }
        } else {                              /* a comment: until --> */
            w->tag[w->ntag % 3] = c;
            w->ntag++;
            if (c == '>' && w->ntag >= 3 && w->tag[(w->ntag - 2) % 3] == '-' && w->tag[(w->ntag - 3) % 3] == '-') w->mode = 0;
        }
    }
}

static void reset_page(struct web *w) {
    w->len = 0;
    w->nlinks = 0;
    w->mode = 0;
    w->skip = w->in_title = w->space = w->link_open = w->cut = 0;
    w->title[0] = 0;
    w->top = 0;
}

/* ---- lines ---- */

static const struct font *font_for(struct web *w, int head) { return head ? &w->ui.bold : &w->ui.body; }

/* The width of text[a, b) in a font, markers not counted. */
static int span_width(struct web *w, const struct font *f, long a, long b) {
    char buf[128];
    int n = 0, width = 0;
    for (long i = a; i < b; i++) {
        char c = w->text[i];
        if (c == LINK_ON) { i++; continue; }
        if (c == LINK_OFF || c == HEAD) continue;
        buf[n++] = c;
        if (n == (int)sizeof buf - 1) { buf[n] = 0; width += font_width(f, buf); n = 0; }
    }
    buf[n] = 0;
    return width + font_width(f, buf);
}

static void layout(struct web *w) {
    int max = WW - 2 * PAD - 8;
    w->nlines = 0;
    long i = 0;
    int link = 0;
    while (i < w->len && w->nlines < MAX_LINES) {
        int head = w->text[i] == HEAD;
        const struct font *f = font_for(w, head);
        long end = i;
        while (end < w->len && w->text[end] != '\n') end++;
        /* this paragraph, in lines */
        long start = i;
        while (start < end && w->nlines < MAX_LINES) {
            w->line[w->nlines] = (unsigned)start;
            w->line_link[w->nlines] = (unsigned char)link;
            w->line_head[w->nlines] = (unsigned char)(head | (start == i) << 1);
            w->nlines++;
            long fit = start, j = start;
            while (j < end) {
                long k = j;
                while (k < end && w->text[k] == ' ') k++;
                while (k < end && w->text[k] != ' ') k++;
                if (span_width(w, f, start, k) > max) break;
                fit = j = k;
            }
            if (fit == start) {                 /* one word wider than the window: cut it */
                fit = start + 1;
                while (fit < end && span_width(w, f, start, fit + 1) <= max) fit++;
            }
            for (long k = start; k < fit; k++) {
                if (w->text[k] == LINK_ON) link = (unsigned char)w->text[++k];
                else if (w->text[k] == LINK_OFF) link = 0;
            }
            start = fit;
            while (start < end && w->text[start] == ' ') start++;
        }
        if (start == end && i == end && w->nlines < MAX_LINES) {   /* an empty paragraph */
            w->line[w->nlines] = (unsigned)i;
            w->line_link[w->nlines] = (unsigned char)link;
            w->line_head[w->nlines++] = 2;
        }
        i = end + 1;
    }
}

/* ---- drawing ---- */

static void draw(struct web *w) {
    struct surface *s = &w->win;
    fill(s, 0, 0, WW, WH, rgb(252, 252, 250));
    /* the address bar */
    fill(s, 0, 0, WW, BAR, rgb(238, 239, 243));
    fill(s, 0, BAR - 1, WW, 1, rgb(214, 214, 220));
    round_rect(s, PAD, 6, WW - 2 * PAD, BAR - 12, 8, rgb(255, 255, 255), 255);
    const char *shown = w->ntyped ? w->typed : w->url[0] ? w->url : "Type an address: http://...";
    int x = PAD + 10;
    x = font_text(s, &w->ui.body, x, 23, shown, w->ntyped || w->url[0] ? rgb(36, 38, 46) : rgb(150, 150, 158));
    if (w->ntyped) fill(s, x + 1, 11, 2, 16, rgb(58, 110, 230));
    /* the page */
    w->nbox = 0;
    int rows = (WH - BAR - 26) / LH;
    int y = BAR + 8 + 13;
    for (int r = 0; w->top + r < w->nlines; r++) {
        int li = w->top + r;
        if (r) y += LH + (w->line_head[li] & 2 ? 6 : 0);    /* a little space between paragraphs */
        if (y > WH - 26) break;
        long a = w->line[li], b = li + 1 < w->nlines ? w->line[li + 1] : w->len;
        while (b > a && (w->text[b - 1] == '\n' || w->text[b - 1] == ' ')) b--;
        int head = w->line_head[li] & 1, link = w->line_link[li];
        const struct font *f = font_for(w, head);
        int px = PAD;
        char run[160];
        int n = 0, bx = px;
        for (long i = a; i <= b; i++) {
            char c = i < b ? w->text[i] : 0;
            int flush_now = i == b || c == LINK_ON || c == LINK_OFF || n == (int)sizeof run - 1;
            if (flush_now && n) {
                run[n] = 0;
                int nx = font_text(s, f, px, y, run, link ? rgb(40, 90, 210) : head ? rgb(20, 22, 30) : rgb(40, 42, 50));
                if (link) fill(s, px, y + 3, nx - px, 1, rgb(140, 170, 235));
                px = nx;
                n = 0;
            }
            if (i == b) break;
            if (c == LINK_ON) {
                if (link && w->nbox < 80) { w->box[w->nbox].x0 = (short)bx; w->box[w->nbox].x1 = (short)px; w->box[w->nbox].y0 = (short)(y - 13); w->box[w->nbox++].n = (short)link; }
                link = (unsigned char)w->text[++i];
                bx = px;
            } else if (c == LINK_OFF) {
                if (link && w->nbox < 80) { w->box[w->nbox].x0 = (short)bx; w->box[w->nbox].x1 = (short)px; w->box[w->nbox].y0 = (short)(y - 13); w->box[w->nbox++].n = (short)link; }
                link = 0;
            } else if (c != HEAD) run[n++] = c;
        }
        if (link && w->nbox < 80) { w->box[w->nbox].x0 = (short)bx; w->box[w->nbox].x1 = (short)px; w->box[w->nbox].y0 = (short)(y - 13); w->box[w->nbox++].n = (short)link; }
    }
    /* the status line */
    fill(s, 0, WH - 22, WW, 22, rgb(238, 239, 243));
    font_text(s, &w->ui.small, PAD, WH - 7, w->note, rgb(110, 112, 124));
    if (w->nlines > rows) {
        int th = (WH - BAR - 26) * rows / w->nlines, ty = BAR + 2 + (WH - BAR - 26 - th) * w->top / (w->nlines - rows);
        round_rect(s, WW - 7, ty, 4, th < 12 ? 12 : th, 2, rgb(190, 192, 200), 255);
    }
}

/* ---- going places ---- */

static void copy(char *d, const char *s, int max) {
    int i = 0;
    for (; s[i] && i < max; i++) d[i] = s[i];
    d[i] = 0;
}

static int starts_with(const char *s, const char *p) {
    while (*p) if ((*s++ | 32) != (*p++ | 32)) return 0;
    return 1;
}

/* A link's address, made whole against the page it is on. */
static void resolve_link(struct web *w, const char *href, char *out) {
    if (starts_with(href, "http://") || starts_with(href, "https://")) { copy(out, href, URL_MAX); return; }
    if (href[0] == '/' && href[1] == '/') { copy(out, "http:", URL_MAX); copy(out + 5, href, URL_MAX - 5); return; }
    int n = 0;
    const char *u = w->url;
    if (href[0] == '/') {                        /* from the host */
        int slashes = 0;
        while (u[n] && !(u[n] == '/' && ++slashes == 3)) n++;
    } else {                                     /* from the page's folder */
        int last = 0;
        for (int i = 0; u[i]; i++) if (u[i] == '/') last = i;
        n = last + 1;
        int slashes = 0;
        for (int i = 0; i < n; i++) slashes += u[i] == '/';
        if (slashes < 3) { n = 0; while (u[n]) n++; out[n] = '/'; for (int i = 0; i < n; i++) out[i] = u[i]; n++; copy(out + n, href, URL_MAX - n); return; }
    }
    if (n > URL_MAX) n = URL_MAX;
    for (int i = 0; i < n; i++) out[i] = u[i];
    copy(out + n, href, URL_MAX - n);
}

static void set_note(struct web *w, const char *a, const char *b) {
    int n = 0;
    for (int i = 0; a[i] && n < 118; i++) w->note[n++] = a[i];
    for (int i = 0; b && b[i] && n < 118; i++) w->note[n++] = b[i];
    w->note[n] = 0;
}

static const char *net_why(u64 code) {
    return code == NET_DENIED ? "not allowed to use the network: start it with run -net web"
         : code == NET_NO_DEVICE ? "no network adapter" : code == NET_NO_ADDRESS ? "no address from the network"
         : code == NET_NO_HOST ? "no such host" : code == NET_NO_ANSWER ? "no answer"
         : code == NET_UNSUPPORTED ? "only http:// pages (no https yet)"
         : code == NET_NO_SERVICE ? "the network service did not answer" : "could not load";
}

static void go(struct web *w, struct line *l, const char *to) {
    char url[URL_MAX + 1];
    if (!starts_with(to, "http://") && !starts_with(to, "https://")) {
        copy(url, "http://", URL_MAX);
        copy(url + 7, to, URL_MAX - 7);
    } else copy(url, to, URL_MAX);
    put_s(l, "web: ");
    put_s(l, url);
    put_s(l, " -> ");
    struct res r = net_call(&w->net, NET_GET, 0, url);
    if (r.x[1] != NET_OK) {
        set_note(w, net_why(r.x[1]), 0);
        put_s(l, net_why(r.x[1]));
        put_s(l, "\n");
        flush(l);
        return;
    }
    u64 size = r.x[2], http = r.x[3];
    copy(w->url, url, URL_MAX);
    reset_page(w);
    for (u64 off = 0; off < size;) {
        struct res c = net_call(&w->net, NET_READ, off, 0);
        if (c.x[1] != NET_OK || c.x[2] == 0) break;
        feed(w, net_data(&w->net), (long)c.x[2]);
        off += c.x[2];
    }
    para(w);
    if (w->cut) emit_s(w, "(the page is cut off here)");
    layout(w);
    struct line m = {.n = 0};
    put_s(&m, w->title[0] ? w->title : "");
    if (w->title[0]) put_s(&m, " - ");
    put_dec(&m, size / 1024);
    put_s(&m, " KiB, ");
    put_dec(&m, (u64)w->nlinks);
    put_s(&m, w->nlinks == 1 ? " link" : " links");
    if (http != 200) { put_s(&m, ", HTTP "); put_dec(&m, http); }
    m.b[m.n < 118 ? m.n : 118] = 0;
    set_note(w, m.b, 0);
    put_dec(l, size);
    put_s(l, " bytes, HTTP ");
    put_dec(l, http);
    put_s(l, ", ");
    put_dec(l, (u64)w->nlinks);
    put_s(l, " links, ");
    put_dec(l, (u64)w->nlines);
    put_s(l, " lines");
    if (w->title[0]) { put_s(l, ": "); put_s(l, w->title); }
    put_s(l, "\n");
    flush(l);
}

static void follow(struct web *w, struct line *l, int n) {
    if (n < 1 || n > w->nlinks) { set_note(w, "no such link", 0); return; }
    char to[URL_MAX + 1];
    resolve_link(w, w->links[n - 1], to);
    go(w, l, to);
}

static void enter(struct web *w, struct line *l) {
    w->typed[w->ntyped] = 0;
    int number = w->ntyped > 0, n = 0;
    for (int i = 0; i < w->ntyped; i++) {
        if (w->typed[i] < '0' || w->typed[i] > '9') number = 0;
        else n = n * 10 + (w->typed[i] - '0');
    }
    char to[URL_MAX + 1];
    copy(to, w->typed, URL_MAX);
    w->ntyped = 0;
    if (number) follow(w, l, n);
    else if (to[0]) go(w, l, to);
}

static void welcome(struct web *w) {
    reset_page(w);
    const char *t = "<h1>web</h1><p>A text browser for leanos. Type an address (http:// only) and press Enter."
                    "<p>Links are blue, with their number. Click one, or type its number and press Enter. "
                    "The up and down arrows scroll.<p>It reaches the network only if you started it with "
                    "<b>run -net web</b> in Terminal: the network service answers only a program you allowed.";
    long n = 0;
    while (t[n]) n++;
    feed(w, t, n);
    para(w);
    layout(w);
    set_note(w, "ready", 0);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct web *w = WEB;
    struct line l = {.n = 0};
    ui_load(&w->ui, app_assets());
    w->win = app_surface(WW, WH);
    net_init_open(&w->net, SPARE_PAGE);
    w->text = (char *)PAGE(TEXT_PAGE);
    w->url[0] = 0;
    w->ntyped = 0;
    welcome(w);
    draw(w);
    u64 opened = app_open(WW, WH, "Web");
    put_s(&l, "web: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "web: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        int rows = (WH - BAR - 26) / LH;
        if (e.kind == EV_KEY) {
            u64 k = e.a;
            if (k == '\r' || k == '\n') {
                set_note(w, "loading...", 0);
                draw(w);
                app_poll(1);
                enter(w, &l);
            } else if (k == 127 || k == 8) {
                if (w->ntyped) w->ntyped--;
            } else if (k == 27) {
                w->ntyped = 0;
            } else if (k == KEY_DOWN) {
                if (w->top + rows < w->nlines) w->top += 3;
                if (w->top + rows > w->nlines) w->top = w->nlines > rows ? w->nlines - rows : 0;
            } else if (k == KEY_UP) {
                w->top = w->top > 3 ? w->top - 3 : 0;
            } else if (k >= 32 && k < 127 && w->ntyped < URL_MAX) {
                w->typed[w->ntyped++] = (char)k;
                w->typed[w->ntyped] = 0;
            }
            draw(w);
            dirty = 1;
        } else if (e.kind == EV_DOWN) {
            int x = (int)e.a, y = (int)e.b;
            for (int i = 0; i < w->nbox; i++)
                if (x >= w->box[i].x0 && x < w->box[i].x1 && y >= w->box[i].y0 && y < w->box[i].y0 + LH) {
                    set_note(w, "loading...", 0);
                    draw(w);
                    app_poll(1);
                    follow(w, &l, w->box[i].n);
                    break;
                }
            draw(w);
            dirty = 1;
        }
    }
}
