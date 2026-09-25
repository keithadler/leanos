/* Apps: every program, with its icon. The built-in apps first (clicking one asks the display
   server to start it, as its dock icon would), then every program on the SD card: click one
   to start it in a free open slot; a dot marks those running. A card program NAME's icon is
   the file NAME.icon beside it (tools/mkicon.py), and rides along in the program's image, so
   the program can show it in its title bar and the dock; without one it gets a tile with its
   initial.

   It is in the manifest, slot 16: a window, the file server (to read programs and icons),
   and the launch capabilities for the open slots. What a program it starts may do is fixed
   by the open slot, not by the launcher. */
#include "app.h"
#include "fs.h"
#include "elfload.h"
#include "net.h"

#define AW 480
#define AH 336
#define CELL_W 88
#define CELL_H 84
#define COLS 5
#define ICON 48
#define GRID_X 20
#define BUILTIN_Y 34
#define CARD_Y 170
#define MAX_PROGS 10
#define LAUNCH_OPEN 6
#define OPEN_FIRST 10
#define OPEN_SLOTS 6
/* the spare run: assets (fonts, built-in icons) first, then */
#define IMAGE_PAGE 24      /* a program's image, pages 24-39 */
#define WIN_OFFSET 40      /* the window's pixels, 158 pages */
#define ICONS_PAGE 198     /* card icons, 48 px, one after another up to page 224 */
#define ICON_BYTES (8 + ICON * ICON * 4)
#define ICON_SLOTS ((224 - ICONS_PAGE) * 4096 / ICON_BYTES)
enum { F_UI = 1, F_TITLE = 2, F_SMALL = 3, F_LABEL = 4 };

#define NBUILTIN 5
static const char *const builtin_names[NBUILTIN] = {"Notes", "Files", "Terminal", "Settings", "Security"};

struct prog {
    char name[FS_NAME_MAX + 1];
    int icon;              /* icon slot + 1, or 0 */
    int slot;              /* the open slot it was started in + 1, or 0 */
};

struct launcher {
    struct font ui, title, small, label;
    struct picture builtin[NBUILTIN];
    struct surface win;
    struct fs_client fs;
    struct net_client net;
    struct prog p[MAX_PROGS];
    int n;
    int pressed;           /* the cell drawn pressed: 0-4 built-in, 10 + i a card program, -1 none */
};

static unsigned *icon_at(int i) { return (unsigned *)((char *)PAGE(SPARE_PAGE + ICONS_PAGE) + i * ICON_BYTES); }

static int has_dot(const char *s) {
    for (; *s; s++) if (*s == '.') return 1;
    return 0;
}

/* An icon asset (w, h, premultiplied pixels) shrunk to ICON x ICON, each pixel the average
   of those it covers, stored the same way. */
static void shrink(unsigned *dst, const unsigned *src) {
    int w = (int)src[0], h = (int)src[1];
    const unsigned *px = src + 2;
    dst[0] = ICON;
    dst[1] = ICON;
    for (int j = 0; j < ICON; j++)
        for (int i = 0; i < ICON; i++) {
            int x0 = i * w / ICON, x1 = (i + 1) * w / ICON, y0 = j * h / ICON, y1 = (j + 1) * h / ICON;
            if (x1 <= x0) x1 = x0 + 1;
            if (y1 <= y0) y1 = y0 + 1;
            unsigned a = 0, r = 0, g = 0, b = 0, n = 0;
            for (int y = y0; y < y1; y++)
                for (int x = x0; x < x1; x++) {
                    unsigned v = px[y * w + x];
                    a += v >> 24; r += (v >> 16) & 255; g += (v >> 8) & 255; b += v & 255; n++;
                }
            dst[2 + j * ICON + i] = (a / n) << 24 | (r / n) << 16 | (g / n) << 8 | (b / n);
        }
}

static void icon_name(char *out, const char *name) {
    int m = 0;
    for (; name[m] && m < FS_NAME_MAX; m++) out[m] = name[m];
    const char *ext = ".icon";
    for (int x = 0; ext[x]; x++) out[m++] = ext[x];
    out[m] = 0;
}

/* The programs on the card, and their icons. */
static void scan(struct launcher *st, struct line *l) {
    long count = fs_list(&st->fs);
    struct fs_entry list[48];
    const struct fs_entry *e = fs_entries(&st->fs);
    for (long i = 0; i < count && i < 48; i++) list[i] = e[i];
    int icons = 0;
    st->n = 0;
    for (long i = 0; i < count && st->n < MAX_PROGS; i++) {
        if (has_dot(list[i].name)) continue;
        struct prog *p = &st->p[st->n];
        int k = 0;
        for (; list[i].name[k] && k < FS_NAME_MAX; k++) p->name[k] = list[i].name[k];
        p->name[k] = 0;
        p->icon = 0;
        p->slot = 0;
        char iconname[FS_NAME_MAX + 6];
        icon_name(iconname, p->name);
        if (icons < ICON_SLOTS) {
            long size = fs_read(&st->fs, iconname);
            const unsigned *d = (const unsigned *)fs_data(&st->fs);
            if (size > 8 && d[0] > 0 && d[1] > 0 && d[0] <= 64 && d[1] <= 64 && (long)(8 + d[0] * d[1] * 4) <= size) {
                shrink(icon_at(icons), d);
                p->icon = ++icons;
            }
        }
        st->n++;
    }
    put_s(l, "apps: ");
    put_dec(l, (u64)st->n);
    put_s(l, " programs, ");
    put_dec(l, (u64)icons);
    put_s(l, " with icons\n");
    flush(l);
}

static int running(struct prog *p) {
    return p->slot && sys1(SYS_BOOTINFO, (u64)(p->slot - 1)).x[4] == 1;
}

static void cell(struct launcher *st, int x, int y, const struct picture *pic, const char *name, int dot, int pressed) {
    struct surface *s = &st->win;
    static const unsigned tints[6] = {0x3a6ee6, 0x2eaa6e, 0xe0873a, 0x9b59d0, 0xd8465a, 0x2a9dc0};
    if (pressed) round_rect(s, x + 4, y, CELL_W - 8, CELL_H - 4, 12, rgb(222, 228, 244), 255);
    int ix = x + CELL_W / 2 - ICON / 2, iy = y + 6;
    if (pic && pic->px) icon(s, ix, iy, pic);
    else {
        round_rect(s, ix + 2, iy + 2, ICON - 4, ICON - 4, 12, tints[(unsigned char)name[0] % 6], 255);
        char ch[2] = {name[0] >= 'a' && name[0] <= 'z' ? (char)(name[0] - 32) : name[0], 0};
        font_text(s, &st->title, ix + ICON / 2 - font_width(&st->title, ch) / 2, iy + ICON / 2 + 7, ch,
                  rgb(255, 255, 255));
    }
    char label[FS_NAME_MAX + 1];
    int k = 0;
    for (; name[k] && k < FS_NAME_MAX; k++) label[k] = name[k];
    label[k] = 0;
    if (label[0] >= 'a' && label[0] <= 'z') label[0] = (char)(label[0] - 32);
    int w = font_width(&st->ui, label);
    font_text(s, &st->ui, x + CELL_W / 2 - w / 2, y + ICON + 24, label, rgb(40, 40, 50));
    if (dot) round_rect(s, x + CELL_W / 2 - 3, y + ICON + 31, 6, 6, 3, rgb(58, 110, 230), 255);
}

static void draw(struct launcher *st) {
    struct surface *s = &st->win;
    fill(s, 0, 0, AW, AH, rgb(247, 247, 250));
    font_text(s, &st->label, GRID_X, 24, "BUILT IN", rgb(140, 144, 158));
    for (int i = 0; i < NBUILTIN; i++)
        cell(st, GRID_X + i * CELL_W, BUILTIN_Y, &st->builtin[i], builtin_names[i], 0, st->pressed == i);
    fill(s, GRID_X, CARD_Y - 30, AW - 2 * GRID_X, 1, rgb(226, 228, 236));
    font_text(s, &st->label, GRID_X, CARD_Y - 10, "ON THE SD CARD", rgb(140, 144, 158));
    for (int i = 0; i < st->n; i++) {
        struct prog *p = &st->p[i];
        struct picture pic = {0, 0, 0};
        if (p->icon) {
            const unsigned *raw = icon_at(p->icon - 1);
            pic.w = (int)raw[0];
            pic.h = (int)raw[1];
            pic.px = raw + 2;
        }
        cell(st, GRID_X + (i % COLS) * CELL_W, CARD_Y + (i / COLS) * CELL_H, p->icon ? &pic : 0, p->name,
             running(p), st->pressed == 10 + i);
    }
    if (st->n == 0) font_text(s, &st->ui, GRID_X, CARD_Y + 30, "No programs on the SD card.", rgb(120, 120, 130));
    const char *hint = "Each program from the card gets its own memory and a window, nothing else.";
    font_text(s, &st->small, AW / 2 - font_width(&st->small, hint) / 2, AH - 12, hint, rgb(130, 130, 145));
}

/* Read the program (and its icon), make its image, and start it in a free open slot. */
static void start(struct launcher *st, struct line *l, int i) {
    struct prog *p = &st->p[i];
    const char *why = 0;
    if (app_raise(p->name)) {
        put_s(l, "apps: ");
        put_s(l, p->name);
        put_s(l, " is already open\n");
        flush(l);
        return;
    }
    unsigned char *image = (unsigned char *)PAGE(SPARE_PAGE + IMAGE_PAGE);
    u64 len = 0;
    why = elf_load(&st->fs, p->name, image, &len);
    if (!why) {
        char iconname[FS_NAME_MAX + 6];
        icon_name(iconname, p->name);
        long isize = fs_read(&st->fs, iconname);
        image_add_icon(image, &len, (const unsigned char *)fs_data(&st->fs), isize > 0 ? (u64)isize : 0, p->name);
        why = "no free slot: close a program first";
        for (int k = 0; k < OPEN_SLOTS; k++) {
            if (sys1(SYS_BOOTINFO, OPEN_FIRST + (u64)k).x[4] == 1) continue;
            /* its own folder on the card, apps/NAME, and nothing else */
            char folder[FS_PATH_MAX + 1] = "apps/";
            for (int i = 0; p->name[i] && i < FS_NAME_MAX; i++) { folder[5 + i] = p->name[i]; folder[6 + i] = 0; }
            fs_unshare(&st->fs, OPEN_FIRST + (u64)k);
            fs_share(&st->fs, folder, OPEN_FIRST + (u64)k, FS_R | FS_W, 1);
            if (sys(SYS_EXEC, LAUNCH_OPEN + (u64)k, (u64)image, len, 0, 0).status != OK) continue;
            /* the network: only for the browser (what ran in this slot before loses it) */
            int wants = p->name[0] == 'w' && p->name[1] == 'e' && p->name[2] == 'b' && !p->name[3];
            net_call(&st->net, NET_ALLOW, OPEN_FIRST + (u64)k | (u64)wants << 8, 0);
            p->slot = OPEN_FIRST + k + 1;
            why = 0;
            break;
        }
    }
    put_s(l, "apps: ");
    put_s(l, p->name);
    if (why) {
        put_s(l, ": ");
        put_s(l, why);
    } else {
        put_s(l, " started in slot ");
        put_dec(l, (u64)(p->slot - 1));
    }
    put_s(l, "\n");
    flush(l);
}

/* Start the card program called `name`, if the card has it. */
static void start_named(struct launcher *st, struct line *l, const char *name) {
    for (int i = 0; i < st->n; i++) {
        int j = 0;
        while (j < 15 && name[j] && name[j] == st->p[i].name[j]) j++;
        if (name[j] == st->p[i].name[j]) {
            start(st, l, i);
            return;
        }
    }
    put_s(l, "apps: ");
    put_s(l, name);
    put_s(l, " is not on the SD card\n");
    flush(l);
}

/* Which cell is at (x, y): 0-4 a built-in app, 10 + i a card program, -1 none. */
static int hit(struct launcher *st, int x, int y) {
    if (x < GRID_X) return -1;
    int col = (x - GRID_X) / CELL_W;
    if (col >= COLS) return -1;
    if (y >= BUILTIN_Y && y < BUILTIN_Y + CELL_H) return col < NBUILTIN ? col : -1;
    if (y >= CARD_Y) {
        int i = (y - CARD_Y) / CELL_H * COLS + col;
        return i < st->n ? 10 + i : -1;
    }
    return -1;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct launcher *st = (struct launcher *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->title = font_of(assets, F_TITLE);
    st->small = font_of(assets, F_SMALL);
    st->label = font_of(assets, F_LABEL);
    for (int i = 0; i < NBUILTIN; i++) st->builtin[i] = picture_of(assets, ASSET_ICON, 10 + (unsigned)i);
    st->win = app_surface_at(WIN_OFFSET, AW, AH);
    fs_init(&st->fs, SPARE_PAGE);
    net_init(&st->net, SPARE_PAGE);
    st->pressed = -1;
    scan(st, &l);
    /* Started by a click on a program pinned in the dock? Then start that, and nothing else.
       Started by the display server at boot ("@startup")? Then open what startup.txt on
       the card lists: program names, and "apps" for this window (# starts a comment). */
    struct res pend = sys(SYS_CALL, ENDPOINT, OP_PENDING, 0, 0, 0);
    char startup[512];
    int nstartup = 0, show = 1;
    if (pend.status == OK && pend.x[2]) {
        char name[17];
        for (int i = 0; i < 16; i++) name[i] = (char)(pend.x[2 + i / 8] >> (8 * (i % 8)));
        name[16] = 0;
        if (name[0] != '@') {
            start_named(st, &l, name);
            exit_task();
        }
        long n = fs_read(&st->fs, "startup.txt");
        if (n <= 0) exit_task();                 /* nothing to open at startup */
        const char *d = fs_data(&st->fs);
        for (long i = 0; i < n && i < (long)sizeof startup - 1; i++) startup[nstartup++] = d[i];
        startup[nstartup] = 0;
        show = 0;
        for (int i = 0; i + 3 < nstartup; i++)
            if ((i == 0 || startup[i - 1] <= ' ') && startup[i] == 'a' && startup[i + 1] == 'p' &&
                startup[i + 2] == 'p' && startup[i + 3] == 's' && (i + 4 == nstartup || startup[i + 4] <= ' '))
                show = 1;
        put_s(&l, "apps: opening what startup.txt lists\n");
        flush(&l);
    }
    u64 opened = BAD_ARG;
    if (show) {
        draw(st);
        opened = app_open_at(WIN_OFFSET, AW, AH, "Apps");
        put_s(&l, "apps: opened a window");
        put_s(&l, outcome(opened));
        put_s(&l, "\n");
        flush(&l);
    }
    /* the startup programs, after this window, so the last one listed ends up in front */
    for (int i = 0; i < nstartup;) {
        while (i < nstartup && startup[i] <= ' ') i++;
        if (startup[i] == '#') { while (i < nstartup && startup[i] != '\n') i++; continue; }
        char name[FS_NAME_MAX + 1];
        int k = 0;
        while (i < nstartup && startup[i] > ' ' && k < FS_NAME_MAX) name[k++] = startup[i++];
        while (i < nstartup && startup[i] > ' ') i++;
        name[k] = 0;
        if (k && !(k == 4 && name[0] == 'a' && name[1] == 'p' && name[2] == 'p' && name[3] == 's')) start_named(st, &l, name);
    }
    if (opened != OK) exit_task();
    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) exit_task();
        if (e.kind == EV_LAUNCH) {          /* from the dock: up to 8 bytes of a name */
            char name[9];
            for (int i = 0; i < 8; i++) name[i] = (char)((i < 4 ? e.a : e.b) >> (8 * (i % 4)));
            name[8] = 0;
            start_named(st, &l, name);
            continue;
        }
        if (e.kind != EV_DOWN) continue;
        int c = hit(st, (int)e.a, (int)e.b);
        if (c < 0) continue;
        st->pressed = c;
        draw(st);
        if (c < NBUILTIN) {
            put_s(&l, "apps: asked the display server to start ");
            put_s(&l, builtin_names[c]);
            put_s(&l, "\n");
            flush(&l);
            sys(SYS_CALL, ENDPOINT, OP_START, (u64)c, 0, 0);
        } else {
            start(st, &l, c - 10);
        }
        st->pressed = -1;
        draw(st);
        dirty = 1;
    }
}
