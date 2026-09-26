/* Files. Lists a folder of what the file server holds and shows the selected file. Click a
   file, or use the up and down arrows (the list scrolls), to show it; click a folder, or
   press Enter or the right arrow on it, to open it; the left arrow goes back up; click
   anywhere else to look again; Delete (or Backspace) removes the selected file or empty
   folder. Programs' icons (NAME.icon, fs.h) are not listed. It reaches the files only by
   asking the file server, one request at a time. */
#include "app.h"
#include "fs.h"

#define FW 460
#define FH 340
#define LIST_W 184
#define ROW_H 22
#define ROW_Y 40
#define MAX_SHOWN 12
#define PREVIEW_MAX 4096
enum { F_UI = 1, F_BOLD = 2, F_SMALL = 3, F_MONO = 4 };

struct files {
    struct font ui, bold, small, mono;
    struct surface win;
    struct fs_client fs;
    struct fs_entry list[128];
    long count;
    char dir[FS_PATH_MAX + 1];      /* the folder shown: "" is the top */
    char path[FS_PATH_MAX + 1];     /* scratch: dir + '/' + a name */
    int selected;                   /* -1: none */
    int top;                        /* the first file the list shows */
    char preview[PREVIEW_MAX + 1];
    long size;                      /* of the selected file, -1 if it could not be read */
};

/* The path of entry i in the folder shown. */
static const char *path_of(struct files *st, int i) {
    int n = 0;
    for (; st->dir[n]; n++) st->path[n] = st->dir[n];
    if (n) st->path[n++] = '/';
    for (int k = 0; st->list[i].name[k] && n < FS_PATH_MAX; k++) st->path[n++] = st->list[i].name[k];
    st->path[n] = 0;
    return st->path;
}

static void size_text(char *out, unsigned n) {
    char t[12];
    int i = 0;
    do { t[i++] = (char)('0' + n % 10); n /= 10; } while (n);
    int k = 0;
    while (i) out[k++] = t[--i];
    out[k++] = ' ';
    out[k++] = 'B';
    out[k] = 0;
}

static void draw(struct files *st) {
    struct surface *s = &st->win;
    fill(s, 0, 0, FW, FH, rgb(255, 255, 255));
    fill(s, 0, 0, LIST_W, FH, rgb(243, 243, 246));
    fill(s, LIST_W, 0, 1, FH, rgb(224, 224, 230));
    struct line head = {.n = 0};
    if (st->dir[0]) {
        put_s(&head, st->dir);
        put_s(&head, ": ");
    }
    put_dec(&head, (u64)(st->count < 0 ? 0 : st->count));
    put_s(&head, st->count == 1 ? " file" : " files");
    head.b[head.n] = 0;
    font_text(s, &st->bold, 16, 26, head.b, rgb(30, 30, 36));
    if (st->selected >= 0 && st->selected < st->top) st->top = st->selected;
    if (st->selected >= st->top + MAX_SHOWN) st->top = st->selected - MAX_SHOWN + 1;
    for (int r = 0; r < MAX_SHOWN && st->top + r < st->count; r++) {
        int i = st->top + r;
        int y = ROW_Y + r * ROW_H, sel = i == st->selected;
        if (sel) round_rect(s, 8, y, LIST_W - 16, ROW_H - 2, 6, rgb(58, 110, 230), 255);
        int folder = st->list[i].kind == FS_DIR;
        int nx = font_text(s, &st->ui, 16, y + 15, st->list[i].name, sel ? rgb(255, 255, 255) : rgb(40, 40, 48));
        if (folder) font_text(s, &st->ui, nx, y + 15, "/", sel ? rgb(255, 255, 255) : rgb(40, 40, 48));
        char n[16];
        if (folder) { n[0] = 'f'; n[1] = 'o'; n[2] = 'l'; n[3] = 'd'; n[4] = 'e'; n[5] = 'r'; n[6] = 0; }
        else size_text(n, st->list[i].size);
        font_text(s, &st->small, LIST_W - 16 - font_width(&st->small, n), y + 14, n,
                  sel ? rgb(220, 230, 255) : rgb(130, 130, 140));
    }
    if (st->count < 0) font_text(s, &st->small, 16, ROW_Y + 16, "The file server did not answer.", rgb(200, 60, 50));
    font_text(s, &st->small, 16, FH - 14, st->dir[0] ? "Left arrow: back up" : "Delete removes the selected file",
              rgb(150, 150, 160));

    int x0 = LIST_W + 16, right = FW - 16;
    if (st->selected < 0) {
        font_text(s, &st->ui, x0, 40, "Nothing selected", rgb(150, 150, 160));
        return;
    }
    font_text(s, &st->bold, x0, 26, st->list[st->selected].name, rgb(30, 30, 36));
    if (st->list[st->selected].kind == FS_DIR) {
        font_text(s, &st->ui, x0, 52, "A folder. Press Enter, or click it, to open it.", rgb(110, 110, 120));
        return;
    }
    if (st->size < 0) {
        font_text(s, &st->ui, x0, 52, "Could not read this file.", rgb(200, 60, 50));
        return;
    }
    /* the text, wrapped at word boundaries where it can be */
    int x = x0, y = 52;
    const char *p = st->preview;
    while (*p && y < FH - 8) {
        if (*p == '\n') { x = x0; y += 16; p++; continue; }
        int wl = 0, ww = 0;
        while (p[wl] && p[wl] != ' ' && p[wl] != '\n') {
            char c[2] = {p[wl], 0};
            ww += font_width(&st->mono, c);
            wl++;
        }
        if (x + ww > right && x > x0) { x = x0; y += 16; if (y >= FH - 8) break; }
        for (int i = 0; i < wl; i++) {
            char c[2] = {p[i], 0};
            if (x + font_width(&st->mono, c) > right) { x = x0; y += 16; }
            x = font_text(s, &st->mono, x, y, c, rgb(50, 50, 60));
        }
        p += wl;
        if (*p == ' ') {
            x += font_width(&st->mono, " ");
            p++;
        }
    }
}

static void show(struct files *st, struct line *l, int i) {
    st->selected = i;
    if (i < 0) return;
    if (st->list[i].kind == FS_DIR) {
        st->size = 0;
        put_s(l, "files: showing ");
        put_s(l, st->list[i].name);
        put_s(l, "/ (folder)\n");
        flush(l);
        return;
    }
    st->size = fs_read(&st->fs, path_of(st, i));
    long n = st->size < 0 ? 0 : st->size > PREVIEW_MAX ? PREVIEW_MAX : st->size;
    const char *d = fs_data(&st->fs);
    for (long k = 0; k < n; k++) st->preview[k] = d[k] >= 32 || d[k] == '\n' ? d[k] : '.';
    st->preview[n] = 0;
    put_s(l, "files: showing ");
    put_s(l, st->list[i].name);
    put_s(l, " (");
    put_dec(l, (u64)(st->size < 0 ? 0 : st->size));
    put_s(l, " bytes)\n");
    flush(l);
}

static void refresh(struct files *st, struct line *l) {
    long n = fs_list_dir(&st->fs, st->dir, 0, 0);
    if (n > 128) n = 128;
    const struct fs_entry *e = fs_entries(&st->fs);
    st->count = n < 0 ? n : 0;
    for (long i = 0; i < n; i++)
        if (!fs_is_icon(&e[i])) st->list[st->count++] = e[i];   /* how programs look (fs.h) */
    if (st->selected >= st->count) st->selected = st->count > 0 ? 0 : -1;
    put_s(l, "files: listed ");
    put_dec(l, (u64)(st->count < 0 ? 0 : st->count));
    put_s(l, st->count == 1 ? " file\n" : " files\n");
    flush(l);
}

static void open_folder(struct files *st, struct line *l, int i) {
    const char *p = path_of(st, i);
    int n = 0;
    for (; p[n]; n++) st->dir[n] = p[n];
    st->dir[n] = 0;
    st->selected = 0;
    st->top = 0;
    refresh(st, l);
    put_s(l, "files: opened ");
    put_s(l, st->dir);
    put_s(l, "\n");
    flush(l);
    show(st, l, st->count > 0 ? 0 : -1);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct files *st = (struct files *)DATA;
    struct line l = {.n = 0};
    const unsigned char *assets = app_assets();
    st->ui = font_of(assets, F_UI);
    st->bold = font_of(assets, F_BOLD);
    st->small = font_of(assets, F_SMALL);
    st->mono = font_of(assets, F_MONO);
    st->win = app_surface(FW, FH);
    fs_init(&st->fs, SPARE_PAGE);
    st->selected = -1;
    st->top = 0;
    st->dir[0] = 0;
    refresh(st, &l);
    show(st, &l, st->count > 0 ? 0 : -1);
    draw(st);
    u64 opened = app_open(FW, FH, "Files");
    put_s(&l, "files: opened a window");
    put_s(&l, outcome(opened));
    put_s(&l, "\n");
    flush(&l);
    if (opened != OK) exit_task();

    int dirty = 0;
    for (;;) {
        struct event e = app_wait(dirty);
        dirty = 0;
        if (e.kind == EV_CLOSE) {
            put_s(&l, "files: window closed, exiting\n");
            flush(&l);
            exit_task();
        }
        if (e.kind == EV_DOWN) {
            int x = (int)e.a, y = (int)e.b, row = (y - ROW_Y) / ROW_H;
            refresh(st, &l);
            if (x < LIST_W && y >= ROW_Y && row < MAX_SHOWN && st->top + row < st->count) {
                int i = st->top + row;
                if (st->list[i].kind == FS_DIR && i == st->selected) open_folder(st, &l, i);
                else show(st, &l, i);
            } else show(st, &l, st->selected);
        } else if (e.kind == EV_KEY && (e.a == '\r' || e.a == KEY_RIGHT) && st->selected >= 0 &&
                   st->list[st->selected].kind == FS_DIR) {
            open_folder(st, &l, st->selected);
        } else if (e.kind == EV_KEY && e.a == KEY_LEFT && st->dir[0]) {
            int n = 0;
            while (st->dir[n]) n++;
            while (n > 0 && st->dir[n - 1] != '/') n--;
            st->dir[n > 0 ? n - 1 : 0] = 0;
            st->selected = 0;
            st->top = 0;
            refresh(st, &l);
            show(st, &l, st->count > 0 ? 0 : -1);
        } else if (e.kind == EV_KEY && (e.a == KEY_UP || e.a == KEY_DOWN) && st->count > 0) {
            int to = st->selected + (e.a == KEY_DOWN ? 1 : -1);
            if (to < 0 || to >= st->count) continue;
            show(st, &l, to);
        } else if (e.kind == EV_KEY && (e.a == 127 || e.a == 8) && st->selected >= 0) {
            u64 r = fs_delete(&st->fs, path_of(st, st->selected));
            put_s(&l, "files: deleted ");
            put_s(&l, st->list[st->selected].name);
            put_s(&l, r == FS_OK ? " -> ok\n" : " -> refused\n");
            flush(&l);
            refresh(st, &l);
            show(st, &l, st->selected);
        } else continue;
        draw(st);
        dirty = 1;
    }
}
