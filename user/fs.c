/* The file server. It receives on endpoint 1 (capability 4) and keeps up to 48 files of up
   to 16 KiB in its own spare run. See fs.h for the protocol. It never holds a client's
   memory between requests: each request's buffer is mapped, used, unmapped and dropped
   before the reply. */
#define FS_SERVER
#include "fs.h"

#define EP 4
#define SPARE 3
#define STORE_PAGE 64          /* the spare run: file i at pages STORE_PAGE + 4 i */
#define BUF_PAGE 2000          /* where a request's buffer is mapped */
#define MAX_FILES 48
#define FILE_PAGES 4

struct file {
    char name[FS_NAME_MAX + 1];
    unsigned size;
    int used;
};

struct fs {
    struct file f[MAX_FILES];
};

static char *store(int i) { return (char *)PAGE(STORE_PAGE + FILE_PAGES * i); }

static int same(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == *b;
}

/* A name from the buffer: 1 to FS_NAME_MAX printable bytes, no '/'. */
static int valid_name(const char *p) {
    int n = 0;
    for (; n <= FS_NAME_MAX && p[n]; n++)
        if (p[n] < 33 || p[n] > 126 || p[n] == '/') return 0;
    return n > 0 && n <= FS_NAME_MAX;
}

static int find(struct fs *fs, const char *name) {
    for (int i = 0; i < MAX_FILES; i++)
        if (fs->f[i].used && same(fs->f[i].name, name)) return i;
    return -1;
}

static void copy(char *d, const char *s, u64 n) { for (u64 i = 0; i < n; i++) d[i] = s[i]; }

static u64 put(struct fs *fs, const char *name, const char *data, u64 n, u64 *value) {
    if (n > FS_FILE_MAX) return FS_FULL;
    int i = find(fs, name);
    if (i < 0)
        for (int k = 0; k < MAX_FILES; k++) if (!fs->f[k].used) { i = k; break; }
    if (i < 0) return FS_FULL;
    struct file *f = &fs->f[i];
    int k = 0;
    for (; name[k] && k < FS_NAME_MAX; k++) f->name[k] = name[k];
    f->name[k] = 0;
    copy(store(i), data, n);
    f->size = (unsigned)n;
    f->used = 1;
    *value = n;
    return FS_OK;
}

static u64 serve(struct fs *fs, u64 op, u64 arg, char *buf, u64 *value) {
    if (op == FS_LIST) {
        struct fs_entry *e = (struct fs_entry *)buf;
        u64 n = 0;
        for (int i = 0; i < MAX_FILES; i++) {
            if (!fs->f[i].used) continue;
            int k = 0;
            for (; fs->f[i].name[k]; k++) e[n].name[k] = fs->f[i].name[k];
            e[n].name[k] = 0;
            e[n].size = fs->f[i].size;
            n++;
        }
        *value = n;
        return FS_OK;
    }
    char name[FS_NAME_MAX + 1];
    int k = 0;
    for (; k < FS_NAME_MAX && buf[k]; k++) name[k] = buf[k];
    name[k] = 0;
    if (buf[k] != 0 || !valid_name(name)) return FS_BAD;
    if (op == FS_READ) {
        int i = find(fs, name);
        if (i < 0) return FS_NOT_FOUND;
        copy(buf + FS_DATA_OFF, store(i), fs->f[i].size);
        *value = fs->f[i].size;
        return FS_OK;
    }
    if (op == FS_WRITE) return put(fs, name, buf + FS_DATA_OFF, arg, value);
    if (op == FS_DELETE) {
        int i = find(fs, name);
        if (i < 0) return FS_NOT_FOUND;
        fs->f[i].used = 0;
        return FS_OK;
    }
    return FS_BAD;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct fs *fs = (struct fs *)DATA;
    struct line l = {.n = 0};
    sys2(SYS_MAP, SPARE, STORE_PAGE);
    for (int i = 0; i < MAX_FILES; i++) fs->f[i].used = 0;
    static const char welcome[] =
        "Welcome to leanos. Files live in the file server's memory until the Pi restarts. "
        "Notes saves here, Terminal can ls, cat, write and rm, and Files shows them all.";
    u64 v;
    put(fs, "welcome.txt", welcome, sizeof welcome - 1, &v);
    put_s(&l, "fs: ready, 1 file\n");
    flush(&l);

    for (;;) {
        struct res r = sys1(SYS_RECV, EP);
        u64 op = r.x[2], arg = r.x[3], grant = r.x[5], slot = r.x[6];
        if (!slot) continue;              /* a plain send: nobody to answer */
        u64 code = FS_BAD, value = 0;
        if (grant) {
            struct res info = sys1(SYS_CAPINFO, grant - 1);
            if (info.x[2] == 0 && info.x[3] == FS_BUF_PAGES && (info.x[1] & (R | W)) == (R | W) &&
                sys2(SYS_MAP, grant - 1, BUF_PAGE).status == OK) {
                code = serve(fs, op, arg, (char *)PAGE(BUF_PAGE), &value);
                sys2(SYS_UNMAP, BUF_PAGE, FS_BUF_PAGES);
            }
            sys1(SYS_DROP, grant - 1);
        }
        sys(SYS_REPLY, slot - 1, code, value, 0, 0);
    }
}
