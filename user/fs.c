/* The file server. It receives on endpoint 1 (capability 4) and keeps up to 48 files of up
   to 16 KiB in its own spare run. See fs.h for the protocol. It never holds a client's
   memory between requests: each request's buffer is mapped, used, unmapped and dropped
   before the reply.

   It alone holds the SD card's first 2048 blocks (capability 5), and keeps the files there
   too: the table of files in blocks 0-7, file i's data from block 8 + 32 i. Every change is
   written through (the data, then the table) before the reply; at boot everything on the
   card is read back. Without a card, files are kept in memory only. */
#define FS_SERVER
#include "fs.h"

#define EP 4
#define SPARE 3
#define DISK 5
#define STORE_PAGE 64          /* the spare run: file i at pages STORE_PAGE + 4 i */
#define BUF_PAGE 2000          /* where a request's buffer is mapped */
#define MAX_FILES 48
#define FILE_PAGES 4
#define TABLE_BLOCKS 8
#define FILE_BLOCKS 32         /* 16 KiB */

/* The table, exactly as it sits in blocks 0-7 of the card: one page of the data run. */
struct file {
    char name[48];
    unsigned size;
    unsigned used;
    unsigned pad[2];
};

struct table {
    char magic[8];
    unsigned version, pad;
    struct file f[MAX_FILES];
};

/* Everything else the server remembers: the data run's first page. */
struct server {
    int on_disk;               /* the card answered at boot */
    int disk_errors;
};

#define TABLE ((struct table *)PAGE(17))
static const char MAGIC[8] = {'L', 'E', 'A', 'N', 'O', 'S', 'F', 'S'};

static char *store(int i) { return (char *)PAGE(STORE_PAGE + FILE_PAGES * i); }

static int block_io(u64 call, u64 block, void *va) {
    return sys(call, DISK, block, (u64)va, 0, 0).status == OK;
}

/* Write file i's data (if i >= 0), then the table, to the card. */
static void save(struct server *sv, int i) {
    if (!sv->on_disk) return;
    int ok = 1;
    if (i >= 0)
        for (unsigned b = 0; b * 512 < TABLE->f[i].size; b++)
            ok &= block_io(SYS_BLOCKWRITE, TABLE_BLOCKS + FILE_BLOCKS * (u64)i + b, store(i) + 512 * b);
    for (u64 b = 0; b < TABLE_BLOCKS; b++) ok &= block_io(SYS_BLOCKWRITE, b, (char *)TABLE + 512 * b);
    if (!ok) sv->disk_errors++;
}

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

static int find(const char *name) {
    for (int i = 0; i < MAX_FILES; i++)
        if (TABLE->f[i].used && same(TABLE->f[i].name, name)) return i;
    return -1;
}

static void copy(char *d, const char *s, u64 n) { for (u64 i = 0; i < n; i++) d[i] = s[i]; }

static u64 put(struct server *sv, const char *name, const char *data, u64 n, u64 *value) {
    if (n > FS_FILE_MAX) return FS_FULL;
    int i = find(name);
    if (i < 0)
        for (int k = 0; k < MAX_FILES; k++) if (!TABLE->f[k].used) { i = k; break; }
    if (i < 0) return FS_FULL;
    struct file *f = &TABLE->f[i];
    int k = 0;
    for (; name[k] && k < FS_NAME_MAX; k++) f->name[k] = name[k];
    for (; k < 48; k++) f->name[k] = 0;
    copy(store(i), data, n);
    f->size = (unsigned)n;
    f->used = 1;
    save(sv, i);
    *value = n;
    return FS_OK;
}

static u64 serve(struct server *sv, u64 op, u64 arg, char *buf, u64 *value) {
    if (op == FS_LIST) {
        struct fs_entry *e = (struct fs_entry *)buf;
        u64 n = 0;
        for (int i = 0; i < MAX_FILES; i++) {
            if (!TABLE->f[i].used) continue;
            int k = 0;
            for (; TABLE->f[i].name[k]; k++) e[n].name[k] = TABLE->f[i].name[k];
            e[n].name[k] = 0;
            e[n].size = TABLE->f[i].size;
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
        int i = find(name);
        if (i < 0) return FS_NOT_FOUND;
        copy(buf + FS_DATA_OFF, store(i), TABLE->f[i].size);
        *value = TABLE->f[i].size;
        return FS_OK;
    }
    if (op == FS_WRITE) return put(sv, name, buf + FS_DATA_OFF, arg, value);
    if (op == FS_DELETE) {
        int i = find(name);
        if (i < 0) return FS_NOT_FOUND;
        TABLE->f[i].used = 0;
        save(sv, -1);
        return FS_OK;
    }
    return FS_BAD;
}

static void fresh_table(void) {
    char *t = (char *)TABLE;
    for (int i = 0; i < 4096; i++) t[i] = 0;
    for (int i = 0; i < 8; i++) TABLE->magic[i] = MAGIC[i];
    TABLE->version = 1;
}

static int count_files(void) {
    int n = 0;
    for (int i = 0; i < MAX_FILES; i++) n += TABLE->f[i].used != 0;
    return n;
}

__attribute__((section(".text.start"))) void _start(void) {
    struct server *sv = (struct server *)DATA;
    struct line l = {.n = 0};
    sys2(SYS_MAP, SPARE, STORE_PAGE);
    sv->disk_errors = 0;

    /* The table from the card, if there is one. */
    sv->on_disk = 1;
    for (u64 b = 0; b < TABLE_BLOCKS && sv->on_disk; b++)
        sv->on_disk = block_io(SYS_BLOCKREAD, b, (char *)TABLE + 512 * b);
    int formatted = 1;
    for (int i = 0; i < 8; i++) formatted &= TABLE->magic[i] == MAGIC[i];
    u64 v;
    if (sv->on_disk && formatted) {
        /* read back every file */
        for (int i = 0; i < MAX_FILES; i++) {
            struct file *f = &TABLE->f[i];
            if (!f->used) continue;
            if (f->size > FS_FILE_MAX) { f->used = 0; continue; }
            for (unsigned b = 0; b * 512 < f->size; b++)
                if (!block_io(SYS_BLOCKREAD, TABLE_BLOCKS + FILE_BLOCKS * (u64)i + b, store(i) + 512 * b))
                    sv->disk_errors++;
        }
        int n = count_files();
        put_s(&l, "fs: ready, ");
        put_dec(&l, (u64)n);
        put_s(&l, n == 1 ? " file on the SD card\n" : " files on the SD card\n");
    } else {
        static const char welcome[] =
            "Welcome to leanos. Files are kept on the SD card, so they are still here after "
            "a restart. Notes saves here, Terminal can ls, cat, write and rm, and Files shows "
            "them all.";
        fresh_table();
        put(sv, "welcome.txt", welcome, sizeof welcome - 1, &v);
        if (sv->on_disk) put_s(&l, "fs: made a new file system on the SD card; ready, 1 file\n");
        else put_s(&l, "fs: no SD card; files are kept in memory only; ready, 1 file\n");
    }
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
                code = serve(sv, op, arg, (char *)PAGE(BUF_PAGE), &value);
                sys2(SYS_UNMAP, BUF_PAGE, FS_BUF_PAGES);
            }
            sys1(SYS_DROP, grant - 1);
        }
        sys(SYS_REPLY, slot - 1, code, value, 0, 0);
    }
}
