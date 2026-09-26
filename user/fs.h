/* The file server's protocol, both sides.

   A client calls endpoint capability 5 with an operation and, every time, a grant of its
   4-page buffer (read-write). In the buffer: a path at byte 0 (up to FS_PATH_MAX bytes and
   a 0: folders separated by '/', from the top of the card), an offset at byte 248 for the
   operations that take one, and data from byte 256. The server maps the buffer, does the
   work, unmaps it and drops the capability before it replies, so it never keeps anyone's
   memory between requests. While it works, the client is waiting for the reply, so the
   buffer cannot change under it. The reply: x1 = status, x2 = a count or size, x3 = more
   (a file's whole size, or an entry's kind).

   Every operation that changes the card is one transaction in the server's journal: after
   a power cut, it has happened completely or not at all (user/fs.c). */
#pragma once
#include "lib.h"

enum {
    FS_LIST = 1,      /* the folder at path: entries from index `arg`; x2 = how many, x3 = all of them */
    FS_READ = 2,      /* the file at path, from the offset: x2 = bytes read, x3 = its size */
    FS_WRITE = 3,     /* the file at path becomes `arg` bytes of data (made if new) */
    FS_DELETE = 4,    /* the file, or empty folder, at path */
    FS_WRITE_AT = 5,  /* `arg` bytes of data at the offset of the file at path (made if new) */
    FS_MKDIR = 6,     /* a new folder at path */
    FS_STAT = 7,      /* x2 = size, x3 = kind */
    FS_RENAME = 8,    /* path becomes the path in the data area, in one step */
    FS_SHARE = 9,     /* give open slot (arg & 255) path, with rights (arg >> 8 & 3), making it a
                         folder first if (arg >> 16 & 1); only Terminal, Files and Apps may;
                         FS_FULL if the slot holds FS_GRANTS_PER_SLOT paths already */
    FS_UNSHARE = 10,  /* take back everything open slot `arg` was given */
    FS_GRANTS = 11,   /* what the caller was given: x2 entries in the data area, each a rights
                         byte then a path and a 0 */
};
enum { FS_OK = 0, FS_NOT_FOUND = 1, FS_FULL = 2, FS_BAD = 3, FS_NO_SERVER = 4, FS_EXISTS = 5,
       FS_NOT_EMPTY = 6, FS_NOT_DIR = 7, FS_IS_DIR = 8, FS_IO = 9, FS_DENIED = 10 };
enum { FS_R = 1, FS_W = 2 };
/* What one open slot may be given (SHARE): its folder and 7 more paths. The file server
   keeps this many records for each of the 6, so no program's can crowd out another's. */
#define FS_GRANTS_PER_SLOT 8
enum { FS_FILE = 1, FS_DIR = 2 };

#define FS_BUF_PAGES 4
#define FS_PATH_MAX 200                    /* bytes, without the terminating 0 */
#define FS_OFFSET_AT 248
#define FS_DATA_OFF 256
#define FS_NAME_MAX 55                     /* one name in a path */
#define FS_CHUNK (FS_BUF_PAGES * 4096 - FS_DATA_OFF)   /* the most one request moves */
#define FS_FILE_MAX FS_CHUNK               /* what fs_read and fs_write move in one go */

/* LIST fills the data area with these, one per entry. */
struct fs_entry {
    char name[56];
    unsigned size;
    unsigned kind;                         /* FS_FILE or FS_DIR */
};
#define FS_LIST_MAX (FS_CHUNK / (int)sizeof(struct fs_entry))

#ifndef FS_SERVER
#define FS_ENDPOINT 5
#define FS_SPARE 3
#define FS_BUF_OFFSET 224   /* the last 4 pages of the spare run */

struct fs_client {
    u64 cap;        /* capability index + 1 of the buffer's capability, 0 until first use */
    char *buf;
};

/* The buffer sits in the spare run, which the caller has mapped at page `spare_page`. */
static inline void fs_init(struct fs_client *c, u64 spare_page) {
    c->cap = 0;
    c->buf = (char *)PAGE(spare_page + FS_BUF_OFFSET);
}

static inline struct res fs_call(struct fs_client *c, u64 op, u64 arg) {
    if (!c->cap) {
        struct res d = sys(SYS_DERIVE, FS_SPARE, R | W, FS_BUF_OFFSET, FS_BUF_PAGES, 0);
        if (d.status != OK) { d.x[1] = FS_NO_SERVER; return d; }
        c->cap = d.x[1] + 1;
    }
    struct res r = sys(SYS_CALL, FS_ENDPOINT, op, arg, 0, c->cap);
    if (r.status != OK) r.x[1] = FS_NO_SERVER;
    return r;
}

static inline void fs_path(struct fs_client *c, const char *name) {
    int i = 0;
    for (; name[i] && i < FS_PATH_MAX; i++) c->buf[i] = name[i];
    c->buf[i] = 0;
}

static inline void fs_offset(struct fs_client *c, u64 off) { *(u64 *)(c->buf + FS_OFFSET_AT) = off; }

/* Read up to FS_CHUNK bytes of `name` from `off` into the buffer's data area. Returns how
   many (0 at the end), or -1; *size (if given) gets the file's whole size. */
static inline long fs_read_at(struct fs_client *c, const char *name, u64 off, u64 *size) {
    fs_path(c, name);
    fs_offset(c, off);
    struct res r = fs_call(c, FS_READ, 0);
    if (r.x[1] != FS_OK) return -1;
    if (size) *size = r.x[3];
    return (long)r.x[2];
}

/* Read the start of `name` (FS_CHUNK bytes at most) into the data area. Returns the size
   read, or -1. */
static inline long fs_read(struct fs_client *c, const char *name) { return fs_read_at(c, name, 0, 0); }

/* Read all of `name` into `dst` (at most `max` bytes). Returns the size, or -1 if it is
   missing or larger than `max`. */
static inline long fs_read_all(struct fs_client *c, const char *name, char *dst, u64 max) {
    u64 size = 0, got = 0;
    for (;;) {
        long n = fs_read_at(c, name, got, &size);
        if (n < 0 || size > max) return -1;
        for (long i = 0; i < n; i++) dst[got + (u64)i] = c->buf[FS_DATA_OFF + i];
        got += (u64)n;
        if (n == 0 || got >= size) return (long)got;
    }
}

/* Write `n` bytes from `data` at `off` in `name` (made if new). Returns the status. */
static inline u64 fs_write_at(struct fs_client *c, const char *name, u64 off, const char *data, u64 n) {
    if (n > FS_CHUNK) return FS_FULL;
    fs_path(c, name);
    fs_offset(c, off);
    for (u64 i = 0; i < n; i++) c->buf[FS_DATA_OFF + i] = data[i];
    return fs_call(c, FS_WRITE_AT, n).x[1];
}

/* `name` becomes the `n` bytes at `data` (n up to FS_CHUNK). Returns the status. */
static inline u64 fs_write(struct fs_client *c, const char *name, const char *data, u64 n) {
    if (n > FS_CHUNK) return FS_FULL;
    fs_path(c, name);
    for (u64 i = 0; i < n; i++) c->buf[FS_DATA_OFF + i] = data[i];
    return fs_call(c, FS_WRITE, n).x[1];
}

static inline u64 fs_delete(struct fs_client *c, const char *name) {
    fs_path(c, name);
    return fs_call(c, FS_DELETE, 0).x[1];
}

static inline u64 fs_mkdir(struct fs_client *c, const char *name) {
    fs_path(c, name);
    return fs_call(c, FS_MKDIR, 0).x[1];
}

static inline u64 fs_rename(struct fs_client *c, const char *from, const char *to) {
    fs_path(c, from);
    int i = 0;
    for (; to[i] && i < FS_PATH_MAX; i++) c->buf[FS_DATA_OFF + i] = to[i];
    c->buf[FS_DATA_OFF + i] = 0;
    return fs_call(c, FS_RENAME, 0).x[1];
}

/* The kind (FS_FILE or FS_DIR) of `name`, 0 if it is missing; *size gets its size. */
static inline u64 fs_stat(struct fs_client *c, const char *name, u64 *size) {
    fs_path(c, name);
    struct res r = fs_call(c, FS_STAT, 0);
    if (r.x[1] != FS_OK) return 0;
    if (size) *size = r.x[2];
    return r.x[3];
}

/* List the folder `dir` ("" for the top) into the buffer, from entry `from`. Returns how
   many entries came, or -1; *total (if given) gets how many the folder has. */
static inline long fs_list_dir(struct fs_client *c, const char *dir, u64 from, u64 *total) {
    fs_path(c, dir);
    struct res r = fs_call(c, FS_LIST, from);
    if (r.x[1] != FS_OK) return -1;
    if (total) *total = r.x[3];
    return (long)r.x[2];
}

/* Give open slot `slot` the path, with rights FS_R and/or FS_W; `folder`: make it a folder
   first. Only Terminal, Files and Apps may. */
static inline u64 fs_share(struct fs_client *c, const char *path, u64 slot, u64 rights, int folder) {
    fs_path(c, path);
    return fs_call(c, FS_SHARE, slot | rights << 8 | (u64)(folder ? 1 : 0) << 16).x[1];
}

static inline u64 fs_unshare(struct fs_client *c, u64 slot) {
    fs_path(c, "");
    return fs_call(c, FS_UNSHARE, slot).x[1];
}

/* What this program was given (a program from the card): how many, each in the data area as
   a rights byte, then the path and a 0. -1 if the file server did not answer. */
static inline long fs_grants(struct fs_client *c) {
    fs_path(c, "");
    struct res r = fs_call(c, FS_GRANTS, 0);
    return r.x[1] == FS_OK ? (long)r.x[2] : -1;
}

/* The top folder's first entries. */
static inline long fs_list(struct fs_client *c) { return fs_list_dir(c, "", 0, 0); }

static inline const struct fs_entry *fs_entries(struct fs_client *c) {
    return (const struct fs_entry *)(c->buf + FS_DATA_OFF);
}
static inline const char *fs_data(struct fs_client *c) { return c->buf + FS_DATA_OFF; }

/* NAME.icon is a program's icon, which the loader adds to program NAME when it runs it
   (elf.h): how the program looks, not a file anyone opens. Files and Terminal's ls leave
   them out of their lists (ls -a shows them); cat, rm and the rest reach them as any file. */
static inline int fs_is_icon(const struct fs_entry *e) {
    int n = 0;
    while (n < (int)sizeof e->name && e->name[n]) n++;
    const char *x = ".icon";
    if (e->kind == FS_DIR || n <= 5) return 0;
    for (int i = 0; i < 5; i++) if (e->name[n - 5 + i] != x[i]) return 0;
    return 1;
}
#endif
