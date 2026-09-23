/* The file server's protocol, both sides.

   A client calls endpoint capability 5 with an operation and, every time, a grant of its
   4-page buffer (read-write): the path at the start, data from byte 64. The server maps the
   buffer, does the work, unmaps it and drops the capability before it replies, so it never
   keeps anyone's memory between requests. While it works, the client is waiting for the
   reply, so the buffer cannot change under it. The reply: x1 = status, x2 = a count or size.

   Files live in the file server's own memory until the Pi restarts. */
#pragma once
#include "lib.h"

enum { FS_LIST = 1, FS_READ = 2, FS_WRITE = 3, FS_DELETE = 4 };
enum { FS_OK = 0, FS_NOT_FOUND = 1, FS_FULL = 2, FS_BAD = 3, FS_NO_SERVER = 4 };

#define FS_BUF_PAGES 4
#define FS_DATA_OFF 64
#define FS_NAME_MAX 40                     /* bytes, without the terminating 0 */
#define FS_FILE_MAX (FS_BUF_PAGES * 4096 - FS_DATA_OFF)

/* LIST fills the buffer with these, one per file. */
struct fs_entry {
    char name[48];
    unsigned size;
    unsigned pad[3];
};

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
    for (; name[i] && i < FS_NAME_MAX; i++) c->buf[i] = name[i];
    c->buf[i] = 0;
}

/* Read `name` into the buffer's data area. Returns the size, or -1. */
static inline long fs_read(struct fs_client *c, const char *name) {
    fs_path(c, name);
    struct res r = fs_call(c, FS_READ, 0);
    return r.x[1] == FS_OK ? (long)r.x[2] : -1;
}

/* Write `n` bytes from `data` to `name`. Returns the status. */
static inline u64 fs_write(struct fs_client *c, const char *name, const char *data, u64 n) {
    if (n > FS_FILE_MAX) return FS_FULL;
    fs_path(c, name);
    for (u64 i = 0; i < n; i++) c->buf[FS_DATA_OFF + i] = data[i];
    return fs_call(c, FS_WRITE, n).x[1];
}

static inline u64 fs_delete(struct fs_client *c, const char *name) {
    fs_path(c, name);
    return fs_call(c, FS_DELETE, 0).x[1];
}

/* List the files into the buffer. Returns how many, or -1. */
static inline long fs_list(struct fs_client *c) {
    struct res r = fs_call(c, FS_LIST, 0);
    return r.x[1] == FS_OK ? (long)r.x[2] : -1;
}

static inline const struct fs_entry *fs_entries(struct fs_client *c) { return (const struct fs_entry *)c->buf; }
static inline const char *fs_data(struct fs_client *c) { return c->buf + FS_DATA_OFF; }
#endif
