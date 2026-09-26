/* fsfuzz: a fuzzer for the file server (user/fs.c), from an open slot. test/fsfuzz.sh puts
   it on a card of its own under five names, fsfuzz to fsfuzz5, and Terminal gives each its
   own folder, apps/NAME, and nothing else unless it names more. What it does depends on the
   name it was run as (Terminal writes it into the image, beside the icon):

     fsfuzz   1. Fixed requests, each with the one answer the protocol allows: every
                 operation, and numbers that are none; paths that are empty, too long, all
                 '/', with '.' and '..', a 0 inside, bytes outside printable ASCII, the top
                 folder, other programs' folders (apps/fsfuzz2 starts with its own folder's
                 name), paths through files; offsets and lengths at every limit (a cluster,
                 the direct, indirect and double-indirect clusters, 4 GiB, 2^63, 2^64 - 1);
                 no buffer, a buffer of the wrong size or rights, one it has not mapped, a
                 capability that is not memory, grants by plain send; folders deleted with
                 things inside and moved into themselves; a chain of folders 40 deep; a
                 folder of 300 entries.
              2. The regressions, each bug it found, as it found it. The card is filled
                 until the file server says full; then what needs no new cluster must still
                 work (bytes written over, a rename, an empty file deleted, a folder made); a
                 program started meanwhile whose folder cannot be made (fsfuzz5) must leave
                 nothing behind; a cluster freed and given out again in one request must come
                 zeroed. Then the card is emptied.
              3. Random requests in its folder, checked against a model of what every file
                 holds, with requests for what is not its own mixed in.
              Then it writes what its files must hold (expect), for the next boot, where the
              file 40 folders deep must still be there.
     fsfuzz2, fsfuzz3: 3 alone, at the same time, each in its own folder.
     fsfuzz4: given apps as well (run fsfuzz4 apps), fills it to 64 entries, one cluster.
     fsfuzz5: says what it was given (nothing, on a full card).
     fsg*:    (test/grants.sh) says how many paths it was given and how many of them it
              reaches, then waits to be stopped; fsgx ends by itself instead.
     fsfuzz, when its folder has expect (after a restart): every file as expect says.

   Every answer must come, and a refused request must leave the buffer as it was and say
   nothing more (no size, no count); nothing it reads may hold the secret test/fsfuzz.sh keeps
   outside its folder. The seed is in its folder (seed, written by the test: "SEED", or
   "SEED COUNT" for COUNT random requests) and printed, so a run can be replayed. Every line
   it prints starts "fsfuzz: NAME". */
#include "../app.h"
#include "../fs.h"
#include "../elf.h"

#define SECRET "fsfuzz-must-never-read-this"
#define MODEL_OFFSET 64                   /* spare-run pages 64 to 223: the model's files */
#define MF 10                             /* files the model holds */
#define MAXF (64 * 1024UL)                /* bytes each: past the 12 direct clusters */
#define NODES 24
#define PATHN 96                          /* a path under the model's folder, and its 0 */
#define SHOWN 8                           /* wrong answers described, at most */
#define EXPECT_PATHN 128
#define DEEP 40
#define CL 4096UL
#define B_INDIRECT (12 * CL)              /* where the indirect cluster's files start */
#define B_DOUBLE ((12 + 1024) * CL)       /* and the double-indirect's */
#define B_MID ((12 + 2048) * CL)          /* its second cluster of pointers */
#define LONG55 "a123456789b123456789c123456789d123456789e123456789f1234"

enum { MAIN, HELPER, PAD, LATE };
/* Small helpers called from hundreds of places stay calls: the code run holds 48 KiB. */
#define CALL __attribute__((noinline))

struct node {
    char path[PATHN];
    int used, kind, slot;
    u64 size;
};

struct fz {
    struct fs_client fs;
    char name[16], root[24];              /* apps/NAME */
    int mode;
    u64 me, seed, rng, requests, wrong, shown, slowest, t0;
    struct node n[NODES];
    int slot_used[MF];
};

struct expect_entry { char path[EXPECT_PATHN]; u64 size, hash; };

/* ---- small things ---- */

CALL static u64 next(struct fz *f) {
    u64 x = f->rng;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    return f->rng = x;
}

static int same(const char *a, const char *b) {
    while (*a && *a == *b) a++, b++;
    return *a == *b;
}

static int starts(const char *s, const char *p) {
    while (*p && *s == *p) s++, p++;
    return !*p;
}

CALL static void cat(char *d, const char *s) {
    while (*d) d++;
    while (*s) *d++ = *s++;
    *d = 0;
}

CALL static void cpy(char *d, const char *s) { d[0] = 0; cat(d, s); }

CALL static char *buf(struct fz *f) { return f->fs.buf; }
CALL static char *data(struct fz *f) { return f->fs.buf + FS_DATA_OFF; }
static char *content(int slot) { return (char *)PAGE(SPARE_PAGE + MODEL_OFFSET) + (u64)slot * MAXF; }

CALL static u64 fnv(u64 h, const char *p, u64 n) {
    for (u64 i = 0; i < n; i++) { h ^= (unsigned char)p[i]; h *= 1099511628211UL; }
    return h;
}
#define FNV0 14695981039346656037UL

static u64 sum_buf(struct fz *f) { return fnv(FNV0, buf(f), FS_BUF_PAGES * 4096UL); }

static int holds_secret(struct fz *f) {
    const char *d = data(f), *s = SECRET;
    u64 n = slen(s);
    for (u64 i = 0; i + n <= FS_CHUNK; i++)
        if (d[i] == s[0]) {
            u64 k = 1;
            while (k < n && d[i + k] == s[k]) k++;
            if (k == n) return 1;
        }
    return 0;
}

CALL static void say(struct fz *f, const char *what, u64 n, const char *rest) {
    struct line l = {.n = 0};
    put_s(&l, "fsfuzz: ");
    put_s(&l, f->name);
    put_s(&l, " in slot ");
    put_dec(&l, f->me);
    put_s(&l, ": ");
    put_s(&l, what);
    if (rest) {
        put_dec(&l, n);
        put_s(&l, rest);
    }
    put_s(&l, "\n");
    flush(&l);
}

static const char *op_name(u64 op) {
    static const char *const names[] = {"op 0", "list", "read", "write", "delete", "write-at", "mkdir",
                                        "stat", "rename", "share", "unshare", "grants"};
    return op < 12 ? names[op] : "op 12+";
}

/* A wrong answer: counted, and the first few described (the path as printable bytes). */
CALL static void wrong(struct fz *f, const char *what, u64 op, struct res r, u64 want) {
    f->wrong++;
    if (f->shown++ >= SHOWN) return;
    struct line l = {.n = 0};
    put_s(&l, "fsfuzz: ");
    put_s(&l, f->name);
    put_s(&l, ": WRONG: ");
    put_s(&l, what);
    put_s(&l, ", ");
    put_s(&l, op_name(op));
    put_s(&l, " '");
    for (int i = 0; i < 70 && buf(f)[i]; i++) {
        char c[2] = {buf(f)[i] >= 32 && buf(f)[i] < 127 ? buf(f)[i] : '?', 0};
        put_s(&l, c);
    }
    put_s(&l, "': wanted ");
    put_dec(&l, want);
    put_s(&l, ", got ");
    if (r.status != OK) {
        put_s(&l, "no answer, kernel status ");
        put_dec(&l, r.status);
    } else {
        put_dec(&l, r.x[1]);
        put_s(&l, " (");
        put_dec(&l, r.x[2]);
        put_s(&l, ", ");
        put_dec(&l, r.x[3]);
        put_s(&l, ")");
    }
    put_s(&l, "\n");
    flush(&l);
}

/* ---- requests ---- */

CALL static void set_path(struct fz *f, const char *p) {
    int i = 0;
    for (; p[i] && i < FS_PATH_MAX; i++) buf(f)[i] = p[i];
    buf(f)[i] = 0;
}

CALL static void set_to(struct fz *f, const char *p) {
    int i = 0;
    for (; p[i] && i < FS_PATH_MAX; i++) data(f)[i] = p[i];
    data(f)[i] = 0;
}

CALL static void set_off(struct fz *f, u64 off) { *(u64 *)(buf(f) + FS_OFFSET_AT) = off; }

static struct res raw(struct fz *f, u64 op, u64 arg, u64 grant) {
    u64 t0 = ticks();
    struct res r = sys(SYS_CALL, FS_ENDPOINT, op, arg, 0, grant);
    u64 dt = ticks() - t0;
    if (dt > f->slowest) f->slowest = dt;
    f->requests++;
    return r;
}

CALL static u64 code(struct res r) { return r.status == OK ? r.x[1] : 100 + r.status; }

/* A request with its usual buffer whose answer must be `want`. A refusal says nothing more
   and leaves the buffer as it was; an answer never holds the secret. */
static struct res ask(struct fz *f, u64 op, u64 arg, u64 want, const char *what) {
    u64 before = sum_buf(f);
    struct res r = raw(f, op, arg, f->fs.cap);
    u64 got = code(r);
    if (got != want) wrong(f, what, op, r, want);
    else if (got != FS_OK && (r.x[2] || r.x[3] || sum_buf(f) != before))
        wrong(f, "a refusal said more than no", op, r, want);
    if (got == FS_OK && holds_secret(f)) wrong(f, "an answer held another folder's bytes", op, r, want);
    return r;
}

/* The same with a path. */
CALL static struct res at(struct fz *f, const char *path, u64 op, u64 arg, u64 want, const char *what) {
    set_path(f, path);
    return ask(f, op, arg, want, what);
}

CALL static void full_path(struct fz *f, const char *rel, char *out) {
    cpy(out, f->root);
    if (rel[0]) { cat(out, "/"); cat(out, rel); }
}

/* The file at `path` must hold exactly `n` bytes of `want` (all of it, read in pieces). */
static void read_all(struct fz *f, const char *path, const char *want, u64 n, const char *what) {
    u64 off = 0;
    for (;;) {
        set_path(f, path);
        set_off(f, off);
        struct res r = ask(f, FS_READ, 0, FS_OK, what);
        if (code(r) != FS_OK) return;
        if (r.x[3] != n) { wrong(f, what, FS_READ, r, n); return; }
        u64 got = r.x[2];
        u64 expect = n - off < FS_CHUNK ? n - off : FS_CHUNK;
        if (got != expect) { wrong(f, what, FS_READ, r, expect); return; }
        for (u64 i = 0; i < got; i++)
            if (data(f)[i] != want[off + i]) { wrong(f, what, FS_READ, r, off + i); return; }
        off += got;
        if (!got || off >= n) return;
    }
}

static u64 hash_file(struct fz *f, const char *path, u64 *size) {
    u64 off = 0, h = FNV0;
    *size = ~0UL;
    for (;;) {
        set_path(f, path);
        set_off(f, off);
        struct res r = raw(f, FS_READ, 0, f->fs.cap);
        if (code(r) != FS_OK) return 0;
        if (holds_secret(f)) { wrong(f, "an answer held another folder's bytes", FS_READ, r, 0); return 0; }
        *size = r.x[3];
        h = fnv(h, data(f), r.x[2]);
        off += r.x[2];
        if (!r.x[2] || off >= r.x[3]) return h;
    }
}

static void done(struct fz *f, const char *what);

/* ---- 1. fixed requests ---- */

/* Paths that are not the program's own: every request on them is refused, and says nothing. */
static void hostile_paths(struct fz *f, const char **out, int *count) {
    static const char *const common[] = {"", "/", "//////", "apps", "apps/", "/apps", "notes.txt",
                                         "zzsecret.txt", "/zzsecret.txt", "welcome.txt", "apps/../zzsecret.txt",
                                         "apps/fsfuzz", "apps/fsfuzz/seed", "apps/fsfuzz2", "apps/fsfuzz2/m/x",
                                         "apps/fsfuzz3/m", "apps/fsfuz", "apps/fsfuzzz", "apps/fsfuzz2/../fsfuzz/seed"};
    int n = 0;
    for (u64 i = 0; i < sizeof common / sizeof common[0]; i++) {
        const char *p = common[i];
        char norm[32];
        int k = 0;
        for (int j = 0; p[j] && k < 30; j++)
            if (!(p[j] == '/' && (k == 0 || norm[k - 1] == '/'))) norm[k++] = p[j];
        while (k && norm[k - 1] == '/') k--;
        norm[k] = 0;
        /* its own folder, or something in it, is not hostile */
        if (same(norm, f->root) || (starts(norm, f->root) && norm[slen(f->root)] == '/')) continue;
        out[n++] = p;
    }
    *count = n;
}

CALL static void fill_data(struct fz *f, u64 n, u64 salt) {
    for (u64 i = 0; i < n; i++) data(f)[i] = (char)(i * 31 + salt * 7 + (i >> 8));
}

/* Refused: every operation on every path that is not its own. */
static void fixed_hostile(struct fz *f) {
    const char *hostile[24];
    int n;
    hostile_paths(f, hostile, &n);
    static const u64 ops[] = {0, FS_LIST, FS_READ, FS_WRITE, FS_DELETE, FS_WRITE_AT, FS_MKDIR, FS_STAT, FS_RENAME,
                              FS_SHARE, FS_UNSHARE, 12, 13, 255, 1UL << 40, ~0UL};
    char own[64], want[100];
    full_path(f, "own", own);
    set_path(f, own);
    fill_data(f, 100, 1);
    for (int i = 0; i < 100; i++) want[i] = data(f)[i];
    ask(f, FS_WRITE, 100, FS_OK, "its own file");
    for (int i = 0; i < n; i++)
        for (u64 k = 0; k < sizeof ops / sizeof ops[0]; k++) {
            set_path(f, hostile[i]);
            set_off(f, 0);
            set_to(f, own);                            /* a rename would bring it in */
            ask(f, ops[k], k == 3 || k == 5 ? 10 : 11, FS_DENIED, "not its own");
        }
    /* moving its own file out, or another's in */
    for (int i = 0; i < n; i++) {
        set_path(f, own);
        set_to(f, hostile[i]);
        ask(f, FS_RENAME, 0, FS_DENIED, "moved out");
    }
    read_all(f, own, want, 100, "its own file, after all that");
    at(f, own, FS_DELETE, 0, FS_OK, "its own file");
}

/* Operations that do not exist, and those only Terminal, Files and Apps may make. */
static void fixed_ops(struct fz *f) {
    char p[64];
    full_path(f, "t", p);
    at(f, p, 0, 0, FS_BAD, "op 0");
    static const u64 none[] = {12, 13, 99, 255, 1UL << 32, 1UL << 62, ~0UL};
    for (u64 i = 0; i < sizeof none / sizeof none[0]; i++) at(f, p, none[i], 0, FS_DENIED, "no such op");
    at(f, "zzsecret.txt", FS_SHARE, f->me | (FS_R | FS_W) << 8, FS_DENIED, "sharing to itself");
    at(f, f->root, FS_SHARE, 11 | (FS_R | FS_W) << 8 | 1 << 16, FS_DENIED, "sharing to another");
    at(f, "", FS_UNSHARE, f->me, FS_DENIED, "unsharing");
    /* its grants: its folder, read and write, and nothing else */
    set_path(f, "");
    struct res r = ask(f, FS_GRANTS, 0, FS_OK, "grants");
    if (code(r) == FS_OK && (r.x[2] != 1 || data(f)[0] != (FS_R | FS_W) || !same(data(f) + 1, f->root)))
        wrong(f, "grants not just its folder", FS_GRANTS, r, 1);
}

/* Buffers: missing, the wrong size or rights, elsewhere, not mapped, not memory. */
static void fixed_buffers(struct fz *f) {
    set_path(f, f->root);
    struct res r = raw(f, FS_STAT, 0, 0);
    if (code(r) != FS_BAD) wrong(f, "no buffer", FS_STAT, r, FS_BAD);
    static const u64 shape[][3] = {{R | W, FS_BUF_OFFSET + 1, 3}, {R | W, FS_BUF_OFFSET - 1, 5}, {R, FS_BUF_OFFSET, 4},
                                   {W, FS_BUF_OFFSET, 4}, {R | W, FS_BUF_OFFSET, 1}, {R | W, 0, 228}};
    for (u64 i = 0; i < sizeof shape / sizeof shape[0]; i++) {
        struct res d = sys(SYS_DERIVE, FS_SPARE, shape[i][0], shape[i][1], shape[i][2], 0);
        if (d.status != OK) { wrong(f, "derive", 0, d, 0); continue; }
        set_path(f, f->root);
        r = raw(f, FS_STAT, 0, d.x[1] + 1);
        if (code(r) != FS_BAD) wrong(f, "a buffer of the wrong size or rights", FS_STAT, r, FS_BAD);
        sys1(SYS_DROP, d.x[1]);
    }
    /* its code (read and execute) and data (8 pages) runs: not a buffer */
    for (u64 c = 0; c < 2; c++) {
        r = raw(f, FS_STAT, 0, c + 1);
        if (code(r) != FS_BAD) wrong(f, "its code or data run as a buffer", FS_STAT, r, FS_BAD);
    }
    /* four other pages of its own, read-write: a buffer like any other */
    struct res d = sys(SYS_DERIVE, FS_SPARE, R | W, FS_BUF_OFFSET - 8, 4, 0);
    char *other = (char *)PAGE(SPARE_PAGE + FS_BUF_OFFSET - 8);
    cpy(other, f->root);
    r = raw(f, FS_STAT, 0, d.x[1] + 1);
    if (code(r) != FS_OK || r.x[3] != FS_DIR) wrong(f, "a buffer elsewhere", FS_STAT, r, FS_OK);
    sys1(SYS_DROP, d.x[1]);
    /* its stack's four pages: the path at the bottom, where the stack does not reach */
    char *stack = (char *)PAGE(8188);
    cpy(stack, f->root);
    r = raw(f, FS_STAT, 0, 2 + 1);
    if (code(r) != FS_OK || r.x[3] != FS_DIR) wrong(f, "its stack as the buffer", FS_STAT, r, FS_OK);
    /* the buffer not mapped: the capability is what counts */
    set_path(f, f->root);
    sys2(SYS_UNMAP, SPARE_PAGE + FS_BUF_OFFSET, FS_BUF_PAGES);
    r = raw(f, FS_STAT, 0, f->fs.cap);
    sys2(SYS_MAP, SPARE, SPARE_PAGE);
    if (code(r) != FS_OK || r.x[3] != FS_DIR) wrong(f, "a buffer it has not mapped", FS_STAT, r, FS_OK);
    /* endpoints, and capabilities it does not hold: the kernel lets only frames be granted */
    static const u64 notmem[] = {ENDPOINT, FS_ENDPOINT, 60, 63, 1000};
    for (u64 i = 0; i < sizeof notmem / sizeof notmem[0]; i++) {
        r = raw(f, FS_STAT, 0, notmem[i] + 1);
        if (r.status == OK) wrong(f, "a capability that is not memory, granted", FS_STAT, r, 100 + BAD_ARG);
    }
    /* plain sends, which it does not answer, with and without grants: more than its 64
       capabilities. Then it still takes a request. */
    for (int i = 0; i < 70; i++) sys(SYS_SEND, FS_ENDPOINT, i % 3 ? FS_WRITE : 77, i, 0, i % 2 ? f->fs.cap : 0);
    at(f, f->root, FS_STAT, 0, FS_OK, "after plain sends");
}

/* Paths inside its folder that look like more. */
static void fixed_paths(struct fz *f) {
    char p[FS_PATH_MAX + 64], q[FS_PATH_MAX + 64];
    full_path(f, "seedless", p);
    fill_data(f, 77, 3);
    at(f, p, FS_WRITE, 77, FS_OK, "a file");
    char want[77];
    for (int i = 0; i < 77; i++) want[i] = data(f)[i];
    /* the same file, spelled differently */
    cpy(q, "//");
    cat(q, f->root);
    cat(q, "///seedless/");
    read_all(f, q, want, 77, "spelled with more '/'");
    /* '.' and '..' are names like any other: they reach nothing */
    static const char *const nowhere[] = {"/../fsfuzz2/m", "/./seedless", "/..", "/.", "/seedless/..", "/../../zzsecret.txt"};
    for (u64 i = 0; i < sizeof nowhere / sizeof nowhere[0]; i++) {
        cpy(q, f->root);
        cat(q, nowhere[i]);
        at(f, q, FS_READ, 0, FS_NOT_FOUND, "'.' or '..'");
        at(f, q, FS_STAT, 0, FS_NOT_FOUND, "'.' or '..'");
    }
    /* through a file, as if it were a folder */
    cpy(q, p);
    cat(q, "/x");
    for (u64 op = FS_LIST; op <= FS_STAT; op++) {
        set_path(f, q);
        set_off(f, 0);
        fill_data(f, 5, 1);
        ask(f, op, 5, FS_NOT_FOUND, "through a file");
    }
    at(f, p, FS_LIST, 0, FS_NOT_DIR, "a file listed");
    at(f, p, FS_MKDIR, 0, FS_EXISTS, "a folder over a file");
    at(f, f->root, FS_WRITE, 0, FS_IS_DIR, "its folder written");
    at(f, f->root, FS_READ, 0, FS_IS_DIR, "its folder read");
    at(f, f->root, FS_MKDIR, 0, FS_EXISTS, "its folder made");
    at(f, f->root, FS_DELETE, 0, FS_NOT_EMPTY, "its folder deleted");
    /* names: 55 bytes is the most; spaces and '~' are fine; not control bytes or beyond ASCII */
    full_path(f, LONG55, q);
    fill_data(f, 9, 4);
    at(f, q, FS_WRITE, 9, FS_OK, "a 55-byte name");
    at(f, q, FS_STAT, 0, FS_OK, "a 55-byte name");
    at(f, q, FS_DELETE, 0, FS_OK, "a 55-byte name");
    full_path(f, LONG55 "5", q);
    at(f, q, FS_WRITE, 9, FS_NOT_FOUND, "a 56-byte name");
    at(f, q, FS_MKDIR, 0, FS_NOT_FOUND, "a 56-byte name");
    full_path(f, "a b~", q);
    at(f, q, FS_WRITE, 0, FS_OK, "a space and a '~'");
    at(f, q, FS_DELETE, 0, FS_OK, "a space and a '~'");
    static const char bad[] = {1, 9, 31, 127, (char)128, (char)0xc3, (char)0xff};
    for (u64 i = 0; i < sizeof bad; i++) {
        full_path(f, "badX", q);
        q[slen(q) - 1] = bad[i];
        at(f, q, FS_WRITE, 0, FS_NOT_FOUND, "a byte that is not printable ASCII");
        at(f, q, FS_MKDIR, 0, FS_NOT_FOUND, "a byte that is not printable ASCII");
    }
    /* a 0 in the middle: the path ends there */
    full_path(f, "nul", q);
    int k = (int)slen(q);
    const char *tail = "/../../zzsecret.txt";
    for (int i = 0; i <= k; i++) buf(f)[i] = q[i];
    for (int i = 0; tail[i]; i++) buf(f)[k + 1 + i] = tail[i];
    fill_data(f, 3, 5);
    ask(f, FS_WRITE, 3, FS_OK, "a 0 in the middle");
    at(f, q, FS_STAT, 0, FS_OK, "a 0 in the middle");
    at(f, q, FS_DELETE, 0, FS_OK, "a 0 in the middle");
    const char *secret = "zzsecret.txt";
    for (int i = 0; i <= 12; i++) buf(f)[i] = secret[i];
    for (int i = 0; i <= k; i++) buf(f)[13 + i] = q[i];
    ask(f, FS_READ, 0, FS_DENIED, "its own path after a 0");
    /* 200 bytes and a 0 is the longest path; 201 without one is too long, for either path */
    cpy(q, f->root);
    while (slen(q) < FS_PATH_MAX) cat(q, "/n");
    q[FS_PATH_MAX] = 0;
    at(f, q, FS_STAT, 0, FS_NOT_FOUND, "a path of 200 bytes");
    for (int i = 0; i < FS_PATH_MAX + 8; i++) buf(f)[i] = 'l';
    for (u64 op = FS_LIST; op <= FS_STAT; op++) ask(f, op, 0, FS_BAD, "a path with no end");
    set_path(f, p);
    for (int i = 0; i < FS_PATH_MAX + 8; i++) data(f)[i] = 'l';
    ask(f, FS_RENAME, 0, FS_BAD, "a new name with no end");
    cpy(q, "/");
    cat(q, p);
    set_to(f, q);
    set_path(f, p);
    ask(f, FS_RENAME, 0, FS_OK, "renamed onto itself");
    read_all(f, p, want, 77, "renamed onto itself");
    at(f, p, FS_DELETE, 0, FS_OK, "a file");
}

/* Offsets and lengths at every limit. */
static void check_bytes(struct fz *f, const char *path, u64 off, u64 size, u64 lo, u64 hi, u64 salt,
                        const char *what) {
    /* the file must hold the pattern (salt) at [lo, hi), zeros around it, and be `size` long */
    set_path(f, path);
    set_off(f, off);
    for (u64 i = 0; i < FS_CHUNK; i++) data(f)[i] = (char)0xa5;
    struct res r = ask(f, FS_READ, 0, FS_OK, what);
    if (code(r) != FS_OK) return;
    u64 expect = off >= size ? 0 : size - off < FS_CHUNK ? size - off : FS_CHUNK;
    if (r.x[2] != expect || r.x[3] != size) { wrong(f, what, FS_READ, r, expect); return; }
    for (u64 i = 0; i < FS_CHUNK; i++) {
        u64 a = off + i;
        char w = i >= expect ? (char)0xa5 : a >= lo && a < hi ? (char)((a - lo) * 31 + salt * 7 + ((a - lo) >> 8)) : 0;
        if (data(f)[i] != w) { wrong(f, what, FS_READ, r, i); return; }
    }
}

static void fixed_offsets(struct fz *f) {
    char p[64];
    full_path(f, "o", p);
    /* lengths */
    fill_data(f, FS_CHUNK, 0);
    at(f, p, FS_WRITE, FS_CHUNK, FS_OK, "the most one write moves");
    check_bytes(f, p, 0, FS_CHUNK, 0, FS_CHUNK, 0, "the most one write moves");
    static const u64 toolong[] = {FS_CHUNK + 1, 16384, 1UL << 32, 1UL << 62, ~0UL};
    for (u64 i = 0; i < sizeof toolong / sizeof toolong[0]; i++) {
        at(f, p, FS_WRITE, toolong[i], FS_BAD, "a write longer than the buffer");
        set_off(f, 0);
        ask(f, FS_WRITE_AT, toolong[i], FS_BAD, "a write longer than the buffer");
    }
    check_bytes(f, p, 0, FS_CHUNK, 0, FS_CHUNK, 0, "unchanged by a refusal");
    static const u64 len[] = {0, 1, CL - 1, CL, CL + 1};
    for (u64 i = 0; i < sizeof len / sizeof len[0]; i++) {
        fill_data(f, len[i], i);
        at(f, p, FS_WRITE, len[i], FS_OK, "a cluster, give or take a byte");
        check_bytes(f, p, 0, len[i], 0, len[i], i, "a cluster, give or take a byte");
    }
    /* reading at and past the end, and far past it */
    static const u64 roff[] = {CL, CL + 1, CL + 2, 1UL << 32, 1UL << 63, ~0UL, ~0UL - FS_CHUNK};
    for (u64 i = 0; i < sizeof roff / sizeof roff[0]; i++)
        check_bytes(f, p, roff[i], CL + 1, 0, CL + 1, 4, "reading at or past the end");
    /* a write straddling each boundary, as a sparse file: a cluster, the direct clusters'
       end, the indirect's, and the double-indirect's first cluster of pointers */
    static const u64 edge[] = {CL, B_INDIRECT, B_DOUBLE, B_MID};
    for (u64 i = 0; i < sizeof edge / sizeof edge[0]; i++) {
        char q[64];
        full_path(f, "edge", q);
        at(f, q, FS_WRITE, 0, FS_OK, "an empty file");
        u64 lo = edge[i] - (edge[i] < 8192 ? 100 : 5000), hi = lo + FS_CHUNK;
        fill_data(f, FS_CHUNK, 9);
        set_path(f, q);
        set_off(f, lo);
        ask(f, FS_WRITE_AT, FS_CHUNK, FS_OK, "a write straddling a boundary");
        check_bytes(f, q, lo - 300, hi, lo, hi, 9, "straddling a boundary");
        check_bytes(f, q, edge[i] - 1, hi, lo, hi, 9, "at a boundary");
        check_bytes(f, q, edge[i], hi, lo, hi, 9, "at a boundary");
        check_bytes(f, q, hi - 1, hi, lo, hi, 9, "the last byte");
        check_bytes(f, q, 0, hi, lo, hi, 9, "a hole");
        /* then a second write in the hole below, and the first is still there */
        u64 lo2 = lo > FS_CHUNK + 100 ? lo - FS_CHUNK - 100 : 0;
        fill_data(f, 100, 9);
        set_path(f, q);
        set_off(f, lo2);
        ask(f, FS_WRITE_AT, 100, FS_OK, "a write in the hole");
        check_bytes(f, q, lo - 10, hi, lo, hi, 9, "after a write in the hole");
        at(f, q, FS_DELETE, 0, FS_OK, "a sparse file");
    }
    /* 4 GiB is the most a file holds: its last byte, and no further */
    fill_data(f, 1, 11);
    set_path(f, p);
    set_off(f, 0xFFFFFFFEUL);
    ask(f, FS_WRITE_AT, 1, FS_OK, "the last byte a file can hold");
    check_bytes(f, p, 0xFFFFFFFEUL - 7, 0xFFFFFFFFUL, 0xFFFFFFFEUL, 0xFFFFFFFFUL, 11, "4 GiB less one");
    static const u64 beyond[][2] = {{0xFFFFFFFFUL, 1}, {1UL << 32, 0}, {1UL << 32, 1}, {1UL << 63, 1},
                                    {~0UL, 1}, {~0UL, FS_CHUNK}, {~0UL - FS_CHUNK + 1, FS_CHUNK}, {~0UL - 4095, 4096}};
    for (u64 i = 0; i < sizeof beyond / sizeof beyond[0]; i++) {
        set_path(f, p);
        set_off(f, beyond[i][0]);
        fill_data(f, beyond[i][1], 12);
        ask(f, FS_WRITE_AT, beyond[i][1], FS_FULL, "past 4 GiB");
    }
    check_bytes(f, p, 0xFFFFFFFEUL - 7, 0xFFFFFFFFUL, 0xFFFFFFFEUL, 0xFFFFFFFFUL, 11, "unchanged past 4 GiB");
    at(f, p, FS_DELETE, 0, FS_OK, "a 4 GiB file");
    /* a listing from every start */
    char d[64];
    full_path(f, "l", d);
    at(f, d, FS_MKDIR, 0, FS_OK, "a folder");
    for (int i = 0; i < 5; i++) {
        char q[64];
        full_path(f, "l/e", q);
        char s[2] = {(char)('0' + i), 0};
        cat(q, s);
        at(f, q, FS_WRITE, 0, FS_OK, "a file in a folder");
    }
    static const u64 from[] = {0, 4, 5, 6, 1UL << 40, ~0UL};
    for (u64 i = 0; i < sizeof from / sizeof from[0]; i++) {
        struct res r = at(f, d, FS_LIST, from[i], FS_OK, "a listing");
        u64 want = from[i] < 5 ? 5 - from[i] : 0;
        if (code(r) == FS_OK && (r.x[2] != want || r.x[3] != 5)) wrong(f, "a listing's count", FS_LIST, r, want);
    }
    for (int i = 0; i < 5; i++) {
        char q[64];
        full_path(f, "l/e", q);
        char s[2] = {(char)('0' + i), 0};
        cat(q, s);
        at(f, q, FS_DELETE, 0, FS_OK, "a file in a folder");
    }
    at(f, d, FS_DELETE, 0, FS_OK, "a folder");
}

/* Folders: deleted with things inside, moved into themselves, and 40 deep. */
static void fixed_folders(struct fz *f) {
    char d[64], x[64], q[FS_PATH_MAX + 1];
    full_path(f, "d", d);
    full_path(f, "d/f", x);
    at(f, d, FS_MKDIR, 0, FS_OK, "a folder");
    at(f, d, FS_MKDIR, 0, FS_EXISTS, "a folder twice");
    fill_data(f, 10, 2);
    at(f, x, FS_WRITE, 10, FS_OK, "a file in a folder");
    at(f, d, FS_DELETE, 0, FS_NOT_EMPTY, "a folder with a file");
    static const char *const into[] = {"/d/in", "/d/f/g", "/d/"};
    static const u64 into_want[] = {FS_BAD, FS_NOT_FOUND, FS_OK};
    for (int i = 0; i < 3; i++) {
        cpy(q, f->root);
        cat(q, into[i]);
        set_path(f, d);
        set_to(f, q);
        ask(f, FS_RENAME, 0, into_want[i], "a folder moved into itself");
    }
    set_path(f, x);
    set_to(f, d);
    ask(f, FS_RENAME, 0, FS_EXISTS, "a file over a folder");
    set_path(f, d);
    set_to(f, x);
    ask(f, FS_RENAME, 0, FS_BAD, "a folder over its own file");
    cpy(q, f->root);
    cat(q, "/d2");
    set_path(f, d);
    set_to(f, q);
    ask(f, FS_RENAME, 0, FS_OK, "a folder moved");
    cat(q, "/f");
    at(f, q, FS_STAT, 0, FS_OK, "moved with its folder");
    at(f, x, FS_STAT, 0, FS_NOT_FOUND, "moved with its folder");
    set_to(f, x);
    ask(f, FS_RENAME, 0, FS_NOT_FOUND, "into a folder that is gone");
    q[slen(q) - 2] = 0;
    set_path(f, q);
    set_to(f, d);
    ask(f, FS_RENAME, 0, FS_OK, "a folder moved back");
    /* a file replaces a file, in one step */
    char y[64];
    full_path(f, "d/g", y);
    fill_data(f, 20, 6);
    at(f, y, FS_WRITE, 20, FS_OK, "a file");
    set_path(f, x);
    set_to(f, y);
    ask(f, FS_RENAME, 0, FS_OK, "a file over a file");
    fill_data(f, 10, 2);
    char want[10];
    for (int i = 0; i < 10; i++) want[i] = data(f)[i];
    read_all(f, y, want, 10, "the file that replaced it");
    at(f, x, FS_STAT, 0, FS_NOT_FOUND, "the file that moved");
    /* its own folder: not into itself, not out of its reach, not deleted with things in it */
    cpy(q, f->root);
    cat(q, "/sub");
    set_path(f, f->root);
    set_to(f, q);
    ask(f, FS_RENAME, 0, FS_BAD, "its folder into itself");
    set_to(f, f->root);
    ask(f, FS_RENAME, 0, FS_OK, "its folder onto itself");
    cpy(q, f->root);
    cat(q, "9");
    set_to(f, q);
    ask(f, FS_RENAME, 0, FS_DENIED, "its folder out of its reach");
    cpy(q, d);
    cat(q, "/.");
    at(f, q, FS_DELETE, 0, FS_NOT_FOUND, "'.'");
    at(f, y, FS_DELETE, 0, FS_OK, "a file");
    at(f, d, FS_DELETE, 0, FS_OK, "an empty folder");
    at(f, d, FS_DELETE, 0, FS_NOT_FOUND, "a folder already gone");
    /* folders 40 deep, and a file at the bottom: kept for the next boot's check */
    full_path(f, "deep", q);
    at(f, q, FS_MKDIR, 0, FS_OK, "a deep folder");
    for (int i = 0; i < DEEP; i++) {
        cat(q, "/a");
        at(f, q, FS_MKDIR, 0, FS_OK, "a deep folder");
    }
    cat(q, "/leaf");
    fill_data(f, 1000, 13);
    at(f, q, FS_WRITE, 1000, FS_OK, "a file 40 folders deep");
    char leaf[1000];
    for (int i = 0; i < 1000; i++) leaf[i] = data(f)[i];
    read_all(f, q, leaf, 1000, "a file 40 folders deep");
}

/* A folder of 300 entries: five clusters of them, more than one listing holds (252). */
static void big_name(struct fz *f, u64 k, char *out) {
    full_path(f, "big/e000", out);
    u64 n = slen(out);
    out[n - 3] = (char)('0' + k / 100);
    out[n - 2] = (char)('0' + k / 10 % 10);
    out[n - 1] = (char)('0' + k % 10);
}

static void big_list(struct fz *f, u64 want) {
    char d[64];
    full_path(f, "big", d);
    unsigned char seen[40];
    for (int i = 0; i < 40; i++) seen[i] = 0;
    u64 got = 0;
    for (u64 from = 0;;) {
        struct res r = at(f, d, FS_LIST, from, FS_OK, "a big folder, listed");
        if (code(r) != FS_OK) return;
        u64 expect = want - from < (u64)FS_LIST_MAX ? want - from : (u64)FS_LIST_MAX;
        if (r.x[3] != want || r.x[2] != expect) { wrong(f, "a big folder's listing", FS_LIST, r, expect); return; }
        const struct fs_entry *e = fs_entries(&f->fs);
        for (u64 k = 0; k < r.x[2]; k++) {
            const char *nm = e[k].name;
            u64 v = (u64)(nm[1] - '0') * 100 + (u64)(nm[2] - '0') * 10 + (u64)(nm[3] - '0');
            if (nm[0] != 'e' || nm[4] || v >= 320 || (seen[v / 8] & (1 << (v % 8)))) { wrong(f, "a big folder's entry", FS_LIST, r, k); return; }
            seen[v / 8] |= (unsigned char)(1 << (v % 8));
            got++;
        }
        from += r.x[2];
        if (!r.x[2] || from >= want) break;
    }
    if (got != want) wrong(f, "a big folder's entries", FS_LIST, (struct res){.x = {0, 0, got, 0}}, want);
}

static void fixed_bigdir(struct fz *f) {
    char d[64], q[64];
    full_path(f, "big", d);
    at(f, d, FS_MKDIR, 0, FS_OK, "a big folder");
    for (u64 k = 0; k < 300; k++) { big_name(f, k, q); at(f, q, FS_WRITE, 0, FS_OK, "a file in a big folder"); }
    big_list(f, 300);
    for (u64 k = 0; k < 300; k += 2) { big_name(f, k, q); at(f, q, FS_DELETE, 0, FS_OK, "a file in a big folder"); }
    for (u64 k = 300; k < 310; k++) { big_name(f, k, q); at(f, q, FS_WRITE, 0, FS_OK, "a file in a big folder"); }
    big_list(f, 160);
    big_name(f, 299, q);
    fill_data(f, 50, 8);
    at(f, q, FS_WRITE, 50, FS_OK, "the last file in a big folder");
    at(f, d, FS_DELETE, 0, FS_NOT_EMPTY, "a big folder");
    for (u64 k = 1; k < 310; k += k < 299 ? 2 : 1) { big_name(f, k, q); at(f, q, FS_DELETE, 0, FS_OK, "a file in a big folder"); }
    at(f, d, FS_DELETE, 0, FS_OK, "a big folder, emptied");
}

/* Failed changes, timed, then stats of the same paths: a change that fails must cost about
   what the stat does (test/fsfuzz.sh compares). The file server used to read all its
   metadata back from the card after every change that failed (about 129 blocks, 13 to 17
   ms), so a program could slow it for everyone by asking for changes that fail, in a loop.
   `full`: on a full card, a new file, whose inode and entry are taken in memory before the
   write finds no room. Else changes that fail at once: a folder made twice, a file deleted
   that is not there, a folder written, a rename of nothing, a write longer than the buffer. */
#define TIMED 200
static void timed_failures(struct fz *f, int full) {
    char p[64], q[64];
    full_path(f, full ? "r2/new" : "gone", p);
    full_path(f, "gone2", q);
    u64 us[2];
    for (int stat = 0; stat < 2; stat++) {         /* then stats of the same paths, to compare */
        u64 t0 = ticks();
        for (int i = 0; i < TIMED; i++) {
            int k = full ? 5 : i % 5;
            set_path(f, k == 0 || k == 2 ? f->root : p);
            set_off(f, 0);
            set_to(f, q);                                       /* a rename's; a write's byte */
            static const u64 op[] = {FS_MKDIR, FS_DELETE, FS_WRITE, FS_RENAME, FS_WRITE, FS_WRITE};
            static const u64 arg[] = {0, 0, 1, 0, FS_CHUNK + 1, 1};
            static const u64 want[] = {FS_EXISTS, FS_NOT_FOUND, FS_IS_DIR, FS_NOT_FOUND, FS_BAD, FS_FULL};
            u64 o = stat ? FS_STAT : op[k], w = stat ? (k == 0 || k == 2 ? FS_OK : FS_NOT_FOUND) : want[k];
            struct res r = raw(f, o, arg[k], f->fs.cap);       /* not ask: its sums would count */
            if (code(r) != w) wrong(f, "a change that fails", o, r, w);
        }
        us[stat] = (ticks() - t0) * 1000000 / tick_rate();
    }
    struct line l = {.n = 0};
    put_s(&l, "fsfuzz: ");
    put_s(&l, f->name);
    put_s(&l, " in slot ");
    put_dec(&l, f->me);
    put_s(&l, full ? ": failed changes on a full card: 200 in " : ": failed changes: 200 in ");
    put_dec(&l, us[0]);
    put_s(&l, " us, 200 stats of the same paths in ");
    put_dec(&l, us[1]);
    put_s(&l, " us\n");
    flush(&l);
}

/* ---- 2. regressions ---- */

/* The regressions found on a card filled until the file server says full:
   - What needs no new cluster must still work: bytes written over, a rename, an empty file
     deleted, a folder made where its folder has room. Each asked for 4 free clusters and
     was refused as full.
   - A program started then whose folder cannot be made (Terminal's share of apps/fsfuzz5,
     with apps a whole cluster of entries) must leave nothing behind. The file server kept
     the inode it took for the folder, in memory, until a later change wrote it to the card,
     and the next boot repaired it.
   - A cluster freed and given out again in one request must come zeroed. The rewrite below
     frees f's cluster of pointers (read into memory) and its data; with 3 clusters left free
     just before them, its fourth new cluster is that one, which kept f's old pointers, and
     they read back past the end of the file, where it then grows, instead of zeros.
   (A chain of folders 40 deep, in fixed_folders, is the fourth: the check at start walked
   32 folders down, and freed what was deeper as if it were in no folder.) */
static void regress_full(struct fz *f) {
    char r2[64], fk[64], ff[64];
    full_path(f, "r2", r2);
    full_path(f, "r2/f", ff);
    at(f, r2, FS_MKDIR, 0, FS_OK, "a folder for the fill");
    /* four fill files, each with its cluster of pointers already there */
    for (int k = 0; k < 4; k++) {
        full_path(f, "r2/f0", fk);
        fk[slen(fk) - 1] = (char)('0' + k);
        set_path(f, fk);
        set_off(f, B_INDIRECT);
        fill_data(f, 1, 0);
        ask(f, FS_WRITE_AT, 1, FS_OK, "a fill file");
    }
    char ef[64];
    full_path(f, "r2/empty", ef);
    at(f, ef, FS_WRITE, 0, FS_OK, "an empty file");
    set_path(f, ff);
    set_off(f, 1012 * CL);
    fill_data(f, 3 * CL, 1);
    ask(f, FS_WRITE_AT, 3 * CL, FS_OK, "a file in the indirect clusters");
    u64 k = 0, off = 0, bytes = 0, full = 0;
    fill_data(f, FS_CHUNK, 2);
    while (k < 4) {
        if (off + 4 * CL > 1000 * CL) { k++; off = 0; continue; }
        full_path(f, "r2/f0", fk);
        fk[slen(fk) - 1] = (char)('0' + k);
        set_path(f, fk);
        set_off(f, off);
        struct res r = raw(f, FS_WRITE_AT, FS_CHUNK, f->fs.cap);
        if (code(r) == FS_FULL) { full = 1; break; }
        if (code(r) != FS_OK) { wrong(f, "filling the card", FS_WRITE_AT, r, FS_OK); return; }
        off += 4 * CL;
        bytes += FS_CHUNK;
    }
    if (!full) { wrong(f, "the card never filled", FS_WRITE_AT, (struct res){.x = {0}}, FS_FULL); return; }
    /* one cluster at a time, in file 0, past its end: until 3 are left */
    full_path(f, "r2/f0", fk);
    u64 end = k == 0 ? off : 1000 * CL;
    for (;;) {
        set_path(f, fk);
        set_off(f, end);
        struct res r = raw(f, FS_WRITE_AT, 1, f->fs.cap);
        if (code(r) == FS_FULL) break;
        if (code(r) != FS_OK) { wrong(f, "filling the last clusters", FS_WRITE_AT, r, FS_OK); return; }
        end += CL;
        bytes += 1;
    }
    say(f, "the card is full after ", bytes / 1024, " KiB in 4 files");
    /* full: nothing new fits, and what failed changed nothing */
    char nf[64];
    full_path(f, "r2/new", nf);
    fill_data(f, 1, 3);
    at(f, nf, FS_WRITE, 1, FS_FULL, "a new file on a full card");
    at(f, nf, FS_STAT, 0, FS_NOT_FOUND, "a write that did not fit");
    timed_failures(f, 1);
    at(f, nf, FS_STAT, 0, FS_NOT_FOUND, "a write that did not fit, 200 times");
    char want[CL];
    for (u64 i = 0; i < 3 * CL; i += CL) {
        fill_data(f, 3 * CL, 1);
        for (u64 j = 0; j < CL; j++) want[j] = data(f)[i + j];
        set_path(f, ff);
        set_off(f, 1012 * CL + i);
        struct res r = ask(f, FS_READ, 0, FS_OK, "a file on a full card");
        for (u64 j = 0; j < CL && code(r) == FS_OK; j++)
            if (data(f)[j] != want[j]) { wrong(f, "a file on a full card", FS_READ, r, j); break; }
    }
    /* full, but what needs no new cluster still works: bytes written over, a name
       changed, an empty file deleted, a folder made where its folder has room */
    full_path(f, "r2/f1", fk);
    set_path(f, fk);
    set_off(f, 100);
    fill_data(f, 10, 7);
    ask(f, FS_WRITE_AT, 10, FS_OK, "bytes written over, on a full card");
    char g[64];
    full_path(f, "r2/g1", g);
    set_to(f, g);
    ask(f, FS_RENAME, 0, FS_OK, "a rename on a full card");
    set_path(f, g);
    set_to(f, fk);
    ask(f, FS_RENAME, 0, FS_OK, "a rename on a full card");
    at(f, ef, FS_DELETE, 0, FS_OK, "an empty file deleted on a full card");
    full_path(f, "r2/sub", g);
    at(f, g, FS_MKDIR, 0, FS_OK, "a folder made on a full card");
    at(f, g, FS_DELETE, 0, FS_OK, "an empty folder deleted on a full card");
    /* test/fsfuzz.sh starts a program now, whose folder cannot be made (apps has no room
       left: fsfuzz4 filled it). Wait until it runs, three programs from the card, or 30 s. */
    for (u64 t = ticks(); ticks() - t < 30 * tick_rate();) {
        u64 running = 0;
        for (u64 slot = 10; slot < 16; slot++) running += sys1(SYS_BOOTINFO, slot).x[4] == 1;
        if (running >= 3) break;
        sleep_ms(20);
    }
    /* Its folder was not made. Whatever the file server changed in memory for it must be
       gone: new files, whose inodes sit beside any it took, are written to the card. */
    for (int pass = 0; pass < 2; pass++)
        for (int i = 0; i < 16; i++) {
            full_path(f, "r2/i00", g);
            g[slen(g) - 2] = (char)('0' + i / 10);
            g[slen(g) - 1] = (char)('0' + i % 10);
            at(f, g, pass ? FS_DELETE : FS_WRITE, 0, FS_OK, "an empty file on a full card");
        }
    /* the rewrite, then room for the file to grow (the fill files go) */
    fill_data(f, FS_CHUNK, 4);
    at(f, ff, FS_WRITE, FS_CHUNK, FS_OK, "a rewrite on a full card");
    for (int i = 0; i < 4; i++) {
        full_path(f, "r2/f0", fk);
        fk[slen(fk) - 1] = (char)('0' + i);
        at(f, fk, FS_DELETE, 0, FS_OK, "emptying the card");
    }
    set_path(f, ff);
    set_off(f, 4 * CL - 1);
    fill_data(f, 1, 5);
    ask(f, FS_WRITE_AT, 1, FS_OK, "the file grown to its fourth cluster's end");
    set_path(f, ff);
    set_off(f, FS_CHUNK);
    struct res r = ask(f, FS_READ, 0, FS_OK, "a cluster given out again");
    if (code(r) == FS_OK) {
        if (r.x[2] != 4 * CL - FS_CHUNK) wrong(f, "a cluster given out again", FS_READ, r, 4 * CL - FS_CHUNK);
        for (u64 j = 0; j + 1 < r.x[2]; j++)
            if (data(f)[j]) { wrong(f, "a cluster given out again held old bytes", FS_READ, r, j); break; }
    }
    at(f, ff, FS_DELETE, 0, FS_OK, "emptying the card");
    at(f, r2, FS_DELETE, 0, FS_OK, "emptying the card");
    full_path(f, "r2new", nf);
    fill_data(f, FS_CHUNK, 6);
    at(f, nf, FS_WRITE, FS_CHUNK, FS_OK, "a file after emptying");
    at(f, nf, FS_DELETE, 0, FS_OK, "a file after emptying");
}

/* ---- 3. random requests, checked against a model ---- */

static int find(struct fz *f, const char *p) {
    for (int i = 0; i < NODES; i++)
        if (f->n[i].used && same(f->n[i].path, p)) return i;
    return -1;
}

static void parent_of(const char *p, char *out) {
    int last = -1;
    for (int i = 0; p[i]; i++) if (p[i] == '/') last = i;
    int i = 0;
    for (; i < last; i++) out[i] = p[i];
    out[i < 0 ? 0 : i] = 0;
}

static int dir_ok(struct fz *f, const char *p) {
    if (!p[0]) return 1;                               /* the model's own folder */
    int i = find(f, p);
    return i >= 0 && f->n[i].kind == FS_DIR;
}

static int parent_ok(struct fz *f, const char *p) {
    char q[PATHN];
    parent_of(p, q);
    return dir_ok(f, q);
}

static int under(const char *p, const char *d) { return starts(p, d) && p[slen(d)] == '/'; }

static int children(struct fz *f, const char *d) {
    int c = 0;
    char q[PATHN];
    for (int i = 0; i < NODES; i++)
        if (f->n[i].used) {
            parent_of(f->n[i].path, q);
            c += same(q, d);
        }
    return c;
}

static int new_node(struct fz *f, int kind) {
    int slot = -1, i = 0;
    if (kind == FS_FILE) {
        for (int s = 0; s < MF && slot < 0; s++) if (!f->slot_used[s]) slot = s;
        if (slot < 0) return -1;
    }
    for (; i < NODES && f->n[i].used; i++) {}
    return i == NODES ? -1 : i;
}

static void add_node(struct fz *f, int i, const char *p, int kind) {
    struct node *n = &f->n[i];
    cpy(n->path, p);
    n->used = 1;
    n->kind = kind;
    n->size = 0;
    n->slot = -1;
    if (kind == FS_FILE)
        for (int s = 0; s < MF; s++)
            if (!f->slot_used[s]) { f->slot_used[s] = 1; n->slot = s; break; }
}

static void drop_node(struct fz *f, int i) {
    if (f->n[i].slot >= 0) f->slot_used[f->n[i].slot] = 0;
    f->n[i].used = 0;
}

/* The model's paths are under ROOT/m. A request spells one with extra '/' now and then. */
static void model_path(struct fz *f, const char *rel, char *out) {
    u64 v = next(f) % 8;
    cpy(out, v == 0 ? "/" : v == 1 ? "//" : "");
    cat(out, f->root);
    cat(out, v == 2 ? "//m" : "/m");
    if (rel[0]) {
        cat(out, v == 3 ? "///" : "/");
        cat(out, rel);
    }
    if (v == 4) cat(out, "/");
}

static const char *const NAMES[] = {"x", "y", "zz", "a b", "~", ".", "..", "q.txt", LONG55};

static void pick_path(struct fz *f, char *out) {
    u64 k = next(f) % 10;
    if (k < 4) {                                       /* something that is there */
        int i = (int)(next(f) % NODES);
        if (f->n[i].used) { cpy(out, f->n[i].path); return; }
    }
    char par[PATHN];
    par[0] = 0;
    int i = (int)(next(f) % NODES);
    if (f->n[i].used && (k == 9 || f->n[i].kind == FS_DIR)) cpy(par, f->n[i].path);
    const char *name = NAMES[next(f) % (sizeof NAMES / sizeof NAMES[0])];
    if (slen(par) + 1 + slen(name) >= PATHN - 1) par[0] = 0;
    cpy(out, par);
    if (par[0]) cat(out, "/");
    cat(out, name);
}

static void random_data(struct fz *f, u64 n) {
    u64 x = next(f);
    for (u64 i = 0; i < n; i++) {
        if (i % 8 == 0) x = next(f);
        data(f)[i] = (char)(x >> (8 * (i % 8)));
    }
}

static u64 pick_len(struct fz *f) {
    static const u64 len[] = {0, 1, 100, CL - 1, CL, CL + 1, FS_CHUNK};
    return next(f) % 3 ? len[next(f) % (sizeof len / sizeof len[0])] : next(f) % (FS_CHUNK + 1);
}

/* One random request in the model's folder, and the answer checked against the model. */
static void model_op(struct fz *f) {
    char p[PATHN], q[PATHN], full[FS_PATH_MAX + 1], full2[FS_PATH_MAX + 1];
    pick_path(f, p);
    int i = find(f, p), pok = parent_ok(f, p);
    int kind = i >= 0 ? f->n[i].kind : 0;
    struct node *n = i >= 0 ? &f->n[i] : 0;
    u64 pick = next(f) % 100;
    model_path(f, p, full);
    set_path(f, full);
    if (pick < 14) {                                   /* write */
        u64 len = pick_len(f);
        u64 want = !pok ? FS_NOT_FOUND : kind == FS_DIR ? FS_IS_DIR : FS_OK;
        int fresh = -1;
        if (want == FS_OK && i < 0 && (fresh = new_node(f, FS_FILE)) < 0) return;
        random_data(f, len);
        if (code(ask(f, FS_WRITE, len, want, "a write")) != FS_OK || want != FS_OK) return;
        if (fresh >= 0) { add_node(f, fresh, p, FS_FILE); n = &f->n[fresh]; }
        for (u64 k = 0; k < len; k++) content(n->slot)[k] = data(f)[k];
        n->size = len;
    } else if (pick < 34) {                            /* write at */
        u64 len = pick_len(f), size = n && kind == FS_FILE ? n->size : 0;
        static const u64 edge[] = {CL - 1, CL, CL + 1, B_INDIRECT - 1, B_INDIRECT, B_INDIRECT + 1, 2 * CL - 100};
        u64 off = next(f) % 3 ? next(f) % (size + 200) : edge[next(f) % (sizeof edge / sizeof edge[0])];
        if (off + len > MAXF) off = MAXF - len;
        u64 want = !pok ? FS_NOT_FOUND : kind == FS_DIR ? FS_IS_DIR : FS_OK;
        int fresh = -1;
        if (want == FS_OK && i < 0 && (fresh = new_node(f, FS_FILE)) < 0) return;
        random_data(f, len);
        set_off(f, off);
        if (code(ask(f, FS_WRITE_AT, len, want, "a write at an offset")) != FS_OK || want != FS_OK) return;
        if (fresh >= 0) { add_node(f, fresh, p, FS_FILE); n = &f->n[fresh]; }
        char *c = content(n->slot);
        for (u64 k = n->size; k < off; k++) c[k] = 0;
        for (u64 k = 0; k < len; k++) c[off + k] = data(f)[k];
        if (off + len > n->size) n->size = off + len;
    } else if (pick < 54) {                            /* read */
        u64 size = n && kind == FS_FILE ? n->size : 0;
        static const u64 far[] = {1UL << 32, 1UL << 63, ~0UL, MAXF};
        u64 off = next(f) % 8 ? next(f) % (size + 16) : far[next(f) % 4];
        u64 want = !pok || i < 0 ? FS_NOT_FOUND : kind == FS_DIR ? FS_IS_DIR : FS_OK;
        set_off(f, off);
        for (u64 k = 0; k < FS_CHUNK; k++) data(f)[k] = (char)0x5a;
        struct res r = ask(f, FS_READ, 0, want, "a read");
        if (want != FS_OK || code(r) != FS_OK) return;
        u64 count = off >= size ? 0 : size - off < FS_CHUNK ? size - off : FS_CHUNK;
        if (r.x[2] != count || r.x[3] != size) { wrong(f, "a read's count or size", FS_READ, r, count); return; }
        for (u64 k = 0; k < FS_CHUNK; k++) {
            char w = k < count ? content(n->slot)[off + k] : (char)0x5a;
            if (data(f)[k] != w) { wrong(f, "a read's bytes", FS_READ, r, off + k); return; }
        }
    } else if (pick < 62) {                            /* stat */
        u64 want = !pok || i < 0 ? FS_NOT_FOUND : FS_OK;
        struct res r = ask(f, FS_STAT, 0, want, "a stat");
        if (want == FS_OK && code(r) == FS_OK && (r.x[3] != (u64)kind || (kind == FS_FILE && r.x[2] != n->size)))
            wrong(f, "a stat's size or kind", FS_STAT, r, kind == FS_FILE ? n->size : (u64)kind);
    } else if (pick < 70) {                            /* list */
        if (next(f) % 4 == 0) { p[0] = 0; i = -1; kind = FS_DIR; pok = 1; model_path(f, p, full); set_path(f, full); }
        int top = !p[0];
        u64 want = !pok || (i < 0 && !top) ? FS_NOT_FOUND : kind == FS_FILE ? FS_NOT_DIR : FS_OK;
        u64 from = next(f) % 4 ? 0 : next(f) % 4;
        struct res r = ask(f, FS_LIST, from, want, "a listing");
        if (want != FS_OK || code(r) != FS_OK) return;
        u64 total = (u64)children(f, p), count = total > from ? total - from : 0;
        if (r.x[2] != count || r.x[3] != total) { wrong(f, "a listing's count", FS_LIST, r, total); return; }
        const struct fs_entry *e = fs_entries(&f->fs);
        for (u64 k = 0; k < count; k++) {
            char c[PATHN + 60];
            cpy(c, p);
            if (p[0]) cat(c, "/");
            int m = (int)slen(c);
            for (int j = 0; j < 55 && e[k].name[j]; j++) c[m++] = e[k].name[j];
            c[m] = 0;
            int j = m < PATHN ? find(f, c) : -1;
            if (j < 0 || e[k].kind != (unsigned)f->n[j].kind ||
                (f->n[j].kind == FS_FILE && e[k].size != f->n[j].size)) {
                wrong(f, "a listing's entry", FS_LIST, r, k);
                return;
            }
        }
    } else if (pick < 78) {                            /* delete */
        u64 want = !pok || i < 0 ? FS_NOT_FOUND : kind == FS_DIR && children(f, p) ? FS_NOT_EMPTY : FS_OK;
        if (code(ask(f, FS_DELETE, 0, want, "a delete")) == FS_OK && want == FS_OK) drop_node(f, i);
    } else if (pick < 85) {                            /* mkdir */
        u64 want = !pok ? FS_NOT_FOUND : i >= 0 ? FS_EXISTS : FS_OK;
        int fresh = -1;
        if (want == FS_OK && (fresh = new_node(f, FS_DIR)) < 0) return;
        if (code(ask(f, FS_MKDIR, 0, want, "a mkdir")) == FS_OK && want == FS_OK) add_node(f, fresh, p, FS_DIR);
    } else if (pick < 96) {                            /* rename */
        pick_path(f, q);
        int j = find(f, q);
        /* every path it moves must still fit */
        u64 lp = slen(p), lq = slen(q);
        for (int k = 0; k < NODES; k++)
            if (f->n[k].used && under(f->n[k].path, p) && slen(f->n[k].path) - lp + lq >= PATHN) return;
        u64 want = !pok || i < 0 ? FS_NOT_FOUND : !parent_ok(f, q) ? FS_NOT_FOUND
                 : kind == FS_DIR && under(q, p) ? FS_BAD : j == i ? FS_OK
                 : j >= 0 && (f->n[j].kind != FS_FILE || kind != FS_FILE) ? FS_EXISTS : FS_OK;
        model_path(f, q, full2);
        set_path(f, full);
        set_to(f, full2);
        if (code(ask(f, FS_RENAME, 0, want, "a rename")) != FS_OK || want != FS_OK || j == i) return;
        if (j >= 0) drop_node(f, j);
        for (int k = 0; k < NODES; k++)
            if (f->n[k].used && under(f->n[k].path, p)) {
                char t[PATHN];
                cpy(t, q);
                cat(t, f->n[k].path + lp);
                cpy(f->n[k].path, t);
            }
        cpy(n->path, q);
    } else {                                           /* not its own: refused */
        const char *hostile[24];
        int count;
        hostile_paths(f, hostile, &count);
        static const u64 ops[] = {0, FS_LIST, FS_READ, FS_WRITE, FS_DELETE, FS_WRITE_AT, FS_MKDIR, FS_STAT,
                                  FS_RENAME, FS_SHARE, FS_UNSHARE, 12, 1UL << 40};
        u64 op = ops[next(f) % (sizeof ops / sizeof ops[0])];
        const char *h = hostile[next(f) % (u64)count];
        random_data(f, FS_CHUNK);
        set_off(f, next(f));
        if (next(f) % 2) { set_path(f, h); set_to(f, full); }
        else { set_path(f, full); set_to(f, h); op = FS_RENAME; }
        ask(f, op, next(f) % (FS_CHUNK + 1), FS_DENIED, "not its own");
    }
}

/* Every file and folder of the model, read and listed whole. */
static void model_check(struct fz *f) {
    char full[FS_PATH_MAX + 1];
    for (int i = 0; i < NODES; i++) {
        struct node *n = &f->n[i];
        if (!n->used) continue;
        model_path(f, n->path, full);
        if (n->kind == FS_FILE) read_all(f, full, content(n->slot), n->size, "a file, read whole");
        else {
            struct res r = at(f, full, FS_LIST, 0, FS_OK, "a folder, listed");
            if (code(r) == FS_OK && r.x[3] != (u64)children(f, n->path)) wrong(f, "a folder's count", FS_LIST, r, 0);
        }
    }
    model_path(f, "", full);
    struct res r = at(f, full, FS_LIST, 0, FS_OK, "the model's folder, listed");
    if (code(r) == FS_OK && r.x[3] != (u64)children(f, "")) wrong(f, "the model's folder's count", FS_LIST, r, 0);
}

static void random_run(struct fz *f, u64 count) {
    char full[FS_PATH_MAX + 1];
    model_path(f, "", full);
    at(f, full, FS_MKDIR, 0, FS_OK, "the model's folder");
    for (u64 k = 1; k <= count; k++) {
        model_op(f);
        if (k % 128 == 0) model_check(f);
        if (k % 256 == 0) done(f, "random requests so far");
    }
    model_check(f);
}

/* ---- the next boot ---- */

static void save_expect(struct fz *f) {
    struct expect_entry e[NODES + 1];
    u64 m = 0;
    for (int i = 0; i < NODES; i++) {
        if (!f->n[i].used || f->n[i].kind != FS_FILE) continue;
        cpy(e[m].path, f->root);
        cat(e[m].path, "/m/");
        cat(e[m].path, f->n[i].path);
        e[m].size = f->n[i].size;
        e[m].hash = fnv(FNV0, content(f->n[i].slot), f->n[i].size);
        m++;
    }
    full_path(f, "deep", e[m].path);
    for (int i = 0; i < DEEP; i++) cat(e[m].path, "/a");
    cat(e[m].path, "/leaf");
    fill_data(f, 1000, 13);
    e[m].size = 1000;
    e[m].hash = fnv(FNV0, data(f), 1000);
    m++;
    char *d = data(f);
    *(u64 *)d = m;
    for (u64 i = 0; i < sizeof(struct expect_entry) * m; i++) d[8 + i] = ((char *)e)[i];
    char p[64];
    full_path(f, "expect", p);
    at(f, p, FS_WRITE, 8 + sizeof(struct expect_entry) * m, FS_OK, "what the next boot must find");
}

static int check_expect(struct fz *f) {
    char p[64];
    full_path(f, "expect", p);
    set_path(f, p);
    set_off(f, 0);
    struct res r = raw(f, FS_READ, 0, f->fs.cap);
    if (code(r) != FS_OK) return 0;
    struct expect_entry e[NODES + 1];
    u64 m = *(u64 *)data(f);
    if (m > NODES + 1) m = NODES + 1;
    for (u64 i = 0; i < sizeof(struct expect_entry) * m; i++) ((char *)e)[i] = data(f)[8 + i];
    u64 good = 0;
    for (u64 i = 0; i < m; i++) {
        u64 size;
        u64 h = hash_file(f, e[i].path, &size);
        if (size == e[i].size && h == e[i].hash) good++;
        else {
            set_path(f, e[i].path);
            wrong(f, "a file not as it was before the restart", FS_READ, (struct res){.x = {0, 0, size, 0}}, e[i].size);
        }
    }
    say(f, "after a restart, ", good, " files as they were");
    return 1;
}

/* ---- the start ---- */

static void find_name(struct fz *f) {
    const volatile unsigned char *p = (const volatile unsigned char *)PAGE(ICON_IMAGE_PAGE);
    f->name[0] = '?';
    f->name[1] = 0;
    if (*(const volatile unsigned *)p == ICON_MAGIC)
        for (int i = 0; i < 16; i++) f->name[i] = i < 15 ? (char)p[ICON_NAME_AT + i] : 0;
    f->mode = same(f->name, "fsfuzz") ? MAIN : same(f->name, "fsfuzz4") ? PAD
            : same(f->name, "fsfuzz5") || starts(f->name, "fsg") ? LATE : HELPER;
    cpy(f->root, "apps/");
    for (int i = 0; f->name[i] && i < 15; i++) f->root[5 + i] = f->name[i], f->root[6 + i] = 0;
}

static void done(struct fz *f, const char *what) {
    struct line l = {.n = 0};
    put_s(&l, "fsfuzz: ");
    put_s(&l, f->name);
    put_s(&l, " in slot ");
    put_dec(&l, f->me);
    put_s(&l, ": ");
    put_s(&l, what);
    put_s(&l, ": ");
    put_dec(&l, f->requests);
    put_s(&l, " requests, ");
    put_dec(&l, f->wrong);
    put_s(&l, " wrong, slowest answer ");
    put_dec(&l, f->slowest * 1000 / tick_rate());
    put_s(&l, " ms, ");
    put_dec(&l, (ticks() - f->t0) * 1000 / tick_rate());
    put_s(&l, " ms in all\n");
    flush(&l);
}

__attribute__((section(".text.start"))) void _start(void) {
    struct fz *f = (struct fz *)DATA;
    memset(f, 0, sizeof *f);
    app_assets();                        /* the spare run: the model, then the file buffer */
    fs_init(&f->fs, SPARE_PAGE);
    struct res d = sys(SYS_DERIVE, FS_SPARE, R | W, FS_BUF_OFFSET, FS_BUF_PAGES, 0);
    f->fs.cap = d.x[1] + 1;
    f->me = sys0(SYS_WHOAMI).x[1];
    f->t0 = ticks();
    find_name(f);
    /* the seed: from the test, in its folder; else the clock */
    char p[64];
    full_path(f, "seed", p);
    f->seed = 0;
    u64 count = 0;
    if (fs_read(&f->fs, p) > 0) {
        /* "SEED" or "SEED COUNT": how many random requests, for a longer run */
        int i = 0;
        for (; data(f)[i] >= '0' && data(f)[i] <= '9'; i++) f->seed = f->seed * 10 + (u64)(data(f)[i] - '0');
        if (data(f)[i] == ' ')
            for (i++; data(f)[i] >= '0' && data(f)[i] <= '9'; i++) count = count * 10 + (u64)(data(f)[i] - '0');
    }
    if (!f->seed) f->seed = ticks();
    f->rng = f->seed * 2654435761UL + f->me;
    if (!f->rng) f->rng = 1;
    say(f, "seed ", f->seed, "");
    if (f->mode == MAIN && check_expect(f)) {
        done(f, "checked after a restart");
        exit_task();
    }
    if (f->mode == PAD || f->mode == LATE) {
        set_path(f, "");
        struct res r = raw(f, FS_GRANTS, 0, f->fs.cap);
        u64 given = code(r) == FS_OK ? r.x[2] : 0;
        if (f->mode == LATE && starts(f->name, "fsg")) {
            /* each path it was given (a rights byte, the path, a 0), asked about */
            char *got = content(0);                         /* the model's room: not used here */
            for (u64 i = 0; i < FS_CHUNK; i++) got[i] = data(f)[i];
            u64 reach = 0, at = 0;
            for (u64 k = 0; k < given && at < FS_CHUNK; k++) {
                set_path(f, got + at + 1);
                reach += code(raw(f, FS_STAT, 0, f->fs.cap)) == FS_OK;
                at += 2 + slen(got + at + 1);
            }
            struct line l = {.n = 0};
            put_s(&l, "fsfuzz: ");
            put_s(&l, f->name);
            put_s(&l, ": given ");
            put_dec(&l, given);
            put_s(&l, " paths, ");
            put_dec(&l, reach);
            put_s(&l, " reachable\n");
            flush(&l);
            if (same(f->name, "fsgx")) exit_task();
        } else if (f->mode == LATE) say(f, "given ", given, given ? " paths" : " paths (the card was full)");
        else {
            /* given apps too (Terminal: run fsfuzz4 apps): fill apps to 64 entries, one cluster */
            u64 total = 0;
            for (u64 k = 0;; k++) {
                r = at(f, "apps", FS_LIST, 0, FS_OK, "apps, listed");
                total = r.x[3];
                if (code(r) != FS_OK || total >= 64 || k >= 64) break;
                char pad[16] = "apps/pad00";
                pad[8] = (char)('0' + k / 10);
                pad[9] = (char)('0' + k % 10);
                at(f, pad, FS_MKDIR, 0, FS_OK, "a folder in apps");
            }
            say(f, "apps has ", total, " entries");
        }
        for (;;) sleep_ms(1000);
    }
    if (f->mode == MAIN) {
        fixed_ops(f);
        fixed_buffers(f);
        fixed_hostile(f);
        fixed_paths(f);
        fixed_offsets(f);
        fixed_folders(f);
        fixed_bigdir(f);
        timed_failures(f, 0);
        done(f, "fixed requests");
        regress_full(f);
        done(f, "regressions and a full card");
        random_run(f, count ? count : 600);
        save_expect(f);
        done(f, "all done");
    } else {
        random_run(f, count ? count : 400);
        done(f, "all done");
    }
    exit_task();
}
