/* The file server. It receives on endpoint 1 (capability 4); see fs.h for the protocol.
   It never holds a client's memory between requests: each request's buffer is mapped,
   used, unmapped and dropped before the reply.

   It alone holds the SD card's data partition (capability 5, blocks of 512 bytes), and
   keeps a real file system there: folders, files of any size up to the card's, and a
   journal, so a power cut cannot leave a change half done.

   On the card (tools/mksd.py writes the same thing):
     block 0            the superblock: where everything is
     journal            a header (sequence, how many blocks, a checksum, where each goes),
                        then the blocks of the one transaction being written
     bitmap             one bit per 4 KiB cluster: in use or free
     inodes             64 bytes each: kind, size, 12 direct clusters, one indirect
                        cluster (1024 more), one double-indirect (a million more)
     data               clusters of 8 blocks; a folder is a file of 64-byte entries

   Every request that changes anything is one transaction: the server changes its copies
   of the metadata and the clusters it touches in memory, then writes every changed block
   to the journal, then the journal's header with a checksum over all of it (the commit),
   then each block to its place, then clears the header. At start, a committed transaction
   whose checksum matches is written to its place again; one whose checksum does not match
   never committed, and nothing of it had reached its place. So each change is all or
   nothing: LeanOS/Journal.lean proves it (`crash_atomic`) for a model of exactly this
   protocol, cut after any number of block writes. Then the whole tree is checked: every cluster in use belongs to exactly one
   file, every file is in a folder; anything else is repaired and said.

   Without a card, the same file system lives in memory (smaller), until the Pi restarts. */
#define FS_SERVER
#include "fs.h"

#define EP 4
#define SPARE 3
#define DISK 5
#define BUF_PAGE 2000                 /* where a request's buffer is mapped */

/* The spare run, mapped at page 64: */
#define BITMAP_PAGE 64                /* 4 pages: 131072 clusters, 512 MiB */
#define INODE_PAGE 68                 /* 16 pages: 1024 inodes */
#define STAGE_PAGE 84                 /* 16 pages: clusters a request reads or changes */
#define JHEAD_PAGE 100                /* the journal header */
#define RAMDISK_PAGE 101              /* without a card: the disk, 128 pages */
#define SHADOW_PAGE 229               /* 20 pages: the bitmap and inodes as the card has them */
#define STAGES 16
#define MAX_CLUSTERS (4 * 4096 * 8)
#define MAX_INODES 1024
#define RAM_BLOCKS 1024
#define CARD_MAX_BLOCKS (1UL << 20)   /* what the kernel's block capability covers: 512 MiB */
#define CLUSTER 4096
#define PER_CLUSTER 8                 /* blocks */
#define PTRS 1024                     /* cluster numbers in a cluster */
#define NDIRECT 12
#define JMAX 124                      /* blocks in one transaction */

static const char MAGIC[8] = {'L', 'E', 'A', 'N', 'O', 'S', 'F', '2'};
static const char JMAGIC[4] = {'L', 'J', 'N', 'L'};

struct super {
    char magic[8];
    unsigned version, total, journal_start, journal_blocks, bitmap_start, bitmap_blocks,
        inode_start, inode_count, data_start, clusters;
};

struct inode {
    unsigned short kind, pad;         /* 0 free, FS_FILE, FS_DIR */
    unsigned size;
    unsigned direct[NDIRECT];
    unsigned indirect, dindirect;
};

struct dirent {
    unsigned ino, kind;
    char name[56];
};

struct jhead {
    char magic[4];
    unsigned seq, n, sum;
    unsigned target[JMAX];
};

/* What a program from the card (open slot 10 to 15) was given: a path, and everything
   under it if it is a folder, with read and/or write. Terminal, Files and Apps give; the
   kernel's badges say who asks (`file_server_knows_the_sender`), so a program reaches
   nothing else. Given paths are kept normalized: no leading, trailing or doubled '/'. */
#define MAX_GRANTS (6 * FS_GRANTS_PER_SLOT)    /* FS_GRANTS_PER_SLOT for each open slot */
struct grant { unsigned char slot, rights; char path[FS_PATH_MAX + 1]; };

/* Clusters in memory: a small cache of STAGES pages. A changed cluster stays until the
   request commits; an unchanged one can be dropped when another needs its page. */
struct stage { unsigned cl; int dirty, live; };

struct server {
    int on_disk, ram, errors, repaired;
    struct super sb;
    unsigned free_clusters, seq, rover;
    struct stage st[STAGES];
    int nst;
    unsigned char ino_dirty[MAX_INODES / 8];     /* inode-table blocks changed */
    unsigned char map_dirty[32];                 /* bitmap blocks changed */
    unsigned tx_target[JMAX];
    const char *tx_src[JMAX];
    int ntx, overflow;
    int shadow_ok;                               /* the shadow is the card's metadata, exactly */
    unsigned char seen_ino[MAX_INODES / 8];      /* the check: inodes found in the tree */
    struct grant grants[MAX_GRANTS];
    unsigned char refusals[16];                  /* per open slot, for the log */
};

/* A program's image is read-only: everything it changes lives in its data pages. */
#define S ((struct server *)DATA)
#define BITMAP ((unsigned char *)PAGE(BITMAP_PAGE))
#define INODES ((struct inode *)PAGE(INODE_PAGE))
#define JHEAD ((struct jhead *)PAGE(JHEAD_PAGE))
#define SHADOW ((char *)PAGE(SHADOW_PAGE))
static char *stage_page(int i) { return (char *)PAGE(STAGE_PAGE + (u64)i); }
static char *ram_block(u64 b) { return (char *)PAGE(RAMDISK_PAGE) + 512 * b; }

static void copy(char *d, const char *s, u64 n) { for (u64 i = 0; i < n; i++) d[i] = s[i]; }
static void zero(char *d, u64 n) { for (u64 i = 0; i < n; i++) d[i] = 0; }

/* ---- blocks ---- */

static int bread(u64 b, void *dst) {
    if (S->ram) {
        if (b >= RAM_BLOCKS) return 0;
        copy(dst, ram_block(b), 512);
        return 1;
    }
    return sys(SYS_BLOCKREAD, DISK, b, (u64)dst, 0, 0).status == OK;
}

static int bwrite(u64 b, const void *src) {
    if (S->ram) {
        if (b >= RAM_BLOCKS) return 0;
        copy(ram_block(b), src, 512);
        return 1;
    }
    return sys(SYS_BLOCKWRITE, DISK, b, (u64)src, 0, 0).status == OK;
}

static u64 cluster_block(unsigned cl) { return S->sb.data_start + (u64)cl * PER_CLUSTER; }

/* ---- the metadata, and its shadow ----

   The bitmap and the inode table are kept in memory whole (BITMAP, INODES), and changed
   there by a request before its commit. The shadow is a second copy, of exactly what the
   card holds in those blocks: it is filled when they are read from the card, and a block of
   it changes only when that block's write to its place on the card went through (commit,
   format). A write that fails leaves the card's block unknown, so the shadow is marked
   stale until the next read of the whole metadata from the card. */

/* Where block `b` of the card's metadata (the bitmap's blocks, then the inodes') is in the
   copy at `base` (BITMAP, with INODES after it, or SHADOW); 0 if `b` is not metadata. */
static char *meta_at(char *base, u64 b) {
    const struct super *sb = &S->sb;
    if (b >= sb->bitmap_start && b < (u64)sb->bitmap_start + sb->bitmap_blocks)
        return base + 512 * (b - sb->bitmap_start);
    if (b >= sb->inode_start && b < (u64)sb->inode_start + sb->inode_count / 8)
        return base + 4 * 4096 + 512 * (b - sb->inode_start);
    return 0;
}

/* Every block of metadata from one copy to the other, 8 bytes at a time. */
__attribute__((no_builtin)) static void meta_copy(char *to, const char *from) {
    for (unsigned b = 0; b < S->sb.bitmap_blocks + S->sb.inode_count / 8; b++) {
        u64 at = b < S->sb.bitmap_blocks ? 512 * (u64)b : 4 * 4096 + 512 * (u64)(b - S->sb.bitmap_blocks);
        u64 *d = (u64 *)(to + at);
        const u64 *s = (const u64 *)(from + at);
        for (int i = 0; i < 64; i++) d[i] = s[i];
    }
}

/* ---- the transaction ---- */

static void tx_add(unsigned target, const char *src) {
    for (int i = 0; i < S->ntx; i++)
        if (S->tx_target[i] == target) { S->tx_src[i] = src; return; }
    unsigned cap = S->sb.journal_blocks - 1 < JMAX ? S->sb.journal_blocks - 1 : JMAX;
    if ((unsigned)S->ntx >= cap) { S->overflow = 1; return; }
    S->tx_target[S->ntx] = target;
    S->tx_src[S->ntx] = src;
    S->ntx++;
}

static unsigned fnv(unsigned h, const char *p, u64 n) {
    for (u64 i = 0; i < n; i++) { h ^= (unsigned char)p[i]; h *= 16777619u; }
    return h;
}

static unsigned tx_sum(const struct jhead *h, const char *const *src, int from_journal) {
    unsigned s = fnv(2166136261u, (const char *)&h->seq, 8);
    s = fnv(s, (const char *)h->target, 4 * (u64)h->n);
    if (!from_journal)
        for (unsigned i = 0; i < h->n; i++) s = fnv(s, src[i], 512);
    return s;
}

/* Write the transaction: journal, commit, home, clear. 1 if every write went through. */
static int commit(void) {
    /* what changed in the metadata */
    for (unsigned b = 0; b < S->sb.bitmap_blocks && b < 32 * 8; b++)
        if (S->map_dirty[b / 8] & (1 << (b % 8))) tx_add(S->sb.bitmap_start + b, (const char *)BITMAP + 512 * b);
    for (unsigned b = 0; b < S->sb.inode_count / 8; b++)
        if (S->ino_dirty[b / 8] & (1 << (b % 8))) tx_add(S->sb.inode_start + b, (const char *)INODES + 512 * b);
    for (int i = 0; i < STAGES; i++)
        if (S->st[i].live && S->st[i].dirty)
            for (unsigned k = 0; k < PER_CLUSTER; k++)
                tx_add((unsigned)cluster_block(S->st[i].cl) + k, stage_page(i) + 512 * k);
    if (S->overflow) return 0;
    if (S->ntx == 0) return 1;
    struct jhead *h = JHEAD;
    zero((char *)h, 512);
    copy(h->magic, JMAGIC, 4);
    h->seq = ++S->seq;
    h->n = (unsigned)S->ntx;
    for (int i = 0; i < S->ntx; i++) h->target[i] = S->tx_target[i];
    int ok = 1;
    for (int i = 0; i < S->ntx; i++) ok &= bwrite(S->sb.journal_start + 1 + (u64)i, S->tx_src[i]);
    h->sum = tx_sum(h, S->tx_src, 0);
    if (ok) ok &= bwrite(S->sb.journal_start, h);             /* the commit */
    if (ok)
        for (int i = 0; i < S->ntx; i++) {
            int w = bwrite(S->tx_target[i], S->tx_src[i]);
            char *sh = meta_at(SHADOW, S->tx_target[i]);
            if (sh && w) copy(sh, S->tx_src[i], 512);         /* the card has it now */
            else if (sh) S->shadow_ok = 0;                    /* the card has who knows what */
            ok &= w;
        }
    h->n = 0;
    if (ok) ok &= bwrite(S->sb.journal_start, h);             /* done */
    if (!ok) S->errors++;
    return ok;
}

/* At start: a committed transaction goes to its place (again); anything else is dropped. */
static int replay(struct line *l) {
    struct jhead *h = JHEAD;
    if (!bread(S->sb.journal_start, h)) return 0;
    S->seq = h->seq;
    int valid = 1;
    for (int i = 0; i < 4; i++) valid &= h->magic[i] == JMAGIC[i];
    if (!valid || h->n == 0 || h->n > JMAX || h->n >= S->sb.journal_blocks) return 1;
    char *blk = stage_page(0);
    unsigned s = tx_sum(h, 0, 1);
    for (unsigned i = 0; i < h->n; i++) {
        if (!bread(S->sb.journal_start + 1 + i, blk)) return 0;
        s = fnv(s, blk, 512);
    }
    unsigned n = h->n;
    if (s == h->sum) {
        for (unsigned i = 0; i < n; i++) {
            bread(S->sb.journal_start + 1 + i, blk);
            if (h->target[i] < S->sb.total) bwrite(h->target[i], blk);
        }
        put_s(l, "fs: finished a change a power cut interrupted (");
        put_dec(l, n);
        put_s(l, " blocks)\n");
    } else put_s(l, "fs: dropped a change a power cut interrupted before it was complete\n");
    flush(l);
    h->n = 0;
    bwrite(S->sb.journal_start, h);
    return 1;
}

/* ---- clusters ---- */

static void op_begin(void) {
    for (int i = 0; i < STAGES; i++) S->st[i].live = 0;
    S->ntx = 0;
    S->overflow = 0;
    zero((char *)S->ino_dirty, sizeof S->ino_dirty);
    zero((char *)S->map_dirty, sizeof S->map_dirty);
}

/* Cluster `cl` in memory: read from the card if `load`, else zeros. 0 if every page holds a
   changed cluster (a request changes at most a handful). */
static char *cluster(unsigned cl, int load) {
    int slot = -1;
    for (int i = 0; i < STAGES; i++) if (S->st[i].live && S->st[i].cl == cl) return stage_page(i);
    for (int i = 0; i < STAGES && slot < 0; i++) if (!S->st[i].live) slot = i;
    for (int i = 0; i < STAGES && slot < 0; i++) if (!S->st[i].dirty) slot = i;
    if (slot < 0) { S->overflow = 1; return 0; }
    S->st[slot].cl = cl;
    S->st[slot].dirty = 0;
    S->st[slot].live = 1;
    char *p = stage_page(slot);
    if (load) {
        for (unsigned k = 0; k < PER_CLUSTER; k++)
            if (!bread(cluster_block(cl) + k, p + 512 * k)) { S->errors++; zero(p, CLUSTER); break; }
    } else zero(p, CLUSTER);
    return p;
}

/* Mark cluster `cl` changed: it stays in memory and is written at the commit. */
static void dirty(unsigned cl) {
    for (int i = 0; i < STAGES; i++) if (S->st[i].live && S->st[i].cl == cl) S->st[i].dirty = 1;
}

static int used(unsigned cl) { return BITMAP[cl / 8] & (1 << (cl % 8)); }

static void set_used(unsigned cl, int on) {
    if (on) BITMAP[cl / 8] |= (unsigned char)(1 << (cl % 8));
    else BITMAP[cl / 8] &= (unsigned char)~(1 << (cl % 8));
    unsigned b = cl / 4096;
    S->map_dirty[b / 8] |= (unsigned char)(1 << (b % 8));
}

/* A new, zeroed cluster, or 0 if the card is full. It may be one this request freed and
   still has in memory (a file's pointers, read while it was emptied): zeroed all the same. */
static unsigned alloc_cluster(void) {
    for (unsigned k = 0; k < S->sb.clusters; k++) {
        unsigned cl = (S->rover + k) % S->sb.clusters;
        if (cl == 0 || used(cl)) continue;
        set_used(cl, 1);
        S->free_clusters--;
        S->rover = cl + 1;
        char *p = cluster(cl, 0);
        if (!p) return 0;
        zero(p, CLUSTER);
        dirty(cl);
        return cl;
    }
    return 0;
}

static void free_cluster(unsigned cl) {
    if (cl == 0 || cl >= S->sb.clusters || !used(cl)) return;
    set_used(cl, 0);
    S->free_clusters++;
}

static void inode_dirty(unsigned ino) {
    unsigned b = ino / 8;
    S->ino_dirty[b / 8] |= (unsigned char)(1 << (b % 8));
}

/* The cluster holding block `idx` of a file (4 KiB each); allocated if `make`, else 0 for a
   hole. */
static unsigned bmap(unsigned ino, unsigned idx, int make) {
    struct inode *in = &INODES[ino];
    if (idx < NDIRECT) {
        if (!in->direct[idx] && make) { in->direct[idx] = alloc_cluster(); inode_dirty(ino); }
        return in->direct[idx];
    }
    idx -= NDIRECT;
    unsigned holder;
    if (idx < PTRS) {
        if (!in->indirect) {
            if (!make) return 0;
            if (!(in->indirect = alloc_cluster())) return 0;
            inode_dirty(ino);
        }
        holder = in->indirect;
    } else {
        idx -= PTRS;
        if (idx >= PTRS * PTRS) return 0;
        if (!in->dindirect) {
            if (!make) return 0;
            if (!(in->dindirect = alloc_cluster())) return 0;
            inode_dirty(ino);
        }
        unsigned *outer = (unsigned *)cluster(in->dindirect, 1);
        if (!outer) return 0;
        unsigned mid = outer[idx / PTRS];
        if (!mid) {
            if (!make) return 0;
            dirty(in->dindirect);              /* kept in memory while a cluster is found */
            if (!(mid = alloc_cluster())) return 0;
            outer = (unsigned *)cluster(in->dindirect, 1);
            outer[idx / PTRS] = mid;
        }
        holder = mid;
        idx %= PTRS;
    }
    unsigned *p = (unsigned *)cluster(holder, 1);
    if (!p) return 0;
    if (!p[idx] && make) {
        dirty(holder);
        unsigned cl = alloc_cluster();
        p = (unsigned *)cluster(holder, 1);
        p[idx] = cl;
    }
    return p[idx];
}

/* Clusters a write of `n` bytes at `off` may need: those the file does not have yet, and 3
   more for pointer clusters if it needs any. Bytes written over need none, so a full card
   still takes them (a folder's entry changed in place: a rename, a delete). */
static unsigned clusters_needed(unsigned ino, u64 off, u64 n) {
    unsigned need = 0;
    for (u64 idx = off / CLUSTER; n && idx <= (off + n - 1) / CLUSTER; idx++) need += !bmap(ino, (unsigned)idx, 0);
    return need ? need + 3 : 0;
}

/* Free every cluster of the file, and make it empty. The pointer clusters are read one
   request at a time, so a very large file is freed across a few staging reuses. */
static void truncate_all(unsigned ino) {
    struct inode *in = &INODES[ino];
    for (int i = 0; i < NDIRECT; i++) { free_cluster(in->direct[i]); in->direct[i] = 0; }
    if (in->indirect) {
        unsigned *p = (unsigned *)cluster(in->indirect, 1);
        if (p) for (int i = 0; i < PTRS; i++) free_cluster(p[i]);
        free_cluster(in->indirect);
        in->indirect = 0;
    }
    if (in->dindirect) {
        unsigned outer[PTRS];
        unsigned *o = (unsigned *)cluster(in->dindirect, 1);
        for (int j = 0; j < PTRS; j++) outer[j] = o ? o[j] : 0;
        for (int j = 0; j < PTRS; j++) {
            if (!outer[j]) continue;
            unsigned *p = (unsigned *)cluster(outer[j], 1);
            if (p) for (int i = 0; i < PTRS; i++) free_cluster(p[i]);
            free_cluster(outer[j]);
        }
        free_cluster(in->dindirect);
        in->dindirect = 0;
    }
    in->size = 0;
    inode_dirty(ino);
}

/* ---- files ---- */

static u64 file_read(unsigned ino, u64 off, char *dst, u64 max) {
    struct inode *in = &INODES[ino];
    if (off >= in->size) return 0;
    u64 n = in->size - off < max ? in->size - off : max, done = 0;
    while (done < n) {
        u64 at = off + done, in_cl = at % CLUSTER, take = CLUSTER - in_cl;
        if (take > n - done) take = n - done;
        unsigned cl = bmap(ino, (unsigned)(at / CLUSTER), 0);
        if (cl) {
            char *p = cluster(cl, 1);
            if (!p) break;
            copy(dst + done, p + in_cl, take);
        } else zero(dst + done, take);
        done += take;
    }
    return done;
}

static int file_write(unsigned ino, u64 off, const char *src, u64 n) {
    struct inode *in = &INODES[ino];
    if (clusters_needed(ino, off, n) > S->free_clusters) return FS_FULL;
    u64 done = 0;
    while (done < n) {
        u64 at = off + done, in_cl = at % CLUSTER, take = CLUSTER - in_cl;
        if (take > n - done) take = n - done;
        unsigned idx = (unsigned)(at / CLUSTER);
        int existed = bmap(ino, idx, 0) != 0;
        unsigned cl = bmap(ino, idx, 1);
        if (!cl) return FS_FULL;
        char *p = cluster(cl, existed && (in_cl || take < CLUSTER));
        if (!p) return FS_FULL;
        copy(p + in_cl, src + done, take);
        dirty(cl);
        done += take;
    }
    if (off + n > in->size) { in->size = (unsigned)(off + n); inode_dirty(ino); }
    return S->overflow ? FS_FULL : FS_OK;
}

/* ---- folders ---- */

static int same(const char *a, const char *b) {
    int i = 0;
    for (; i < 56 && a[i] && a[i] == b[i]; i++) {}
    return i == 56 || a[i] == b[i];
}

/* The entry called `name` in folder `dir`: its position, or -1. */
static long dir_find(unsigned dir, const char *name, struct dirent *out) {
    struct inode *d = &INODES[dir];
    for (u64 at = 0; at + sizeof(struct dirent) <= d->size; at += sizeof(struct dirent)) {
        struct dirent e;
        if (file_read(dir, at, (char *)&e, sizeof e) != sizeof e) return -1;
        if (e.ino && same(e.name, name)) { if (out) *out = e; return (long)at; }
    }
    return -1;
}

static int dir_add(unsigned dir, const char *name, unsigned ino, unsigned kind) {
    struct inode *d = &INODES[dir];
    struct dirent e;
    zero((char *)&e, sizeof e);
    e.ino = ino;
    e.kind = kind;
    for (int i = 0; i < FS_NAME_MAX && name[i]; i++) e.name[i] = name[i];
    u64 at = d->size;
    for (u64 p = 0; p + sizeof e <= d->size; p += sizeof e) {
        struct dirent x;
        file_read(dir, p, (char *)&x, sizeof x);
        if (!x.ino) { at = p; break; }
    }
    return file_write(dir, at, (const char *)&e, sizeof e);
}

static int dir_remove(unsigned dir, long at) {
    struct dirent e;
    zero((char *)&e, sizeof e);
    return file_write(dir, (u64)at, (const char *)&e, sizeof e);
}

static int dir_empty(unsigned dir) {
    struct inode *d = &INODES[dir];
    for (u64 at = 0; at + sizeof(struct dirent) <= d->size; at += sizeof(struct dirent)) {
        struct dirent e;
        file_read(dir, at, (char *)&e, sizeof e);
        if (e.ino) return 0;
    }
    return 1;
}

static unsigned alloc_inode(unsigned kind) {
    for (unsigned i = 2; i < S->sb.inode_count; i++)
        if (!INODES[i].kind) {
            zero((char *)&INODES[i], sizeof(struct inode));
            INODES[i].kind = (unsigned short)kind;
            inode_dirty(i);
            return i;
        }
    return 0;
}

/* Split a path: the folder it is in (an inode), and its last name. 0 if a folder on the way
   is missing or the path is bad; the last name "" means the top folder itself. */
static unsigned walk(const char *path, char *last) {
    unsigned dir = 1;
    while (*path == '/') path++;
    last[0] = 0;
    for (;;) {
        int n = 0;
        while (path[n] && path[n] != '/') {
            if (n >= FS_NAME_MAX || path[n] < 32 || path[n] > 126) return 0;
            last[n] = path[n];
            n++;
        }
        last[n] = 0;
        const char *rest = path + n;
        while (*rest == '/') rest++;
        if (!*rest) return dir;
        if (n == 0) return 0;
        struct dirent e;
        if (dir_find(dir, last, &e) < 0 || e.kind != FS_DIR) return 0;
        dir = e.ino;
        path = rest;
    }
}

/* ---- who may reach what ---- */

/* A path ends within FS_PATH_MAX bytes (what follows its 0 may be anything). */
static int terminated(const char *p) {
    for (int i = 0; i <= FS_PATH_MAX; i++) if (!p[i]) return 1;
    return 0;
}

enum { BADGE_NOTES = 1, BADGE_TERMINAL = 5, BADGE_FILES = 9, BADGE_APPS = 16 };
static int trusted(u64 badge) {
    return badge == BADGE_NOTES || badge == BADGE_TERMINAL || badge == BADGE_FILES || badge == BADGE_APPS;
}
static int sharer(u64 badge) { return badge == BADGE_TERMINAL || badge == BADGE_FILES || badge == BADGE_APPS; }
static int open_slot(u64 badge) { return badge >= 10 && badge <= 15; }

/* `path` without leading, trailing or doubled '/'. */
static void normalize(const char *path, char *out) {
    int n = 0;
    for (int i = 0; path[i] && n < FS_PATH_MAX; i++) {
        if (path[i] == '/' && (n == 0 || out[n - 1] == '/')) continue;
        out[n++] = path[i];
    }
    while (n > 0 && out[n - 1] == '/') n--;
    out[n] = 0;
}

/* Whether `badge` may do what needs `rights` to `path`. */
static int allowed(u64 badge, const char *path, unsigned rights) {
    if (trusted(badge)) return 1;
    if (!open_slot(badge)) return 0;
    char p[FS_PATH_MAX + 1];
    normalize(path, p);
    for (int g = 0; g < MAX_GRANTS; g++) {
        struct grant *gr = &S->grants[g];
        if (gr->slot != badge || (gr->rights & rights) != rights || !gr->path[0]) continue;
        int i = 0;
        while (gr->path[i] && gr->path[i] == p[i]) i++;
        if (!gr->path[i] && (p[i] == 0 || p[i] == '/')) return 1;
    }
    return 0;
}

/* Whether the path `to` passes through folder `ino` (so a move there would put a folder
   inside itself). */
static int inside(const char *to, unsigned ino) {
    unsigned dir = 1;
    char name[FS_NAME_MAX + 1];
    while (*to == '/') to++;
    while (*to) {
        int n = 0;
        while (to[n] && to[n] != '/' && n < FS_NAME_MAX) { name[n] = to[n]; n++; }
        name[n] = 0;
        to += n;
        while (*to == '/') to++;
        if (!*to) return 0;                  /* the last name is the new one */
        struct dirent e;
        if (dir_find(dir, name, &e) < 0) return 0;
        dir = e.ino;
        if (dir == ino) return 1;
    }
    return 0;
}

/* ---- requests ---- */

/* Free clusters in the bitmap in memory (cluster 0 means "none": never counted). */
static unsigned count_free(void) {
    unsigned n = S->sb.clusters, taken = 0;
    for (unsigned cl = 1; cl < n;) {
        if (cl % 64 == 0 && cl + 64 <= n) {           /* 64 at once: a word's bits counted */
            u64 x = *(const u64 *)(BITMAP + cl / 8);
            x = x - ((x >> 1) & 0x5555555555555555UL);
            x = (x & 0x3333333333333333UL) + ((x >> 2) & 0x3333333333333333UL);
            x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FUL;
            taken += (unsigned)((x * 0x0101010101010101UL) >> 56);
            cl += 64;
        } else taken += !!used(cl++);
    }
    return n > 1 ? n - 1 - taken : 0;
}

/* Everything from the card: the bitmap, the inodes, and the shadow with them. */
static int load_metadata(void) {
    S->shadow_ok = 0;
    for (unsigned b = 0; b < S->sb.bitmap_blocks; b++)
        if (!bread(S->sb.bitmap_start + b, (char *)BITMAP + 512 * b)) return 0;
    for (unsigned b = 0; b < S->sb.inode_count / 8; b++)
        if (!bread(S->sb.inode_start + b, (char *)INODES + 512 * b)) return 0;
    S->free_clusters = count_free();
    meta_copy(SHADOW, (const char *)BITMAP);
    S->shadow_ok = 1;
    return 1;
}

/* A change that failed: what it changed in the metadata in memory is dropped, and the
   metadata becomes what the card holds, as reading all of it from the card again would
   make it. The shadow is exactly that (unless a write to the card failed: then it is read
   from the card, as it always was), so it is copied whole, and the free clusters counted
   again. That takes about 45 microseconds (in QEMU), where the read took 13 to 17 ms, and
   any program could make the file server spend those again and again, with requests that
   fail. */
static void rollback(void) {
    if (S->shadow_ok) {
        meta_copy((char *)BITMAP, SHADOW);
        S->free_clusters = count_free();
    } else load_metadata();
    op_begin();
}

/* SPACE, for any client: the file system's size and what is free, and how many files and
   folders there are (the inodes in use, which the check at start keeps to what the folders
   hold). Totals only: no name, no size of any one file, nothing any file holds. */
static u64 space_op(char *data, u64 *value, u64 *more) {
    struct fs_space *s = (struct fs_space *)data;
    zero(data, sizeof *s);
    s->cluster = CLUSTER;
    s->clusters = S->sb.clusters - 1;              /* cluster 0 means "none" */
    s->free = S->free_clusters;
    s->names = S->sb.inode_count - 2;              /* inode 0 means "none", 1 is the top folder */
    for (unsigned i = 2; i < S->sb.inode_count; i++) {
        s->files += INODES[i].kind == FS_FILE;
        s->folders += INODES[i].kind == FS_DIR;
    }
    *value = s->free;
    *more = s->clusters;
    return FS_OK;
}

static u64 serve_op(u64 op, u64 arg, char *buf, u64 *value, u64 *more);
static u64 share_op(u64 badge, u64 op, u64 arg, char *buf, u64 *value, struct line *l);

/* A request that fails part way leaves the card as it was (nothing was committed), and
   its changes to the copies in memory are dropped (rollback). */
static u64 serve(u64 badge, u64 op, u64 arg, char *buf, u64 *value, u64 *more, struct line *l) {
    if (op == FS_SPACE) return space_op(buf + FS_DATA_OFF, value, more);
    if (op >= FS_SHARE) return share_op(badge, op, arg, buf, value, l);
    if (!terminated(buf)) return FS_BAD;                          /* a path too long */
    if (op == FS_RENAME && !terminated(buf + FS_DATA_OFF)) return FS_BAD;
    unsigned need = op == FS_LIST || op == FS_READ || op == FS_STAT ? FS_R : FS_W;
    if (!allowed(badge, buf, need) || (op == FS_RENAME && !allowed(badge, buf + FS_DATA_OFF, FS_W))) {
        if (open_slot(badge) && S->refusals[badge] < 4) {
            S->refusals[badge]++;
            put_s(l, "fs: refused the program in slot ");
            put_dec(l, badge);
            put_s(l, need == FS_R ? " a read of " : " a change to ");
            put_s(l, buf[0] ? buf : "the top folder");
            put_s(l, ": not given to it\n");
            flush(l);
        }
        return FS_DENIED;
    }
    u64 code = serve_op(op, arg, buf, value, more);
    if (code != FS_OK && op != FS_LIST && op != FS_READ && op != FS_STAT) rollback();
    return code;
}

static u64 serve_op(u64 op, u64 arg, char *buf, u64 *value, u64 *more) {
    char path[FS_PATH_MAX + 1], name[FS_NAME_MAX + 1];
    int k = 0;
    for (; k < FS_PATH_MAX && buf[k]; k++) path[k] = buf[k];
    if (buf[k]) return FS_BAD;
    path[k] = 0;
    u64 off = *(u64 *)(buf + FS_OFFSET_AT);
    char *data = buf + FS_DATA_OFF;
    op_begin();
    unsigned dir = walk(path, name);
    if (!dir) return FS_NOT_FOUND;
    struct dirent e;
    long at = name[0] ? dir_find(dir, name, &e) : -1;
    unsigned ino = name[0] ? (at >= 0 ? e.ino : 0) : 1;     /* "" is the top folder */
    unsigned kind = ino ? INODES[ino].kind : 0;

    if (op == FS_LIST) {
        if (kind != FS_DIR) return ino ? FS_NOT_DIR : FS_NOT_FOUND;
        struct fs_entry *out = (struct fs_entry *)data;
        u64 n = 0, total = 0;
        struct inode *d = &INODES[ino];
        for (u64 p = 0; p + sizeof(struct dirent) <= d->size; p += sizeof(struct dirent)) {
            struct dirent x;
            file_read(ino, p, (char *)&x, sizeof x);
            if (!x.ino) continue;
            if (total >= arg && n < (u64)FS_LIST_MAX) {
                for (int i = 0; i < 56; i++) out[n].name[i] = x.name[i];
                out[n].size = INODES[x.ino].size;
                out[n].kind = INODES[x.ino].kind;
                n++;
            }
            total++;
        }
        *value = n;
        *more = total;
        return FS_OK;
    }
    if (op == FS_STAT) {
        if (!ino) return FS_NOT_FOUND;
        *value = INODES[ino].size;
        *more = kind;
        return FS_OK;
    }
    if (op == FS_READ) {
        if (!ino) return FS_NOT_FOUND;
        if (kind != FS_FILE) return FS_IS_DIR;
        *value = file_read(ino, off, data, FS_CHUNK);
        *more = INODES[ino].size;
        return FS_OK;
    }
    if (!name[0]) return FS_BAD;                         /* the top folder itself stays */
    u64 code = FS_OK;
    if (op == FS_WRITE || op == FS_WRITE_AT) {
        if (arg > FS_CHUNK) return FS_BAD;
        if (kind == FS_DIR) return FS_IS_DIR;
        if (op == FS_WRITE_AT && off + arg > 0xFFFFFFFFUL) return FS_FULL;
        if (!ino) {
            if (!(ino = alloc_inode(FS_FILE))) return FS_FULL;
            if ((code = (u64)dir_add(dir, name, ino, FS_FILE)) != FS_OK) return code;
        }
        if (op == FS_WRITE) truncate_all(ino);
        if ((code = (u64)file_write(ino, op == FS_WRITE ? 0 : off, data, arg)) != FS_OK) return code;
        *value = arg;
    } else if (op == FS_MKDIR) {
        if (ino) return FS_EXISTS;
        if (!(ino = alloc_inode(FS_DIR))) return FS_FULL;
        if ((code = (u64)dir_add(dir, name, ino, FS_DIR)) != FS_OK) return code;
    } else if (op == FS_DELETE) {
        if (!ino) return FS_NOT_FOUND;
        if (kind == FS_DIR && !dir_empty(ino)) return FS_NOT_EMPTY;
        truncate_all(ino);
        INODES[ino].kind = 0;
        inode_dirty(ino);
        if ((code = (u64)dir_remove(dir, at)) != FS_OK) return code;
    } else if (op == FS_RENAME) {
        if (!ino) return FS_NOT_FOUND;
        char to[FS_PATH_MAX + 1], toname[FS_NAME_MAX + 1];
        int n = 0;
        for (; n < FS_PATH_MAX && data[n]; n++) to[n] = data[n];
        if (data[n]) return FS_BAD;
        to[n] = 0;
        unsigned todir = walk(to, toname);
        if (!todir || !toname[0]) return FS_NOT_FOUND;
        if (kind == FS_DIR && inside(to, ino)) return FS_BAD;   /* not into itself */
        struct dirent old;
        long oat = dir_find(todir, toname, &old);
        if (oat >= 0) {
            if (old.ino == ino) return FS_OK;
            if (old.kind != FS_FILE || kind != FS_FILE) return FS_EXISTS;
            truncate_all(old.ino);                       /* replaced, in the same step */
            INODES[old.ino].kind = 0;
            inode_dirty(old.ino);
            if ((code = (u64)dir_remove(todir, oat)) != FS_OK) return code;
        }
        if ((code = (u64)dir_remove(dir, at)) != FS_OK) return code;
        if ((code = (u64)dir_add(todir, toname, ino, kind)) != FS_OK) return code;
    } else return FS_BAD;
    if (!commit()) return S->overflow ? FS_FULL : FS_IO;
    return FS_OK;
}

/* SHARE, UNSHARE, GRANTS. */
static u64 share_op(u64 badge, u64 op, u64 arg, char *buf, u64 *value, struct line *l) {
    char p[FS_PATH_MAX + 1];
    if (!terminated(buf)) return FS_BAD;
    normalize(buf, p);
    if (op == FS_GRANTS) {
        char *out = buf + FS_DATA_OFF;
        u64 n = 0, at = 0;
        for (int g = 0; g < MAX_GRANTS; g++) {
            struct grant *gr = &S->grants[g];
            if (gr->slot != badge || !open_slot(badge)) continue;
            int len = 0;
            while (gr->path[len]) len++;
            if (at + (u64)len + 2 > FS_CHUNK) break;
            out[at++] = (char)gr->rights;
            for (int i = 0; i <= len; i++) out[at++] = gr->path[i];
            n++;
        }
        *value = n;
        return FS_OK;
    }
    if (!sharer(badge)) return FS_DENIED;
    u64 slot = arg & 255;
    if (!open_slot(slot)) return FS_BAD;
    if (op == FS_UNSHARE) {
        u64 n = 0;
        for (int g = 0; g < MAX_GRANTS; g++)
            if (S->grants[g].slot == slot) { S->grants[g].slot = 0; n++; }
        S->refusals[slot] = 0;
        if (n) {
            put_s(l, "fs: took back ");
            put_dec(l, n);
            put_s(l, n == 1 ? " path from slot " : " paths from slot ");
            put_dec(l, slot);
            put_s(l, "\n");
            flush(l);
        }
        return FS_OK;
    }
    if (op != FS_SHARE || !p[0]) return FS_BAD;
    /* The record: the slot's own for this path (its rights change), or a free one if the
       slot holds fewer than its share. Each open slot may hold FS_GRANTS_PER_SLOT, and the
       table has that many for every slot, so however many files one program is given, and
       however long the records of a program that stopped wait for its slot to start again,
       every other slot still has room for its folder and its files. */
    int rec = -1, free = -1, held = 0;
    for (int g = 0; g < MAX_GRANTS; g++) {
        struct grant *gr = &S->grants[g];
        int i = 0;
        while (gr->path[i] && gr->path[i] == p[i]) i++;
        if (gr->slot == slot && !gr->path[i] && !p[i]) rec = g;
        held += gr->slot == slot;
        if (!gr->slot && free < 0) free = g;
    }
    if (rec < 0 && (held >= FS_GRANTS_PER_SLOT || free < 0)) return FS_FULL;
    if ((arg >> 16) & 1) {                /* the folder, and the folders it is in */
        char part[FS_PATH_MAX + 1];
        u64 v, m;
        for (int i = 0;; i++) {
            if (p[i] == '/' || !p[i]) {
                for (int k = 0; k < i; k++) part[k] = p[k];
                part[i] = 0;
                for (int k = 0; k <= i; k++) buf[k] = part[k];
                u64 code = serve_op(FS_STAT, 0, buf, &v, &m);
                if (code == FS_NOT_FOUND) code = serve_op(FS_MKDIR, 0, buf, &v, &m);
                else if (m != FS_DIR) code = FS_NOT_DIR;
                if (code != FS_OK) {      /* a folder not made (the card full): as serve() does */
                    rollback();
                    return code;
                }
            }
            if (!p[i]) break;
        }
    }
    struct grant *gr = &S->grants[rec >= 0 ? rec : free];
    gr->rights = (unsigned char)((arg >> 8) & 3);
    if (rec >= 0) return FS_OK;
    gr->slot = (unsigned char)slot;
    for (int i = 0; i <= FS_PATH_MAX; i++) { gr->path[i] = p[i]; if (!p[i]) break; }
    return FS_OK;
}

/* ---- the whole tree, checked ---- */

/* Mark cluster `cl` as belonging to a file. 0 if it cannot (out of range, or taken). */
static int claim(unsigned char *map, unsigned cl) {
    if (cl == 0 || cl >= S->sb.clusters || (map[cl / 8] & (1 << (cl % 8)))) return 0;
    map[cl / 8] |= (unsigned char)(1 << (cl % 8));
    return 1;
}

static void claim_file(unsigned char *map, unsigned ino) {
    struct inode *in = &INODES[ino];
    for (int i = 0; i < NDIRECT; i++)
        if (in->direct[i] && !claim(map, in->direct[i])) { in->direct[i] = 0; inode_dirty(ino); S->repaired++; }
    if (in->indirect) {
        if (!claim(map, in->indirect)) { in->indirect = 0; inode_dirty(ino); S->repaired++; }
        else {
            unsigned *p = (unsigned *)cluster(in->indirect, 1);
            for (int i = 0; p && i < PTRS; i++)
                if (p[i] && !claim(map, p[i])) { p[i] = 0; dirty(in->indirect); S->repaired++; }
        }
    }
    if (in->dindirect) {
        if (!claim(map, in->dindirect)) { in->dindirect = 0; inode_dirty(ino); S->repaired++; }
        else {
            unsigned outer[PTRS];
            unsigned *o = (unsigned *)cluster(in->dindirect, 1);
            for (int j = 0; j < PTRS; j++) outer[j] = o ? o[j] : 0;
            for (int j = 0; j < PTRS; j++) {
                if (!outer[j]) continue;
                if (!claim(map, outer[j])) {
                    unsigned *w = (unsigned *)cluster(in->dindirect, 1);
                    if (w) { w[j] = 0; dirty(in->dindirect); }
                    S->repaired++;
                    continue;
                }
                unsigned *p = (unsigned *)cluster(outer[j], 1);
                for (int i = 0; p && i < PTRS; i++)
                    if (p[i] && !claim(map, p[i])) { p[i] = 0; dirty(outer[j]); S->repaired++; }
            }
        }
    }
    u64 max = ((u64)NDIRECT + PTRS + (u64)PTRS * PTRS) * CLUSTER;
    if (in->size > max) { in->size = 0; inode_dirty(ino); S->repaired++; }
}

/* Walk the tree from the top folder: count what is there, drop entries that point at
   nothing, and remember which inodes are reachable. In rounds over the inodes: each folder
   found is read once, so a tree of any depth is walked without recursion (a path of 200
   bytes goes 100 folders down, and a folder moved into another can go deeper still). */
static void walk_tree(unsigned *files, unsigned *dirs) {
    unsigned char walked[MAX_INODES / 8];
    zero((char *)walked, sizeof walked);
    for (int again = 1; again;) {
        again = 0;
        for (unsigned dir = 1; dir < S->sb.inode_count; dir++) {
            if (!(S->seen_ino[dir / 8] & (1 << (dir % 8))) || (walked[dir / 8] & (1 << (dir % 8))) ||
                INODES[dir].kind != FS_DIR)
                continue;
            walked[dir / 8] |= (unsigned char)(1 << (dir % 8));
            again = 1;
            struct inode *d = &INODES[dir];
            for (u64 at = 0; at + sizeof(struct dirent) <= d->size; at += sizeof(struct dirent)) {
                struct dirent e;
                file_read(dir, at, (char *)&e, sizeof e);
                if (!e.ino) continue;
                int bad = e.ino >= S->sb.inode_count || e.ino < 2 || !INODES[e.ino].kind ||
                          INODES[e.ino].kind != e.kind || (S->seen_ino[e.ino / 8] & (1 << (e.ino % 8)));
                if (bad) {
                    dir_remove(dir, (long)at);
                    S->repaired++;
                    continue;
                }
                S->seen_ino[e.ino / 8] |= (unsigned char)(1 << (e.ino % 8));
                if (e.kind == FS_DIR) (*dirs)++;
                else (*files)++;
            }
        }
    }
}

static void check(struct line *l, unsigned *files, unsigned *dirs) {
    S->repaired = 0;
    op_begin();
    /* files first: which clusters each one uses (the map: 16 KiB of the memory a disk
       without a card would use, free when there is a card) */
    unsigned char *map = (unsigned char *)PAGE(RAMDISK_PAGE);
    zero((char *)map, 4 * 4096);
    map[0] |= 1;
    INODES[1].kind = FS_DIR;
    for (unsigned i = 1; i < S->sb.inode_count; i++)
        if (INODES[i].kind) {
            claim_file(map, i);
            if (S->overflow) { commit(); op_begin(); }
        }
    /* then the tree: every entry to a live inode, every live inode in the tree */
    zero((char *)S->seen_ino, sizeof S->seen_ino);
    S->seen_ino[0] |= 3;
    *files = *dirs = 0;
    walk_tree(files, dirs);
    for (unsigned i = 2; i < S->sb.inode_count; i++)
        if (INODES[i].kind && !(S->seen_ino[i / 8] & (1 << (i % 8)))) {
            truncate_all(i);
            INODES[i].kind = 0;
            inode_dirty(i);
            S->repaired++;
        }
    /* the bitmap is what the files use: nothing leaks, nothing is used twice */
    unsigned free = 0;
    for (unsigned cl = 0; cl < S->sb.clusters; cl++) {
        int want = (map[cl / 8] >> (cl % 8)) & 1;
        if (!!used(cl) != want) {
            set_used(cl, want);
            S->repaired++;
        }
        if (!want) free++;
    }
    S->free_clusters = free;
    if (S->repaired) {
        commit();
        put_s(l, "fs: repaired ");
        put_dec(l, (u64)S->repaired);
        put_s(l, S->repaired == 1 ? " thing on the card\n" : " things on the card\n");
        flush(l);
    }
}

/* ---- a new file system ---- */

static void geometry(struct super *sb, unsigned total, unsigned journal, unsigned inodes) {
    zero((char *)sb, sizeof *sb);
    copy(sb->magic, MAGIC, 8);
    sb->version = 2;
    sb->total = total;
    sb->journal_start = 1;
    sb->journal_blocks = journal;
    sb->bitmap_start = 1 + journal;
    unsigned est = (total - sb->bitmap_start - inodes / 8) / PER_CLUSTER;
    if (est > MAX_CLUSTERS) est = MAX_CLUSTERS;
    sb->bitmap_blocks = (est + 4095) / 4096;
    sb->inode_start = sb->bitmap_start + sb->bitmap_blocks;
    sb->inode_count = inodes;
    sb->data_start = (sb->inode_start + inodes / 8 + 7) & ~7u;
    unsigned cl = (total - sb->data_start) / PER_CLUSTER;
    if (cl > sb->bitmap_blocks * 4096) cl = sb->bitmap_blocks * 4096;
    sb->clusters = cl;
}

static int format(unsigned total) {
    struct super *sb = &S->sb;
    if (S->ram) geometry(sb, total, 128, 128);
    else geometry(sb, total, 256, MAX_INODES);
    zero((char *)BITMAP, 4 * 4096);
    zero((char *)INODES, 16 * 4096);
    BITMAP[0] = 1;                                   /* cluster 0 means "none" */
    INODES[1].kind = FS_DIR;
    char *z = stage_page(0);
    zero(z, 512);
    int ok = bwrite(sb->journal_start, z);           /* an empty journal */
    for (unsigned b = 0; b < sb->bitmap_blocks && ok; b++) ok &= bwrite(sb->bitmap_start + b, (char *)BITMAP + 512 * b);
    for (unsigned b = 0; b < sb->inode_count / 8 && ok; b++) ok &= bwrite(sb->inode_start + b, (char *)INODES + 512 * b);
    zero(z, 512);
    copy(z, (const char *)sb, sizeof *sb);
    if (ok) ok &= bwrite(0, z);                      /* last: the superblock makes it real */
    S->seq = 0;
    S->free_clusters = sb->clusters - 1;
    meta_copy(SHADOW, (const char *)BITMAP);
    S->shadow_ok = ok;
    return ok;
}

/* The data partition's size in blocks: the last one that can be read, found by halving. */
static unsigned card_blocks(void) {
    char *z = stage_page(1);
    u64 lo = 0, hi = CARD_MAX_BLOCKS;       /* lo readable, hi not (or past the capability) */
    while (hi - lo > 1) {
        u64 mid = (lo + hi) / 2;
        if (bread(mid, z)) lo = mid;
        else hi = mid;
    }
    return (unsigned)(lo + 1);
}

static int mount(void) {
    char *z = stage_page(0);
    if (!bread(0, z)) return 0;
    struct super *sb = (struct super *)z;
    for (int i = 0; i < 8; i++) if (sb->magic[i] != MAGIC[i]) return 0;
    if (sb->version != 2 || sb->bitmap_blocks > 32 || sb->inode_count > MAX_INODES ||
        sb->clusters > sb->bitmap_blocks * 4096 || sb->journal_blocks < 2 || sb->data_start >= sb->total)
        return 0;
    S->sb = *sb;
    return 1;
}

static int load(struct line *l) {
    return replay(l) && load_metadata();
}

__attribute__((section(".text.start"))) void _start(void) {
    struct server *sv = S;
    struct line l = {.n = 0};
    sys2(SYS_MAP, SPARE, BITMAP_PAGE);
    sv->errors = 0;
    sv->ram = 0;
    sv->shadow_ok = 0;
    for (int g = 0; g < MAX_GRANTS; g++) sv->grants[g].slot = 0;
    for (int i = 0; i < 16; i++) sv->refusals[i] = 0;
    sv->rover = 1;

    /* The card, if there is one: its file system, or a new one. */
    char *z = stage_page(0);
    sv->on_disk = bread(0, z);
    int fresh = 0;
    if (!sv->on_disk) {
        sv->ram = 1;
        format(RAM_BLOCKS);
        fresh = 1;
    } else if (!mount() || !load(&l)) {
        format(card_blocks());
        fresh = 1;
    }
    unsigned files = 0, dirs = 0;
    if (fresh) {
        static const char welcome[] =
            "Welcome to leanos. Files are kept on the SD card, so they are still here after "
            "a restart. Notes saves here, Terminal can ls, cat, write and rm, and Files shows "
            "them all.";
        char *buf = (char *)PAGE(20);           /* a data page: the cluster pages are busy */
        zero(buf, FS_DATA_OFF);
        copy(buf, "welcome.txt", 12);
        *(u64 *)(buf + FS_OFFSET_AT) = 0;
        copy(buf + FS_DATA_OFF, welcome, sizeof welcome - 1);
        u64 v, m;
        serve(BADGE_TERMINAL, FS_WRITE, sizeof welcome - 1, buf, &v, &m, &l);
        files = 1;
        if (sv->on_disk) put_s(&l, "fs: made a new file system on the SD card; ready, 1 file\n");
        else put_s(&l, "fs: no SD card; files are kept in memory only; ready, 1 file\n");
    } else {
        check(&l, &files, &dirs);
        put_s(&l, "fs: ready, ");
        put_dec(&l, files);
        put_s(&l, files == 1 ? " file on the SD card\n" : " files on the SD card\n");
        flush(&l);
        put_s(&l, "fs: checked: ");
        put_dec(&l, files);
        put_s(&l, files == 1 ? " file in " : " files in ");
        put_dec(&l, dirs + 1);
        put_s(&l, dirs ? " folders, " : " folder, ");
        put_dec(&l, (u64)sv->free_clusters * 4);
        put_s(&l, " KiB free of ");
        put_dec(&l, (u64)(sv->sb.clusters - 1) * 4);
        put_s(&l, ", journal ");
        put_dec(&l, sv->sb.journal_blocks / 2);
        put_s(&l, " KiB\n");
    }
    flush(&l);

    for (;;) {
        struct res r = sys1(SYS_RECV, EP);
        u64 badge = r.x[1], op = r.x[2], arg = r.x[3], grant = r.x[5], slot = r.x[6];
        if (!slot) {                      /* a plain send: nobody to answer */
            /* A capability it grants is let go of all the same: kept, 58 of them would
               fill the server's 64, and every request carries one (test/chaos.sh). */
            if (grant) sys1(SYS_DROP, grant - 1);
            continue;
        }
        u64 code = FS_BAD, value = 0, more = 0;
        if (grant) {
            struct res info = sys1(SYS_CAPINFO, grant - 1);
            if (info.x[2] == 0 && info.x[3] == FS_BUF_PAGES && (info.x[1] & (R | W)) == (R | W) &&
                sys2(SYS_MAP, grant - 1, BUF_PAGE).status == OK) {
                code = serve(badge, op, arg, (char *)PAGE(BUF_PAGE), &value, &more, &l);
                sys2(SYS_UNMAP, BUF_PAGE, FS_BUF_PAGES);
            }
            sys1(SYS_DROP, grant - 1);
        }
        sys(SYS_REPLY, slot - 1, code, value, more, 0);
    }
}
