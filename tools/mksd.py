#!/usr/bin/env python3
"""Writes an SD card image for leanos: a partition table (MBR) and a data partition of type
0xDA holding the file server's file system (user/fs.c: a superblock, a journal, a bitmap of
4 KiB clusters, inodes, and the files, all in the top folder), with welcome.txt and the
programs given, so Terminal can run them (`run NAME`). A NAME with '/' in it goes in folders,
made as needed: apps/view/colors.bmp=FILE puts a picture in view's own folder.

The machine layer finds the data partition at boot and keeps every block the file server
reads or writes inside it; a real card's boot partition is never touched. tools/mkpiimage.py
adds the FAT boot partition a Raspberry Pi starts from.

Usage: mksd.py OUT.img [--blank] NAME=FILE ...
  --blank   an empty data partition (the file server formats it on first boot)
"""
import struct
import sys

SECTOR = 512
CARD_BYTES = 8 * 1024 * 1024
DATA_START = 2048                 # the data partition's first block (1 MiB in)
WELCOME = (b"Welcome to leanos. Files are kept on the SD card, so they are still here after "
           b"a restart. Notes saves here, Terminal can ls, cat, write and rm, and Files shows "
           b"them all.")

# The file system of user/fs.c (keep the two in step): 512-byte blocks, 4 KiB clusters.
MAGIC = b"LEANOSF2"
CLUSTER, PER_CLUSTER, PTRS, NDIRECT = 4096, 8, 1024, 12
MAX_CLUSTERS, JOURNAL, INODES = 4 * 4096 * 8, 256, 1024
FS_FILE, FS_DIR = 1, 2
NAME_MAX = 55


def mbr(partitions):
    """A master boot record: partitions as (type, first block, number of blocks)."""
    m = bytearray(SECTOR)
    for i, (kind, start, count) in enumerate(partitions):
        e = 446 + 16 * i
        m[e + 0] = 0x00                              # not the boot partition in the BIOS sense
        m[e + 1:e + 4] = b"\xfe\xff\xff"             # CHS unused: LBA only
        m[e + 4] = kind
        m[e + 5:e + 8] = b"\xfe\xff\xff"
        struct.pack_into("<II", m, e + 8, start, count)
    m[510:512] = b"\x55\xaa"
    return m


def geometry(total, journal=JOURNAL, inodes=INODES):
    """Where everything goes on a partition of `total` blocks (fs.c: geometry)."""
    g = {"total": total, "journal_start": 1, "journal_blocks": journal, "bitmap_start": 1 + journal}
    est = min((total - g["bitmap_start"] - inodes // 8) // PER_CLUSTER, MAX_CLUSTERS)
    g["bitmap_blocks"] = (est + 4095) // 4096
    g["inode_start"] = g["bitmap_start"] + g["bitmap_blocks"]
    g["inode_count"] = inodes
    g["data_start"] = (g["inode_start"] + inodes // 8 + 7) & ~7
    g["clusters"] = min((total - g["data_start"]) // PER_CLUSTER, g["bitmap_blocks"] * 4096)
    return g


def file_system(files, total):
    """The data partition's contents: the files, in the top folder or (a name with '/') in
    folders under it."""
    g = geometry(total)
    disk = bytearray(g["data_start"] * SECTOR)
    clusters = {}                                    # cluster number -> 4 KiB
    inodes = bytearray(g["inode_count"] * 64)
    bitmap = bytearray(g["bitmap_blocks"] * SECTOR)
    next_cluster = [1]                               # cluster 0 means "none"

    def alloc(data=b""):
        c = next_cluster[0]
        if c >= g["clusters"]:
            sys.exit("the files do not fit on the card")
        next_cluster[0] += 1
        clusters[c] = bytes(data).ljust(CLUSTER, b"\0")
        return c

    def write_inode(ino, kind, content):
        pieces = [content[i:i + CLUSTER] for i in range(0, len(content), CLUSTER)]
        direct = [alloc(p) for p in pieces[:NDIRECT]]
        indirect = 0
        rest = pieces[NDIRECT:]
        if len(rest) > PTRS:
            sys.exit("a file too large for mksd.py (it writes no double-indirect clusters)")
        if rest:
            ptrs = [alloc(p) for p in rest]
            indirect = alloc(struct.pack(f"<{len(ptrs)}I", *ptrs))
        struct.pack_into("<HHI12III", inodes, 64 * ino, kind, 0, len(content),
                         *(direct + [0] * (NDIRECT - len(direct))), indirect, 0)

    # the tree: a folder is a dict of name -> content (bytes) or folder, in the order given
    top = {}
    for name, content in files:
        parts = name.split("/")
        for part in parts:
            if not part or len(part.encode()) > NAME_MAX or not part.isprintable() or " " in part:
                sys.exit(f"bad file name: {name}")
        folder = top
        for part in parts[:-1]:
            folder = folder.setdefault(part, {})
            if not isinstance(folder, dict):
                sys.exit(f"{name}: {part} is a file, not a folder")
        if parts[-1] in folder:
            sys.exit(f"{name} is on the card twice")
        folder[parts[-1]] = content
    next_ino = [2]

    def write_folder(ino, folder):
        """Each entry first (a folder's own entries before it), then the folder itself."""
        entries = bytearray()
        for name, content in folder.items():
            child = next_ino[0]
            next_ino[0] += 1
            if child >= g["inode_count"]:
                sys.exit("too many files")
            kind = FS_DIR if isinstance(content, dict) else FS_FILE
            if kind == FS_DIR:
                write_folder(child, content)
            else:
                write_inode(child, FS_FILE, content)
            entries += struct.pack("<II", child, kind) + name.encode().ljust(56, b"\0")
        write_inode(ino, FS_DIR, bytes(entries))

    write_folder(1, top)                             # the top folder

    for c in range(next_cluster[0]):
        bitmap[c // 8] |= 1 << (c % 8)
    sb = struct.pack("<8s10I", MAGIC, 2, g["total"], g["journal_start"], g["journal_blocks"],
                     g["bitmap_start"], g["bitmap_blocks"], g["inode_start"], g["inode_count"],
                     g["data_start"], g["clusters"])
    disk[0:len(sb)] = sb                             # the journal stays empty (zeros)
    b = g["bitmap_start"] * SECTOR
    disk[b:b + len(bitmap)] = bitmap
    b = g["inode_start"] * SECTOR
    disk[b:b + len(inodes)] = inodes
    end = (g["data_start"] + next_cluster[0] * PER_CLUSTER) * SECTOR
    disk = disk.ljust(end, b"\0")
    for c, data in clusters.items():
        at = (g["data_start"] + c * PER_CLUSTER) * SECTOR
        disk[at:at + CLUSTER] = data
    return disk


def program_files(specs):
    files = [("welcome.txt", WELCOME)]
    for spec in specs:
        name, path = spec.split("=", 1)
        files.append((name, open(path, "rb").read()))
    return files


def main():
    args = sys.argv[1:]
    out = args.pop(0)
    blank = "--blank" in args
    specs = [a for a in args if a != "--blank"]
    card = bytearray(CARD_BYTES)
    blocks = CARD_BYTES // SECTOR
    card[0:SECTOR] = mbr([(0xDA, DATA_START, blocks - DATA_START)])
    if not blank:
        fs = file_system(program_files(specs), blocks - DATA_START)
        card[DATA_START * SECTOR:DATA_START * SECTOR + len(fs)] = fs
    open(out, "wb").write(card)


if __name__ == "__main__":
    main()
