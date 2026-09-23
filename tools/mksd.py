#!/usr/bin/env python3
"""Writes an SD card image for leanos: a partition table (MBR) and a data partition of type
0xDA holding the file server's file system (user/fs.c: the table of files in the
partition's blocks 0-7, file i's data from block 8 + 32 i), with welcome.txt and the
programs given, so Terminal can run them (`run NAME`).

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
MAX_FILES, FILE_BLOCKS, TABLE_BLOCKS, FILE_MAX = 48, 32, 8, 4 * 4096 - 64
WELCOME = (b"Welcome to leanos. Files are kept on the SD card, so they are still here after "
           b"a restart. Notes saves here, Terminal can ls, cat, write and rm, and Files shows "
           b"them all.")


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


def file_system(files):
    """The data partition's contents: the table, then each file's data."""
    if len(files) > MAX_FILES:
        sys.exit("too many files")
    table = bytearray(TABLE_BLOCKS * SECTOR)
    table[0:8] = b"LEANOSFS"
    struct.pack_into("<II", table, 8, 1, 0)
    data = bytearray((TABLE_BLOCKS + FILE_BLOCKS * len(files)) * SECTOR)
    for i, (name, content) in enumerate(files):
        if len(name.encode()) > 40 or not name.isprintable() or "/" in name or " " in name:
            sys.exit(f"bad file name: {name}")
        if len(content) > FILE_MAX:
            sys.exit(f"{name} is {len(content)} bytes; a file holds at most {FILE_MAX}")
        entry = 16 + 64 * i
        table[entry:entry + 48] = name.encode().ljust(48, b"\0")
        struct.pack_into("<II", table, entry + 48, len(content), 1)
        at = (TABLE_BLOCKS + FILE_BLOCKS * i) * SECTOR
        data[at:at + len(content)] = content
    data[0:len(table)] = table
    return data


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
        fs = file_system(program_files(specs))
        card[DATA_START * SECTOR:DATA_START * SECTOR + len(fs)] = fs
    open(out, "wb").write(card)


if __name__ == "__main__":
    main()
