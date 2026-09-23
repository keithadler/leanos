#!/usr/bin/env python3
"""Writes an SD card image in the file server's format (user/fs.c): the table of files in
blocks 0-7, file i's data from block 8 + 32 i. The card holds welcome.txt and the programs
given, so they can be run from Terminal (`run NAME`) the way programs are copied onto a
card for any computer.

Usage: mksd.py OUT.img NAME=FILE ...
"""
import struct
import sys

SIZE = 8 * 1024 * 1024
MAX_FILES, FILE_BLOCKS, TABLE_BLOCKS, FILE_MAX = 48, 32, 8, 4 * 4096 - 64
WELCOME = (b"Welcome to leanos. Files are kept on the SD card, so they are still here after "
           b"a restart. Notes saves here, Terminal can ls, cat, write and rm, and Files shows "
           b"them all.")


def main():
    out, specs = sys.argv[1], sys.argv[2:]
    files = [("welcome.txt", WELCOME)]
    for spec in specs:
        name, path = spec.split("=", 1)
        files.append((name, open(path, "rb").read()))
    if len(files) > MAX_FILES:
        sys.exit("too many files")
    card = bytearray(SIZE)
    table = bytearray(TABLE_BLOCKS * 512)
    table[0:8] = b"LEANOSFS"
    struct.pack_into("<II", table, 8, 1, 0)
    for i, (name, data) in enumerate(files):
        if len(name.encode()) > 40 or not name.isprintable() or "/" in name or " " in name:
            sys.exit(f"bad file name: {name}")
        if len(data) > FILE_MAX:
            sys.exit(f"{name} is {len(data)} bytes; a file holds at most {FILE_MAX}")
        entry = 16 + 64 * i
        table[entry:entry + 48] = name.encode().ljust(48, b"\0")
        struct.pack_into("<II", table, entry + 48, len(data), 1)
        at = (TABLE_BLOCKS + FILE_BLOCKS * i) * 512
        card[at:at + len(data)] = data
    card[0:len(table)] = table
    open(out, "wb").write(card)


if __name__ == "__main__":
    main()
