#!/usr/bin/env python3
"""Prints how much of its code run each user program takes, and fails if one takes more.

A program's code (and its constants) runs from 16 read/execute pages, 64 KiB, at 0x80000000
(user/user.ld, and the code runs the manifest gives in LeanOS/Kernel.lean). The linker
refuses a program over that; this makes the room left visible, so a program that grows
toward the limit is seen before it reaches it. A program from the card also carries its icon
in the last four pages of its run (user/elf.h): over 48 KiB it still runs, without its icon.

Usage: codesize.py OUT.txt PROGRAM.elf ...   (the table goes to the terminal and to OUT.txt,
which is written only if every program fits)
"""
import os
import struct
import sys

BASE = 0x80000000
RUN = 16 * 4096           # the code run
ICON_AT = 12 * 4096       # where a card program's icon goes (user/elf.h, ICON_IMAGE_PAGE)


def code_size(path):
    """The bytes of the code run the program's loadable segments reach, from its start."""
    data = open(path, "rb").read()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        sys.exit(f"{path}: not a 64-bit little-endian ELF file")
    phoff, = struct.unpack_from("<Q", data, 32)
    phentsize, phnum = struct.unpack_from("<HH", data, 54)
    end = BASE
    for i in range(phnum):
        p_type, _flags, _off, vaddr, _paddr, _filesz, memsz = struct.unpack_from("<IIQQQQQ", data, phoff + i * phentsize)
        if p_type == 1 and memsz:        # PT_LOAD
            if vaddr < BASE:
                sys.exit(f"{path}: a segment at {vaddr:#x}, before the code run")
            end = max(end, vaddr + memsz)
    return end - BASE


def main():
    out, paths = sys.argv[1], sys.argv[2:]
    lines, over = [f"code size, of the {RUN // 1024} KiB code run each program has:"], []
    for path in paths:
        name = os.path.splitext(os.path.basename(path))[0]
        card = os.path.basename(os.path.dirname(path)) == "progs"
        n = code_size(path)
        note = ""
        if n > RUN:
            over.append(name)
            note = "  TOO BIG"
        elif card and n > ICON_AT:
            note = "  (no room for its icon)"
        where = "card" if card else "kernel image"
        lines.append(f"  {name:<10} {where:<12} {n:>6} bytes, {RUN - n:>6} left ({100 * n // RUN:>2}%){note}")
    print("\n".join(lines))
    if over:
        sys.exit(f"codesize: larger than the {RUN // 1024} KiB code run: {', '.join(over)}")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
