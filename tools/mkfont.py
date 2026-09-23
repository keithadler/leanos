#!/usr/bin/env python3
"""Turns user/font5x7.txt into a C table: font5x7[c - 32][row], five bits per row, bit 4 = left."""
import sys

src, dst = sys.argv[1], sys.argv[2]
glyphs = {}
for line in open(src, encoding="utf-8"):
    if not line.strip() or line.startswith("#") and len(line.split()) != 8:
        continue
    parts = line.split()
    ch = " " if parts[0] == "space" else parts[0]
    rows = parts[1:]
    if len(ch) != 1 or len(rows) != 7 or any(len(r) != 5 or set(r) - {".", "#"} for r in rows):
        sys.exit(f"bad glyph line: {line!r}")
    glyphs[ch] = [int(r.replace(".", "0").replace("#", "1"), 2) for r in rows]
missing = [chr(c) for c in range(32, 127) if chr(c) not in glyphs]
if missing:
    sys.exit(f"font is missing: {''.join(missing)!r}")
with open(dst, "w") as out:
    out.write("/* Generated from user/font5x7.txt by tools/mkfont.py. */\n")
    out.write("static const unsigned char font5x7[95][7] = {\n")
    for c in range(32, 127):
        out.write("    {" + ", ".join(str(v) for v in glyphs[chr(c)]) + "},\n")
    out.write("};\n")
