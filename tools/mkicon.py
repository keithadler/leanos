#!/usr/bin/env python3
"""Writes a program's icon for the SD card: NAME.icon next to the program NAME. The format is
the display server's icon asset (tools/mkassets.py): u32 width, u32 height, then premultiplied
0xAARRGGBB pixels, row by row. The Apps launcher shows it; a program without one gets a tile
with its initial.

Usage: mkicon.py OUT.icon IN.png [PIXELS]   (default 64)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mkassets import icon_blob  # noqa: E402

if __name__ == "__main__":
    out, src = sys.argv[1], sys.argv[2]
    size = int(sys.argv[3]) if len(sys.argv) > 3 else 64
    open(out, "wb").write(icon_blob(src, size))
