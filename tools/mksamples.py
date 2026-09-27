#!/usr/bin/env python3
"""Writes the sample pictures `view` finds in its folder, apps/view/, on the card people use
(the Makefile's VIEW_SAMPLES): made here at build time, so no picture is kept in git.

  colors.bmp   a test pattern, 24-bit BMP (bottom-up, rows padded to 4 bytes, as paint
               saves): color bars, a gray ramp, red, green and blue ramps, and a fine
               checkerboard that only a scaled-down view that averages shows as gray
  sunset.ppm   something simple, binary PPM (P6): a sky, a sun, hills and the sea

The writers are used by test/view.sh too, for its own pictures (every kind view reads, and
some it must refuse).

Usage: mksamples.py OUT/NAME   (writes the sample called NAME)
"""
import math
import os
import struct
import sys


def bmp(w, h, pixel, bpp=24, topdown=False, palette=None, header=40):
    """A BMP of w x h: pixel(x, y) is an (r, g, b), or a palette index when bpp is 8, 4 or 1
    (palette: a list of (r, g, b)). bpp 32 writes BI_BITFIELDS masks (header 40: after it;
    108: inside it, a V4 header). Rows go bottom-up unless topdown."""
    stride = (w * bpp + 31) // 32 * 4
    rows = []
    for y in range(h):
        row = bytearray()
        if bpp in (24, 32):
            for x in range(w):
                r, g, b = pixel(x, y)
                row += bytes((b, g, r)) + (b"\xff" if bpp == 32 else b"")
        else:
            bits = 0
            n = 0
            for x in range(w):
                bits = bits << bpp | pixel(x, y)
                n += bpp
                if n == 8:
                    row.append(bits)
                    bits = n = 0
            if n:
                row.append(bits << (8 - n))
        rows.append(bytes(row).ljust(stride, b"\0"))
    if not topdown:
        rows.reverse()
    data = b"".join(rows)
    comp = 3 if bpp == 32 else 0
    masks = struct.pack("<III", 0xFF0000, 0xFF00, 0xFF)
    pal = b"".join(bytes((b, g, r, 0)) for r, g, b in (palette or []))
    info = struct.pack("<IiiHHIIiiII", header, w, -h if topdown else h, 1, bpp, comp, len(data),
                       2835, 2835, len(palette or []), 0)
    if header == 108:
        info += masks + struct.pack("<I", 0xFF000000) + b"sRGB" + bytes(48)
        extra = b""
    else:
        extra = masks if comp == 3 else b""
    offset = 14 + len(info) + len(extra) + len(pal)
    return b"BM" + struct.pack("<IHHI", offset + len(data), 0, 0, offset) + info + extra + pal + data


def ppm(w, h, pixel, gray=False, maxval=255):
    """A binary PPM (P6), or PGM (P5) if gray: pixel(x, y) is an (r, g, b), or one value."""
    body = bytearray()
    for y in range(h):
        for x in range(w):
            v = pixel(x, y)
            body += bytes([v]) if gray else bytes(v)
    return (b"P5" if gray else b"P6") + b"\n# made by tools/mksamples.py\n" + \
        f"{w} {h}\n{maxval}\n".encode() + bytes(body)


def colors():
    """The test pattern, 320 x 200."""
    w, h = 320, 200
    bars = [(235, 235, 235), (235, 235, 16), (16, 235, 235), (16, 235, 16), (235, 16, 235), (235, 16, 16),
            (16, 16, 235), (16, 16, 16)]

    def px(x, y):
        if y < 100:                                   # eight bars
            return bars[x * 8 // w]
        if y < 124:                                   # a gray ramp
            v = x * 255 // (w - 1)
            return (v, v, v)
        if y < 176:                                   # red, green and blue ramps, then the checkerboard
            band = (y - 124) // 13
            if band < 3 and x < 240:
                v = x * 255 // 239
                return tuple(v if i == band else 0 for i in range(3))
            if x >= 240:
                return (255, 255, 255) if (x + y) % 2 else (0, 0, 0)
            return (40, 40, 48)
        return (40, 40, 48) if (x // 20 + y // 20) % 2 else (70, 72, 84)   # a coarse check at the foot
    return bmp(w, h, px)


def sunset():
    """The scene, 300 x 200."""
    w, h = 300, 200
    horizon = 130

    def px(x, y):
        if y < horizon:
            t = y / horizon
            sky = (int(40 + 215 * t), int(40 + 110 * t), int(110 - 30 * t))
            hill = horizon - 28 * math.exp(-((x - 60) / 55) ** 2) - 16 * math.exp(-((x - 270) / 40) ** 2)
            if y > hill:
                return (48, 40, 70)
            d = math.hypot(x - 190, y - 105)
            if d < 30:
                return (255, 214, 120)
            if d < 40:                                # its glow
                a = (40 - d) / 10
                return tuple(int(s + (g - s) * a * 0.6) for s, g in zip(sky, (255, 190, 110)))
            return sky
        t = (y - horizon) / (h - horizon)
        sea = (int(60 - 30 * t), int(70 - 30 * t), int(120 - 40 * t))
        if abs(x - 190) < 26 * (1 - t * 0.5) and (y // 3) % 2 == 0:   # the sun on the water
            return (230, 170, 100)
        return sea
    return ppm(w, h, px)


SAMPLES = {"colors.bmp": colors, "sunset.ppm": sunset}

if __name__ == "__main__":
    out = sys.argv[1]
    name = os.path.basename(out)
    if name not in SAMPLES:
        sys.exit(f"no sample called {name} (the samples: {', '.join(SAMPLES)})")
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    open(out, "wb").write(SAMPLES[name]())
