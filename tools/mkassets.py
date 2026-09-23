#!/usr/bin/env python3
"""Builds a task's asset blob: fonts rasterized from TrueType, icons scaled from PNG, and a
wallpaper, in a simple format the user programs read (user/assets.h). Plain Python, no
packages: it carries its own TrueType reader, rasterizer and PNG decoder.

Usage: mkassets.py OUT.bin ITEM...
  font:ID:FILE.ttf:PIXELS        a font at that pixel size (printable ASCII and a few extras)
  icon:ID:FILE.png:PIXELS        a square icon, premultiplied alpha
  image:ID:FILE.png              a picture as it is (the wallpaper)

The blob: "LNAS", version, item count, then per item (kind, id, offset, size), all
little-endian u32. Kinds: 1 font, 2 icon (premultiplied 0xAARRGGBB), 3 image (0x00RRGGBB).
A font: size, ascent, descent, line height, glyph count, then per glyph (codepoint,
advance in 1/64 px, width, height, left bearing, top above the baseline, data offset),
then one byte of coverage per pixel.
"""
import math
import struct
import sys
import zlib

# Characters every font carries: printable ASCII, and © • — λ.
CODEPOINTS = list(range(32, 127)) + [0xA9, 0x2022, 0x2014, 0x3BB]


# ---------------------------------------------------------------- TrueType

class TrueType:
    def __init__(self, path):
        self.data = open(path, "rb").read()
        d = self.data
        num = struct.unpack(">H", d[4:6])[0]
        self.tables = {}
        for i in range(num):
            tag, _, off, length = struct.unpack(">4sIII", d[12 + 16 * i: 28 + 16 * i])
            self.tables[tag.decode()] = (off, length)
        head = self.table("head")
        self.units = struct.unpack(">H", head[18:20])[0]
        self.long_loca = struct.unpack(">h", head[50:52])[0] == 1
        hhea = self.table("hhea")
        self.ascent, self.descent, self.gap = struct.unpack(">hhh", hhea[4:10])
        self.nmetrics = struct.unpack(">H", hhea[34:36])[0]
        self.nglyphs = struct.unpack(">H", self.table("maxp")[4:6])[0]
        self.cmap = self.read_cmap()

    def table(self, tag):
        off, length = self.tables[tag]
        return self.data[off: off + length]

    def read_cmap(self):
        c = self.table("cmap")
        n = struct.unpack(">H", c[2:4])[0]
        best = None
        for i in range(n):
            pid, eid, off = struct.unpack(">HHI", c[4 + 8 * i: 12 + 8 * i])
            fmt = struct.unpack(">H", c[off: off + 2])[0]
            if pid == 3 and eid == 10 and fmt == 12:
                best = (off, fmt)
            elif pid == 3 and eid == 1 and fmt == 4 and best is None:
                best = (off, fmt)
        off, fmt = best
        m = {}
        if fmt == 12:
            groups = struct.unpack(">I", c[off + 12: off + 16])[0]
            for g in range(groups):
                start, end, gid = struct.unpack(">III", c[off + 16 + 12 * g: off + 28 + 12 * g])
                for cp in range(start, end + 1):
                    m[cp] = gid + cp - start
        else:
            segs = struct.unpack(">H", c[off + 6: off + 8])[0] // 2
            ends = struct.unpack(f">{segs}H", c[off + 14: off + 14 + 2 * segs])
            p = off + 16 + 2 * segs
            starts = struct.unpack(f">{segs}H", c[p: p + 2 * segs])
            deltas = struct.unpack(f">{segs}h", c[p + 2 * segs: p + 4 * segs])
            ro_at = p + 4 * segs
            ranges = struct.unpack(f">{segs}H", c[ro_at: ro_at + 2 * segs])
            for s in range(segs):
                for cp in range(starts[s], ends[s] + 1):
                    if cp == 0xFFFF:
                        continue
                    if ranges[s] == 0:
                        gid = (cp + deltas[s]) & 0xFFFF
                    else:
                        at = ro_at + 2 * s + ranges[s] + 2 * (cp - starts[s])
                        gid = struct.unpack(">H", c[at: at + 2])[0]
                        if gid:
                            gid = (gid + deltas[s]) & 0xFFFF
                    m[cp] = gid
        return m

    def advance(self, gid):
        h = self.table("hmtx")
        i = min(gid, self.nmetrics - 1)
        return struct.unpack(">H", h[4 * i: 4 * i + 2])[0]

    def glyph_range(self, gid):
        loca = self.table("loca")
        if self.long_loca:
            a, b = struct.unpack(">II", loca[4 * gid: 4 * gid + 8])
        else:
            a, b = struct.unpack(">HH", loca[2 * gid: 2 * gid + 4])
            a, b = 2 * a, 2 * b
        return a, b

    def contours(self, gid, depth=0):
        """The glyph's outline as closed contours of (x, y, on_curve) points, font units."""
        a, b = self.glyph_range(gid)
        if a == b:
            return []
        g = self.table("glyf")[a:b]
        ncont = struct.unpack(">h", g[0:2])[0]
        if ncont >= 0:
            ends = struct.unpack(f">{ncont}H", g[10: 10 + 2 * ncont])
            npts = ends[-1] + 1 if ncont else 0
            p = 10 + 2 * ncont
            ilen = struct.unpack(">H", g[p: p + 2])[0]
            p += 2 + ilen
            flags = []
            while len(flags) < npts:
                f = g[p]
                p += 1
                flags.append(f)
                if f & 8:
                    r = g[p]
                    p += 1
                    flags.extend([f] * r)
            xs, ys = [], []
            v = 0
            for f in flags:
                if f & 2:
                    dx = g[p]
                    p += 1
                    v += dx if f & 16 else -dx
                elif not f & 16:
                    v += struct.unpack(">h", g[p: p + 2])[0]
                    p += 2
                xs.append(v)
            v = 0
            for f in flags:
                if f & 4:
                    dy = g[p]
                    p += 1
                    v += dy if f & 32 else -dy
                elif not f & 32:
                    v += struct.unpack(">h", g[p: p + 2])[0]
                    p += 2
                ys.append(v)
            out, start = [], 0
            for e in ends:
                out.append([(xs[i], ys[i], bool(flags[i] & 1)) for i in range(start, e + 1)])
                start = e + 1
            return out
        # a composite glyph: other glyphs, moved and scaled
        out, p = [], 10
        while True:
            flags, sub = struct.unpack(">HH", g[p: p + 4])
            p += 4
            if flags & 1:
                dx, dy = struct.unpack(">hh", g[p: p + 4])
                p += 4
            else:
                dx, dy = struct.unpack(">bb", g[p: p + 2])
                p += 2
            m = (1.0, 0.0, 0.0, 1.0)
            if flags & 8:
                s = struct.unpack(">h", g[p: p + 2])[0] / 16384
                p += 2
                m = (s, 0.0, 0.0, s)
            elif flags & 0x40:
                sx, sy = struct.unpack(">hh", g[p: p + 4])
                p += 4
                m = (sx / 16384, 0.0, 0.0, sy / 16384)
            elif flags & 0x80:
                m = tuple(v / 16384 for v in struct.unpack(">hhhh", g[p: p + 8]))
                p += 8
            for c in self.contours(sub, depth + 1):
                out.append([(m[0] * x + m[2] * y + dx, m[1] * x + m[3] * y + dy, on) for x, y, on in c])
            if not flags & 0x20:
                break
        return out


def flatten(contour, scale):
    """Quadratic TrueType contour to straight segments in pixels, y down."""
    pts = [(x * scale, -y * scale, on) for x, y, on in contour]
    n = len(pts)
    if n == 0:
        return []
    # start on an on-curve point (or the midpoint of two off-curve points)
    start = next((i for i in range(n) if pts[i][2]), None)
    if start is None:
        a, b = pts[0], pts[1]
        pts.insert(0, ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2, True))
        n += 1
        start = 0
    pts = pts[start:] + pts[:start]
    segs = []
    cur = pts[0][:2]
    i = 1
    while i <= n:
        p = pts[i % n]
        if p[2]:
            segs.append((cur, p[:2]))
            cur = p[:2]
            i += 1
        else:
            nxt = pts[(i + 1) % n]
            end = nxt[:2] if nxt[2] else ((p[0] + nxt[0]) / 2, (p[1] + nxt[1]) / 2)
            steps = 8
            prev = cur
            for k in range(1, steps + 1):
                t = k / steps
                x = (1 - t) ** 2 * cur[0] + 2 * (1 - t) * t * p[0] + t * t * end[0]
                y = (1 - t) ** 2 * cur[1] + 2 * (1 - t) * t * p[1] + t * t * end[1]
                segs.append((prev, (x, y)))
                prev = (x, y)
            cur = end
            i += 2 if nxt[2] else 1
    return segs


def rasterize(segs, w, h, ox, oy, sub=5):
    """Coverage 0..255 per pixel: nonzero winding, `sub` scanlines per pixel, exact
    horizontal coverage at span ends."""
    cov = [0.0] * (w * h)
    for sy in range(h * sub):
        y = sy / sub + 0.5 / sub
        hits = []
        for (x0, y0), (x1, y1) in segs:
            y0, y1 = y0 - oy, y1 - oy
            if y0 == y1 or not (min(y0, y1) <= y < max(y0, y1)):
                continue
            x = x0 + (y - y0) * (x1 - x0) / (y1 - y0) - ox
            hits.append((x, 1 if y1 > y0 else -1))
        hits.sort()
        wind = 0
        row = (sy // sub) * w
        for k in range(len(hits) - 1):
            wind += hits[k][1]
            if wind == 0:
                continue
            a, b = hits[k][0], hits[k + 1][0]
            a, b = max(a, 0.0), min(b, float(w))
            if b <= a:
                continue
            ia, ib = int(a), int(b)
            if ia == ib:
                cov[row + ia] += (b - a) / sub
                continue
            cov[row + ia] += (ia + 1 - a) / sub
            for px in range(ia + 1, min(ib, w)):
                cov[row + px] += 1 / sub
            if ib < w:
                cov[row + ib] += (b - ib) / sub
    return bytes(min(255, int(round(c * 255))) for c in cov)


def font_blob(path, px):
    tt = TrueType(path)
    scale = px / tt.units
    glyphs, data = [], bytearray()
    for cp in CODEPOINTS:
        gid = tt.cmap.get(cp, 0)
        contours = tt.contours(gid)
        segs = [s for c in contours for s in flatten(c, scale)]
        adv = int(round(tt.advance(gid) * scale * 64))
        if segs:
            xs = [x for s in segs for x, _ in s]
            ys = [y for s in segs for _, y in s]
            x0, x1 = math.floor(min(xs)), math.ceil(max(xs))
            y0, y1 = math.floor(min(ys)), math.ceil(max(ys))
            w, h = x1 - x0, y1 - y0
            bitmap = rasterize(segs, w, h, x0, y0)
        else:
            w = h = x0 = y0 = 0
            bitmap = b""
        glyphs.append((cp, adv, w, h, x0, -y0, len(data)))
        data += bitmap
    ascent = int(round(tt.ascent * scale))
    descent = int(round(-tt.descent * scale))
    line = int(round((tt.ascent - tt.descent + tt.gap) * scale))
    out = struct.pack("<5I", px, ascent, descent, line, len(glyphs))
    for g in glyphs:
        out += struct.pack("<IiHHhhI", *g)
    return out + bytes(data)


# ---------------------------------------------------------------- PNG

def read_png(path):
    d = open(path, "rb").read()
    assert d[:8] == b"\x89PNG\r\n\x1a\n", path
    p, idat = 8, b""
    while p < len(d):
        length, kind = struct.unpack(">I4s", d[p: p + 8])
        body = d[p + 8: p + 8 + length]
        if kind == b"IHDR":
            w, h, depth, ctype, _, _, interlace = struct.unpack(">IIBBBBB", body)
            assert depth == 8 and ctype in (2, 6) and interlace == 0, (path, depth, ctype, interlace)
        elif kind == b"IDAT":
            idat += body
        p += 12 + length
    bpp = 4 if ctype == 6 else 3
    raw = zlib.decompress(idat)
    stride = w * bpp
    pixels = bytearray()
    prev = bytearray(stride)
    at = 0
    for _ in range(h):
        f = raw[at]
        line = bytearray(raw[at + 1: at + 1 + stride])
        at += 1 + stride
        for i in range(stride):
            a = line[i - bpp] if i >= bpp else 0
            b = prev[i]
            c = prev[i - bpp] if i >= bpp else 0
            if f == 1:
                line[i] = (line[i] + a) & 255
            elif f == 2:
                line[i] = (line[i] + b) & 255
            elif f == 3:
                line[i] = (line[i] + (a + b) // 2) & 255
            elif f == 4:
                pa, pb, pc = abs(b - c), abs(a - c), abs(a + b - 2 * c)
                pr = a if pa <= pb and pa <= pc else b if pb <= pc else c
                line[i] = (line[i] + pr) & 255
        pixels += line
        prev = line
    rgba = []
    for i in range(w * h):
        px = pixels[i * bpp: i * bpp + bpp]
        rgba.append(tuple(px) if bpp == 4 else (px[0], px[1], px[2], 255))
    return w, h, rgba


def icon_blob(path, size):
    w, h, px = read_png(path)
    out = []
    for y in range(size):
        for x in range(size):
            # average the source pixels under this one, premultiplied
            sx0, sx1 = x * w // size, max((x + 1) * w // size, x * w // size + 1)
            sy0, sy1 = y * h // size, max((y + 1) * h // size, y * h // size + 1)
            r = g = b = a = n = 0
            for yy in range(sy0, sy1):
                for xx in range(sx0, sx1):
                    pr, pg, pb, pa = px[yy * w + xx]
                    r += pr * pa
                    g += pg * pa
                    b += pb * pa
                    a += pa
                    n += 1
            A = a // n
            R, G, B = (r // (255 * n), g // (255 * n), b // (255 * n)) if n else (0, 0, 0)
            out.append((A << 24) | (R << 16) | (G << 8) | B)
    return struct.pack("<II", size, size) + struct.pack(f"<{len(out)}I", *out)


def image_blob(path):
    w, h, px = read_png(path)
    return struct.pack("<II", w, h) + struct.pack(f"<{w * h}I", *[(r << 16) | (g << 8) | b for r, g, b, _ in px])


# ---------------------------------------------------------------- the blob

def main():
    out, specs = sys.argv[1], sys.argv[2:]
    items = []
    for spec in specs:
        kind, ident, rest = spec.split(":", 2)
        if kind == "font":
            path, px = rest.rsplit(":", 1)
            items.append((1, int(ident), font_blob(path, int(px))))
        elif kind == "icon":
            path, px = rest.rsplit(":", 1)
            items.append((2, int(ident), icon_blob(path, int(px))))
        elif kind == "image":
            items.append((3, int(ident), image_blob(rest)))
        else:
            sys.exit(f"unknown item: {spec}")
    header = b"LNAS" + struct.pack("<II", 1, len(items))
    table_len = 16 * len(items)
    offset = len(header) + table_len
    table, body = b"", b""
    for kind, ident, blob in items:
        pad = (-(offset + len(body))) % 16
        body += b"\0" * pad
        table += struct.pack("<IIII", kind, ident, offset + len(body), len(blob))
        body += blob
    open(out, "wb").write(header + table + body)


if __name__ == "__main__":
    main()
