#!/usr/bin/env python3
"""Boots leanos on QEMU's Raspberry Pi 4 and prints its serial console.

When the kernel reports it is idle (tasks waiting, nothing to run), the screen is captured
through QEMU's control socket to build/screen.ppm and build/screen.png, and QEMU is told to
quit. If the machine powers itself off instead, there is no screen to capture.

Usage: test/run.py [timeout-seconds]    (exit status: QEMU's, or 124 on timeout)
"""
import json
import os
import socket
import struct
import subprocess
import sys
import tempfile
import time
import zlib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMAGE = os.path.join(ROOT, "build", "kernel8.img")


def ppm_to_png(ppm_path, png_path):
    data = open(ppm_path, "rb").read()
    magic, dims, maxval, pixels = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    rows = b"".join(b"\0" + pixels[y * w * 3:(y + 1) * w * 3] for y in range(h))

    def chunk(kind, body):
        c = struct.pack(">I", len(body)) + kind + body
        return c + struct.pack(">I", zlib.crc32(kind + body) & 0xffffffff)

    png = b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
    png += chunk(b"IDAT", zlib.compress(rows, 9)) + chunk(b"IEND", b"")
    open(png_path, "wb").write(png)


class Qmp:
    def __init__(self, path):
        for _ in range(100):
            try:
                self.sock = socket.socket(socket.AF_UNIX)
                self.sock.connect(path)
                break
            except OSError:
                time.sleep(0.05)
        self.f = self.sock.makefile("rw")
        self.f.readline()
        self.cmd("qmp_capabilities")

    def cmd(self, name, **args):
        msg = {"execute": name}
        if args:
            msg["arguments"] = args
        self.f.write(json.dumps(msg) + "\n")
        self.f.flush()
        while True:
            line = self.f.readline()
            if not line:
                return None
            reply = json.loads(line)
            if "return" in reply or "error" in reply:
                return reply


def boot(timeout=30, on_line=print, on_screen=None):
    sock = os.path.join(tempfile.mkdtemp(prefix="leanos-"), "qmp.sock")
    proc = subprocess.Popen(
        ["qemu-system-aarch64", "-M", "raspi4b", "-display", "none", "-serial", "stdio",
         "-semihosting", "-qmp", f"unix:{sock},server,nowait", "-kernel", IMAGE],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    qmp = Qmp(sock)
    deadline = time.monotonic() + timeout
    status = None
    try:
        for raw in proc.stdout:
            line = raw.decode(errors="replace").rstrip("\r\n")
            if line:
                on_line(line)
            if line.startswith("leanos: idle"):
                ppm = os.path.join(ROOT, "build", "screen.ppm")
                qmp.cmd("screendump", filename=ppm)
                png = os.path.join(ROOT, "build", "screen.png")
                ppm_to_png(ppm, png)
                if on_screen:
                    on_screen(png)
                qmp.cmd("quit")
                status = 0
                break
            if time.monotonic() > deadline:
                status = 124
                break
    finally:
        if proc.poll() is None:
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
    return proc.returncode if status is None else status


if __name__ == "__main__":
    sys.exit(boot(float(sys.argv[1]) if len(sys.argv) > 1 else 30))
