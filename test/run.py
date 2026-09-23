#!/usr/bin/env python3
"""Boots leanos on QEMU's Raspberry Pi 4 (headless) and prints its serial console.

When the kernel reports it is idle (tasks waiting, nothing to run), the optional input is
typed into the Pi's serial line, one step at a time; after the last step the runner waits
for the line it names. Then the screen is captured through QEMU's control socket to
build/screen.ppm and build/screen.png, and QEMU is told to quit. If the machine powers
itself off instead, there is no screen to capture.

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


def mouse(kind, x, y):
    """A mouse report for the input driver: kind is 'd' (down), 'u' (up) or 'v' (moved)."""
    return f"\x1bm{kind}{x:03d}{y:03d}".encode()


def wait_for(prefix):
    """A step that types nothing: it waits until a serial line starts with `prefix`."""
    return ("wait", prefix)


def blank_card(path=os.path.join(ROOT, "build", "sd-test.img"), size=8 * 1024 * 1024):
    """A blank SD card image (the file server formats it on first boot)."""
    with open(path, "wb") as f:
        f.truncate(size)
    return path


def boot(timeout=30, on_line=print, on_screen=None, steps=(), until=None, snaps=None, image=None,
         settle=0.3, sd=None):
    """sd: the SD card image to boot with (a fresh blank one if None; "" for no card)."""
    if sd is None:
        sd = blank_card()
    """steps: bytes to type once the system is idle, each followed by a short pause, or
    wait_for(prefix) steps, which wait for a serial line.
    until: after the steps, wait for a serial line starting with this before the capture.
    snaps: {line prefix: file name}: also capture the screen, without stopping, when a line
    starting with that prefix appears."""
    sock = os.path.join(tempfile.mkdtemp(prefix="leanos-"), "qmp.sock")
    proc = subprocess.Popen(
        ["qemu-system-aarch64", "-M", "raspi4b", "-display", "none", "-serial", "stdio",
         "-semihosting", "-qmp", f"unix:{sock},server,nowait", "-kernel", image or IMAGE]
        + (["-drive", f"if=sd,format=raw,file={sd}"] if sd else []),
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    qmp = Qmp(sock)
    deadline = time.monotonic() + timeout
    status = None
    waiting_for = None
    import threading
    seen = []
    cond = threading.Condition()

    def capture():
        ppm = os.path.join(ROOT, "build", "screen.ppm")
        qmp.cmd("screendump", filename=ppm)
        png = os.path.join(ROOT, "build", "screen.png")
        ppm_to_png(ppm, png)
        if on_screen:
            on_screen(png)
        qmp.cmd("quit")

    try:
        for raw in proc.stdout:
            line = raw.decode(errors="replace").rstrip("\r\n")
            if line:
                on_line(line)
                with cond:
                    seen.append(line)
                    cond.notify_all()
            for prefix, name in (snaps or {}).items():
                if line.startswith(prefix):
                    ppm = os.path.join(ROOT, "build", name + ".ppm")
                    qmp.cmd("screendump", filename=ppm)
                    ppm_to_png(ppm, os.path.join(ROOT, "build", name + ".png"))
            if waiting_for and line.startswith(waiting_for):
                time.sleep(settle)   # let the display finish drawing
                capture()
                status = 0
                break
            if line.startswith("leanos: idle") and steps:
                def type_steps():
                    for chunk in steps:
                        if isinstance(chunk, tuple):
                            with cond:
                                cond.wait_for(lambda: any(l.startswith(chunk[1]) for l in seen),
                                              timeout=max(0, deadline - time.monotonic()))
                            time.sleep(0.2)
                            continue
                        proc.stdin.write(chunk)
                        proc.stdin.flush()
                        time.sleep(0.15)
                threading.Thread(target=type_steps, daemon=True).start()
                waiting_for = until or "\0"
                continue
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


# The interaction `make test` performs: type into the focused Notes window, then drag it by
# its title bar.
DEMO_STEPS = [b"H", b"i", b"!", mouse("v", 120, 88), mouse("d", 120, 88), mouse("v", 200, 150),
              mouse("v", 300, 220), mouse("u", 300, 220)]

# The apps: type into Notes, close it and start it again (the note is back, from the file
# server); start Terminal from the dock, ask it things and write a file; pick a background in
# Settings; close Terminal with its red button and start it again; open Files and show the
# new file; then open Security.
def keys(s):
    return [c.encode() for c in s]


def click(x, y):
    return [mouse("d", x, y), mouse("u", x, y)]


APP_STEPS = [*keys("Hi"), *click(114, 91), wait_for("alice: window closed"),
             *click(376, 548), wait_for("alice: opened"),
             *click(512, 548), wait_for("terminal: opened"),
             *keys("caps\r"), wait_for("terminal: caps"), *keys("boot\r"), wait_for("terminal: boot"),
             *keys("write hello.txt Hello from Terminal\r"), wait_for("terminal: write"),
             *keys("ls\r"), wait_for("terminal: ls"),
             *click(580, 548), wait_for("settings: opened"),
             *click(362, 268), wait_for("settings: background"),
             *click(154, 127), wait_for("terminal: window closed"),
             mouse("v", 300, 300), *click(512, 548), wait_for("terminal: opened"),
             *keys("caps\r"), wait_for("terminal: caps"),
             *click(444, 548), wait_for("files: opened"),
             *click(306, 311), wait_for("files: showing hello.txt"),
             *click(648, 548), wait_for("security: 10")]

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    demo = "--demo" in sys.argv
    apps = "--apps" in sys.argv
    image = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--image=")), None)
    steps = DEMO_STEPS if demo else APP_STEPS if apps else ()
    # --keep-sd: boot with the card the last run left (build/sd-test.img); --no-sd: no card
    sd = os.path.join(ROOT, "build", "sd-test.img") if "--keep-sd" in sys.argv else "" if "--no-sd" in sys.argv else None
    until = "display: moved" if demo else "security: 10" if apps else None
    sys.exit(boot(float(args[0]) if args else 30, steps=steps, until=until,
                  snaps={"display: boot logo drawn": "logo"}, image=image, settle=2 if apps else 0.3, sd=sd))
