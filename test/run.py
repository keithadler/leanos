#!/usr/bin/env python3
"""Boots leanos on QEMU's Raspberry Pi 4 (headless) and prints its serial console.

When the kernel reports it is idle (tasks waiting, nothing to run), the optional input is
typed into the Pi's serial line, one step at a time; after the last step the runner waits
for the line it names. Then the screen is captured through QEMU's control socket to
screen.ppm and screen.png, and QEMU is told to quit. If the machine powers itself off
instead, there is no screen to capture.

Every file a run makes (the screens, the test card) goes in one folder: $LEANOS_TEST_DIR,
or build/ when it is not set. test/all.py gives each test its own, so tests run at once.

Usage: test/run.py [timeout-seconds]    (exit status: QEMU's, or 124 on timeout)
"""
import json
import os
import re
import socket
import struct
import subprocess
import sys
import tempfile
import time
import zlib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMAGE = os.path.join(ROOT, "build", "kernel8.img")
# Where this run's files go (a relative path is from the top of the project).
SCRATCH = os.path.join(ROOT, os.environ.get("LEANOS_TEST_DIR") or "build")
os.makedirs(SCRATCH, exist_ok=True)


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
    """A mouse report for the input driver: kind is 'd' (down), 'u' (up) or 'v' (moved).
    Three digits each: x and y up to 999."""
    return f"\x1bm{kind}{x:03d}{y:03d}".encode()


def usb_key(qcode, shift=False, ctrl=False):
    """Steps that press and release a key on the USB keyboard (a QEMU qcode: "a", "ret", ...),
    with Shift or Control held if asked."""
    mods = (["shift"] if shift else []) + (["ctrl"] if ctrl else [])
    down = lambda d: ("qmp", "input-send-event", {"events":
                      [{"type": "key", "data": {"down": d, "key": {"type": "qcode", "data": m}}} for m in mods] +
                      [{"type": "key", "data": {"down": d, "key": {"type": "qcode", "data": qcode}}}]})
    return [down(True), down(False)]


def usb_mouse(dx=0, dy=0, button=None):
    """A step that moves the USB mouse by (dx, dy), or presses (True) or releases (False) its left button."""
    if button is not None:
        return ("qmp", "input-send-event", {"events":
                [{"type": "btn", "data": {"down": button, "button": "left"}}]})
    return ("qmp", "input-send-event", {"events":
            [{"type": "rel", "data": {"axis": "x", "value": dx}}, {"type": "rel", "data": {"axis": "y", "value": dy}}]})


def usb_touch(x, y, down=None):
    """A step that puts the USB tablet at screen position (x, y) (1024 x 600), touching
    (down=True) or not (False), or only moving (None)."""
    ev = [{"type": "abs", "data": {"axis": "x", "value": x * 0x7fff // 1023}},
          {"type": "abs", "data": {"axis": "y", "value": y * 0x7fff // 599}}]
    if down is not None:
        ev.append({"type": "btn", "data": {"down": down, "button": "left"}})
    return ("qmp", "input-send-event", {"events": ev})


# Where each dock icon's center is (user/display.c: DOCK_X + DOCK_PAD + ICON / 2 + 66 i).
DOCK = {name: (215 + 66 * i, 548) for i, name in enumerate(
    ["Notes", "Files", "Terminal", "Settings", "Security", "Apps", "Clock", "Calculator", "Tour", "Web"])}


# Where the display put each window: it logs "display: NAME opened a WxH window at X,Y from
# ..., its window N" (NAME: the app, or the card file a program came from; N only for a
# program's second window on), and "display: moved NAME's window to (X, Y)" after a drag.
OPENED = re.compile(r"^display: (.+?) opened a (\d+)x(\d+) window at (\d+),(\d+) from a read-only "
                    r"capability to \d+ pages(?:, its window (\d+))?$")
MOVED = re.compile(r"^display: moved (.+?)'s window to \((-?\d+), (-?\d+)\)(?:, its window (\d+))?$")
# Where to click in a window, from its top-left corner: its close button, its title bar.
CLOSE = (18, 15)
TITLE_H = 30


def window_pos(lines, name, win=0):
    """The top-left corner (x, y) of window `win` of `name` (as the display's log names it),
    where the display last put it: from the serial lines so far (a list, or the whole text),
    or None if it has not opened."""
    if isinstance(lines, str):
        lines = lines.splitlines()
    pos = None
    for line in lines:
        m = OPENED.match(line)
        if m and m.group(1) == name and int(m.group(6) or 0) == win:
            pos = (int(m.group(4)), int(m.group(5)))
            continue
        m = MOVED.match(line)
        if m and pos and m.group(1) == name and int(m.group(4) or 0) == win:
            pos = (int(m.group(2)), int(m.group(3)))
    return pos


def wmouse(kind, name, dx, dy, win=0):
    """A mouse report (as mouse()) at (dx, dy) from the top-left corner of `name`'s window
    `win`, where the display's log last put it when the step runs (it waits for the window
    to open). A drag's steps all count from where the window was when it began: the log says
    where it went only when the button comes up."""
    return ("win", kind, name, win, dx, dy)


def wclick(name, dx, dy, win=0):
    """A click at (dx, dy) from the top-left corner of `name`'s window (wmouse)."""
    return [wmouse("d", name, dx, dy, win), wmouse("u", name, dx, dy, win)]


# The title bar's buttons of the window in front, lit (the display draws every other window's
# gray): red, yellow and green, 20 px apart.
LIGHTS = (b"\xff\x5f\x57", b"\xfe\xbc\x2e", b"\x28\xc8\x40")


def lit_button(ppm_path, which):
    """Where the lit yellow (which=1) or green (2) button is on a screen capture, or None: the
    first pixel of the red one with the other two 20 and 40 px to its right."""
    data = open(ppm_path, "rb").read()
    magic, dims, maxval, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    at = px.find(LIGHTS[0])
    while at >= 0:
        if at % 3 == 0:
            x, y = at // 3 % w, at // 3 // w
            if x + 40 < w and all(px[at + 60 * i:at + 60 * i + 3] == LIGHTS[i] for i in (1, 2)):
                return x + 20 * which, y
        at = px.find(LIGHTS[0], at + 1)
    return None


def screen_click(find):
    """A step that captures the screen and clicks where find(path of the capture, a PPM) says:
    (x, y), or no click for None."""
    return ("screen", find)


def front_button(which):
    """A step that clicks the yellow (minimize) or green (zoom) button of the window in front,
    found on the screen as it is then; no click if no window is in front."""
    n = {"yellow": 1, "green": 2}[which]
    return screen_click(lambda ppm: lit_button(ppm, n))


def wait_for(prefix, times=1):
    """A step that types nothing: it waits until `times` serial lines start with `prefix`."""
    return ("wait", prefix, times)


def pause(seconds):
    """A step that types nothing for that long (for what must happen late)."""
    return ("sleep", seconds)


def snap(name):
    """A step that captures the screen, without stopping, to NAME.ppm and NAME.png."""
    return ("snap", name)


TEST_CARD = os.path.join(SCRATCH, "sd-test.img")


def blank_card(path=TEST_CARD):
    """A card with a partition table and an empty data partition (the file server formats
    it on first boot)."""
    subprocess.run([sys.executable, os.path.join(ROOT, "tools", "mksd.py"), path, "--blank"], check=True)
    return path


def raw_card(path=TEST_CARD, size=8 * 1024 * 1024):
    """A card with no partition table at all: the kernel must not write anywhere on it."""
    with open(path, "wb") as f:
        f.truncate(size)
    return path


def fresh_card(path=TEST_CARD):
    """A copy of the card `make` builds: welcome.txt and the programs (tools/mksd.py)."""
    import shutil
    shutil.copyfile(os.path.join(ROOT, "build", "sd-template.img"), path)
    return path


def boot(timeout=30, on_line=print, on_screen=None, steps=(), until=None, snaps=None, image=None,
         settle=0.3, sd=None, usb=False, cut=False, net=False, touch=False, clock_from=None):
    """sd: the SD card image to boot with (a fresh copy of the programs card if None; ""
    for no card). cut: at the timeout, kill QEMU at once (a power cut), not after a grace.
    clock_from: count the timeout from the first serial line starting with this, not from
    QEMU's start (so a slow boot on a busy host does not eat into it); until that line
    comes, the run may take up to a minute more."""
    if sd is None:
        sd = fresh_card()
    """steps: bytes to type once the system is idle, each followed by a short pause, or
    wait_for(prefix) steps, which wait for a serial line.
    until: after the steps, wait for a serial line starting with this before the capture.
    snaps: {line prefix: file name}: also capture the screen, without stopping, when a line
    starting with that prefix appears."""
    sock = os.path.join(tempfile.mkdtemp(prefix="leanos-"), "qmp.sock")
    proc = subprocess.Popen(
        ["qemu-system-aarch64", "-M", "raspi4b", "-display", "none", "-serial", "stdio",
         "-semihosting", "-qmp", f"unix:{sock},server,nowait", "-kernel", image or IMAGE]
        + (["-drive", f"if=sd,format=raw,file={sd}"] if sd else [])
        # usb: a USB keyboard and mouse on the DWC2 (QEMU puts them behind a hub)
        + (["-device", "usb-kbd,id=kbd", "-device", "usb-mouse,id=mouse"] if usb else [])
        # net: a USB network adapter on QEMU's user network (10.0.2.0/24; the host is 10.0.2.2)
        + (["-device", "usb-net,netdev=n0", "-netdev", "user,id=n0"] if net else [])
        # touch: an absolute pointer, as a touchscreen is (QEMU's tablet)
        + (["-device", "usb-tablet,id=tablet"] if touch else []),
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    qmp = Qmp(sock)
    deadline = [time.monotonic() + timeout + (60 if clock_from else 0)]
    # The loop below only looks at the clock when a line arrives; a machine that goes
    # silent would hang it. A watchdog ends QEMU at the deadline instead.
    import threading as _threading
    def watchdog():
        while proc.poll() is None:
            if time.monotonic() > deadline[0] + (0 if cut else 5):
                proc.kill()
                return
            time.sleep(0.5)
    _threading.Thread(target=watchdog, daemon=True).start()
    status = None
    waiting_for = None
    import threading
    seen = []
    cond = threading.Condition()

    def capture():
        ppm = os.path.join(SCRATCH, "screen.ppm")
        qmp.cmd("screendump", filename=ppm)
        png = os.path.join(SCRATCH, "screen.png")
        ppm_to_png(ppm, png)
        if on_screen:
            on_screen(png)
        qmp.cmd("quit")

    try:
        for raw in proc.stdout:
            line = raw.decode(errors="replace").rstrip("\r\n")
            if line:
                if clock_from and line.startswith(clock_from):
                    deadline[0] = time.monotonic() + timeout
                    clock_from = None
                on_line(line)
                with cond:
                    seen.append(line)
                    cond.notify_all()
            for prefix, name in (snaps or {}).items():
                if line.startswith(prefix):
                    ppm = os.path.join(SCRATCH, name + ".ppm")
                    qmp.cmd("screendump", filename=ppm)
                    ppm_to_png(ppm, os.path.join(SCRATCH, name + ".png"))
            if waiting_for and line.startswith(waiting_for):
                time.sleep(settle)   # let the display finish drawing
                capture()
                status = 0
                break
            if line.startswith("leanos: idle") and steps and waiting_for is None:
                def type_steps():
                    for chunk in steps:
                        if isinstance(chunk, tuple) and chunk[0] == "qmp":
                            reply = qmp.cmd(chunk[1], **chunk[2])
                            if isinstance(reply, dict) and "error" in reply:
                                print("run.py: QMP", chunk[1], "failed:", reply["error"], flush=True)
                            time.sleep(0.05)
                            continue
                        if isinstance(chunk, tuple) and chunk[0] == "sleep":
                            time.sleep(chunk[1])
                            continue
                        if isinstance(chunk, tuple) and chunk[0] == "win":
                            _, kind, name, win, dx, dy = chunk
                            with cond:
                                cond.wait_for(lambda: window_pos(seen, name, win) is not None,
                                              timeout=max(0, deadline[0] - time.monotonic()))
                                pos = window_pos(seen, name, win)
                            if pos is None:
                                print(f"run.py: no window of {name} (its window {win}) in the log", flush=True)
                                return
                            x, y = pos[0] + dx, pos[1] + dy
                            if not (0 <= x <= 999 and 0 <= y <= 999):
                                print(f"run.py: ({x}, {y}) in {name}'s window is past what a mouse report can say", flush=True)
                                return
                            chunk = mouse(kind, x, y)
                        if isinstance(chunk, tuple) and chunk[0] == "screen":
                            time.sleep(0.2)             # what the last step changed, drawn
                            ppm = os.path.join(SCRATCH, "find.ppm")
                            qmp.cmd("screendump", filename=ppm)
                            pos = chunk[1](ppm)
                            if pos is None or pos[0] > 999:
                                continue
                            for kind in "du":
                                try:
                                    proc.stdin.write(mouse(kind, *pos))
                                    proc.stdin.flush()
                                except (BrokenPipeError, ValueError, OSError):
                                    return
                                time.sleep(0.1)
                            continue
                        if isinstance(chunk, tuple) and chunk[0] == "snap":
                            ppm = os.path.join(SCRATCH, chunk[1] + ".ppm")
                            qmp.cmd("screendump", filename=ppm)
                            ppm_to_png(ppm, os.path.join(SCRATCH, chunk[1] + ".png"))
                            continue
                        if isinstance(chunk, tuple):
                            with cond:
                                cond.wait_for(lambda: sum(l.startswith(chunk[1]) for l in seen) >= chunk[2],
                                              timeout=max(0, deadline[0] - time.monotonic()))
                            time.sleep(0.05)
                            continue
                        try:
                            proc.stdin.write(chunk)
                            proc.stdin.flush()
                        except (BrokenPipeError, ValueError, OSError):
                            return                      # QEMU is gone (a cut, a timeout)
                        # QEMU holds what the UART cannot take yet, so no key is lost: keys
                        # go fast. Mouse reports keep a hand's pace, so a drag is drawn one
                        # move at a time, as the drawing-speed check expects.
                        time.sleep(0.1 if chunk.startswith(b"\x1bm") else 0.02)
                threading.Thread(target=type_steps, daemon=True).start()
                waiting_for = until or "\0"
                continue
            if line.startswith("leanos: idle") and waiting_for is None:
                ppm = os.path.join(SCRATCH, "screen.ppm")
                qmp.cmd("screendump", filename=ppm)
                png = os.path.join(SCRATCH, "screen.png")
                ppm_to_png(ppm, png)
                if on_screen:
                    on_screen(png)
                qmp.cmd("quit")
                status = 0
                break
            if time.monotonic() > deadline[0]:
                status = 124
                break
    finally:
        try:
            proc.stdin.close()                  # QEMU may be gone already: nothing to say
        except (BrokenPipeError, OSError, ValueError):
            pass
        if proc.poll() is None:
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
    return proc.returncode if status is None else status


# The interaction `make test` performs: type into the focused Notes window, wait for Notes
# to save the note, then drag the window by its title bar, 180 px right and 132 down.
DEMO_DRAG = (180, 132)
DEMO_STEPS = [b"H", b"i", b"!", wait_for("alice: saved note 1 (3 bytes)"), wmouse("v", "alice", 24, 12), wmouse("d", "alice", 24, 12),
              wmouse("v", "alice", 104, 74), wmouse("v", "alice", 24 + DEMO_DRAG[0], 12 + DEMO_DRAG[1]),
              wmouse("u", "alice", 24 + DEMO_DRAG[0], 12 + DEMO_DRAG[1])]

# The apps: type into Notes, close it and start it again (the note is back, from the file
# server); start Terminal from the dock, ask it things and write a file; pick a background in
# Settings; close Terminal with its red button and start it again; open Files and show the
# new file; then open Security.
def keys(s):
    return [c.encode() for c in s]


def click(x, y):
    return [mouse("d", x, y), mouse("u", x, y)]


APP_STEPS = [*keys("Hi"), *wclick("alice", *CLOSE), wait_for("alice: window closed"),
             *click(*DOCK["Notes"]), wait_for("alice: opened", 2), pause(0.5), snap("notes-again"),
             *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
             *keys("caps\r"), wait_for("terminal: caps"), *keys("boot\r"), wait_for("terminal: boot"),
             *keys("write hello.txt Hello from Terminal\r"), wait_for("terminal: write"),
             *keys("ls\r"), wait_for("terminal: ls"), *keys("ls -a\r"), wait_for("terminal: ls -a"),
             *click(*DOCK["Settings"]), wait_for("settings: opened"),
             *wclick("Settings", 160, TITLE_H + 62), wait_for("settings: background"),         # Graphite
             *wclick("Settings", 387, TITLE_H + 166), wait_for("settings: the firmware reports"),   # 600 MHz
             *wclick("Settings", 351, TITLE_H + 300), wait_for("settings: activity light"),    # on
             *wclick("Terminal", *CLOSE), wait_for("terminal: window closed"),
             mouse("v", 300, 300), *click(*DOCK["Terminal"]), wait_for("terminal: opened", 2),
             *keys("caps\r"), wait_for("terminal: caps"),
             b"write fast.txt 0123456789abcdefghijklmnopqrstuvwxyz\r", wait_for("terminal: write fast.txt"),
             b"cat fast.txt\r", wait_for("terminal: cat fast.txt"),
             b"run welcome.txt\r", wait_for("terminal: run welcome.txt"),
             b"run hello\r", wait_for("hello: opened"),
             *keys("abc"),
             *wclick("Terminal", 230, 280), b"run clock\r", wait_for("clock: ticked 3 times"),
             *click(*DOCK["Files"]), wait_for("files: opened"),
             *[b"\x1b[B"] * 13, wait_for("files: showing hello.txt"),
             *click(*DOCK["Security"]), wait_for("security: 13")]

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    demo = "--demo" in sys.argv
    apps = "--apps" in sys.argv
    image = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--image=")), None)
    steps = DEMO_STEPS if demo else APP_STEPS if apps else ()
    # --keep-sd: boot with the card the last run left (sd-test.img); --no-sd: no card
    sd = (TEST_CARD if "--keep-sd" in sys.argv else "" if "--no-sd" in sys.argv
          else blank_card() if "--blank-sd" in sys.argv else raw_card() if "--raw-sd" in sys.argv else None)
    until = "display: the drag drew" if demo else "security: 13" if apps else None
    sys.exit(boot(float(args[0]) if args else 30, steps=steps, until=until,
                  snaps={"leanos: [13/13]": "console", "display: boot logo drawn": "logo"}, image=image, settle=2 if apps else 0.3, sd=sd))
