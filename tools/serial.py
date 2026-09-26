#!/usr/bin/env python3
"""Watches a Raspberry Pi 4's serial console: the first-boot companion to `make pi-image`.

Finds the USB-serial adapter, opens it at 115200 8N1 (raw), and prints every line the Pi
sends with the host's time and the seconds since the first byte, writing the same to
build/serial-DATE.log. With --keys, what you type goes to the Pi, whose input driver
(user/input.c) reads the UART, so the desktop can be driven over the cable as the browser
console drives it under QEMU. Only Python's standard library.

  tools/serial.py                     watch (Ctrl+C stops)
  tools/serial.py --summary           ... and at the end say where the boot got to
  tools/serial.py --keys              also type into leanos (Ctrl+] stops; Ctrl+C is leanos's copy)
  tools/serial.py --keys --mouse      ... and clicks in this terminal window are the Pi's mouse
  tools/serial.py --list              the serial devices it would pick from
  tools/serial.py --self-test         check it against pseudo-terminals, no Pi needed

Options: --device PATH, --baud N (115200), --log PATH, --until TEXT (stop after a line that
starts with TEXT; exit status 124 if the timeout comes first), --timeout SECONDS,
--screen WxH (the Pi's screen, for --mouse: 1024x600).

The summary reads the kernel's boot steps ("leanos: [n/13] ...", printed before each step,
so the last one is where it stopped; arch/bootcon.c), a panic and its exception registers,
and what came before leanos (the firmware's own log on the bring-up card).
"""
import argparse
import datetime
import glob
import os
import re
import select
import sys
import termios
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Where USB-serial adapters appear: macOS (FTDI, Prolific and CP210x as usbserial or
# SLAB_USBtoUART, CH340 as wchusbserial, CDC-ACM as usbmodem), then Linux.
PATTERNS = ["/dev/cu.usbserial*", "/dev/cu.usbmodem*", "/dev/cu.SLAB_USBtoUART*", "/dev/cu.wchusbserial*",
            "/dev/ttyUSB*", "/dev/ttyACM*"]

STAGE = re.compile(r"^leanos: \[(\d+)/(\d+)\] (.*)$")
LOADED = re.compile(r"kernel8\.img.*?\b(0x[0-9a-fA-F]+)")     # the firmware's log: where it put the kernel
BOOT = "leanos \u00a9 "                 # the first line of every boot
QUIT = 0x1d                              # Ctrl+]

# What each boot step does, to say what probably went wrong when the boot stops in it (the
# names are arch/bootcon.c's, up to the colon).
HINTS = {
    "serial console": "the kernel runs and its UART works; it stopped in the checks right after "
                      "(the kernel stacks' layout)",
    "board": "the firmware's mailbox (board and firmware revisions, the UART clock, the counter, "
             "the ARM's RAM, USB power); its waits are bounded, so a stop here that lasts is a hang "
             "elsewhere. A PANIC about RAM: remove any gpu_mem line from config.txt",
    "Lean runtime": "initializing the Lean runtime and the kernel's Lean code: the heap after the "
                    "image (arch/kernel.ld), or RAM",
    "framebuffer": "the firmware's answer for the screen (the line after the step prints all of it). "
                   "Check the monitor is on HDMI 0, hdmi_force_hotplug=1 in config.txt, and "
                   "start4.elf / fixup4.dat",
    "MMU": "turning on the MMU and the caches: the kernel's page tables or memory attributes",
    "SD card": "EMMC2, the Pi 4's card slot (arch/sd.c): the 'SD:' lines say which command got no "
               "answer. Its waits are bounded, so a stop here that lasts is a bus that hung. Try "
               "another card (plain SDHC, 32 GB or less)",
    "Lean kernel": "the Lean kernel's first state (Lean code and its heap)",
    "memory": "clearing the task frames (20 MiB from 0x4000000) or the SHA-256 self-test",
    "programs": "loading a program or checking its hash; the last 'verified' line names the "
                "program before the one it stopped in",
    "page tables": "writing each task's page tables",
    "interrupts": "the GIC-400 (enable_gic=1 in config.txt) or the timer",
    "cores 1-3": "releasing cores 1-3 through the spin table: a core that never starts does not "
                 "stop core 0, so this is core 0 itself",
    "first task": "the first switch to user mode; the display server draws its boot screen next "
                  "('display:' lines and 'core N up' should follow)",
}


def candidates():
    found = []
    for p in PATTERNS:
        found += sorted(glob.glob(p))
    return found


def pick_device(wait):
    """The adapter's device: the only one, or the newest if several; waits for one to be
    plugged in for up to `wait` seconds."""
    deadline = time.monotonic() + wait
    said = False
    while True:
        found = candidates()
        if found:
            if len(found) > 1:
                found.sort(key=lambda p: os.stat(p).st_mtime)
                print(f"serial.py: several serial devices ({', '.join(found)}); using the newest, "
                      f"{found[-1]} (--device picks another)", file=sys.stderr)
            return found[-1]
        if time.monotonic() > deadline:
            sys.exit("serial.py: no USB-serial adapter found (looked for " + ", ".join(PATTERNS) + "); "
                     "plug it in, or name it with --device")
        if not said:
            print("serial.py: waiting for a USB-serial adapter to be plugged in...", file=sys.stderr)
            said = True
        time.sleep(0.5)


def open_port(path, baud):
    """The device, raw: 8 data bits, no parity, one stop bit, no flow control, no echo."""
    speed = getattr(termios, f"B{baud}", None)
    if speed is None:
        sys.exit(f"serial.py: this system has no {baud} baud")
    try:
        fd = os.open(path, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
    except PermissionError:
        sys.exit(f"serial.py: no permission to open {path}; on Linux, join the dialout group "
                 "(sudo usermod -aG dialout $USER) and log in again")
    except OSError as e:
        sys.exit(f"serial.py: cannot open {path}: {e.strerror}")
    iflag, oflag, cflag, lflag, _, _, cc = termios.tcgetattr(fd)
    iflag = termios.IGNBRK | termios.IGNPAR      # drop breaks and bad bytes (a Pi switched on or off)
    oflag = 0
    cflag = termios.CS8 | termios.CREAD | termios.CLOCAL
    lflag = 0
    cc[termios.VMIN] = 0
    cc[termios.VTIME] = 0
    termios.tcsetattr(fd, termios.TCSANOW, [iflag, oflag, cflag, lflag, speed, speed, cc])
    return fd


class Keys:
    """What this terminal sends, turned into what user/input.c reads: plain bytes are keys;
    the arrows as ESC [ A..D (a terminal in application mode sends ESC O A..D); Backspace as
    127; Enter as a carriage return; a left click or drag, with `screen` set, as ESC m
    d/v/u and x, y in three digits each, scaled from this terminal's cells to the Pi's
    screen (xterm's SGR mouse reports). Other escape sequences and non-ASCII bytes have no
    key in leanos and are dropped. Ctrl+] means quit."""

    def __init__(self, screen=None, size=None):
        self.pending = b""
        self.screen = screen            # (w, h) of the Pi's screen, or None: no mouse
        self.size = size or (lambda: (80, 24))

    def mouse(self, params, final):
        try:
            b, x, y = (int(v) for v in params.split(";"))
        except ValueError:
            return b""
        if not self.screen or b & 64 or (b & 3) != 0:
            return b""                  # only the left button; no wheel
        kind = "u" if final == "m" else "v" if b & 32 else "d"
        cols, rows = self.size()
        w, h = self.screen
        # three digits each: the right edge of a 1024-wide screen is reached at 999
        px = min(w - 1, 999, max(0, int((x - 0.5) * w / cols)))
        py = min(h - 1, 999, max(0, int((y - 0.5) * h / rows)))
        return f"\x1bm{kind}{px:03d}{py:03d}".encode()

    def feed(self, data):
        """Bytes typed -> (bytes for the Pi, quit?)."""
        buf, out, i = self.pending + data, bytearray(), 0
        self.pending = b""
        while i < len(buf):
            c = buf[i]
            if c == QUIT:
                return bytes(out), True
            if c != 0x1b:
                if c == 0x08:
                    out.append(0x7f)
                elif c == 0x0a:
                    out.append(0x0d)
                elif c < 0x80:
                    out.append(c)
                i += 1
                continue
            if i + 1 >= len(buf):               # ESC at the end: wait for what follows
                self.pending = buf[i:]
                break
            n = buf[i + 1]
            if n == ord("O"):                   # ESC O x
                if i + 2 >= len(buf):
                    self.pending = buf[i:]
                    break
                if buf[i + 2] in b"ABCD":
                    out += b"\x1b[" + bytes([buf[i + 2]])
                i += 3
                continue
            if n != ord("["):                   # ESC and a key (Alt+key): the key alone
                i += 1
                continue
            j = i + 2                           # ESC [ params final
            while j < len(buf) and not (0x40 <= buf[j] <= 0x7e):
                j += 1
            if j >= len(buf):
                self.pending = buf[i:]
                break
            params, final = buf[i + 2:j].decode("latin-1"), chr(buf[j])
            if params == "" and final in "ABCD":
                out += b"\x1b[" + final.encode()
            elif params.startswith("<") and final in "Mm":
                out += self.mouse(params[1:], final)
            i = j + 1
        return bytes(out), False


def summarize(lines, received=None):
    """Where the boot got to, from the lines received ((host time, seconds, text) each):
    a list of lines to print."""
    texts = [t for _, _, t in lines]
    out = []
    if received is None:
        received = sum(len(t) + 1 for t in texts)
    if not texts:
        return ["nothing arrived. Check: the cable's RX to the Pi's TX (pin 8), its TX to the Pi's RX "
                "(pin 10), ground to pin 6 (never the 5 V pins); the card has enable_uart=1 in config.txt; "
                "the Pi's green LED says whether the kernel runs at all (docs/SETUP.md, the LED's codes)"]
    bad = sum(1 for t in texts for ch in t if ch == "\ufffd" or (ord(ch) < 32 and ch != "\t"))
    if bad > max(8, sum(len(t) for t in texts) // 5):
        out.append(f"much of what arrived is not text ({bad} bad characters): the baud rate is wrong "
                   "(leanos uses 115200), or the ground wire is missing")
    boots = [i for i, t in enumerate(texts) if t.startswith(BOOT)]
    first = min([i for i, t in enumerate(texts) if t.startswith("leanos")] or [len(texts)])
    if first > 0:
        out.append(f"{first} line(s) before leanos started (the firmware's own log, uart_2ndstage=1); "
                   f"the last: {texts[first - 1]!r}")
        for t in texts[:first]:
            m = LOADED.search(t)
            if m:
                at = int(m.group(1), 16)
                out.append(f"the firmware loaded kernel8.img at {at:#x}" +
                           ("" if at == 0x80000 else ": leanos must be at 0x80000 (kernel_address=0x80000 in "
                                                     "config.txt); elsewhere it only lights the green LED and stops"))
    if not boots and first == len(texts):
        out.append("leanos never printed: the firmware ran (if the lines above are its log) but the kernel "
                   "did not reach its UART. The green LED on and steady: loaded at the wrong address, or "
                   "stopped before its first line; boot the bring-up card (make pi-bringup) to tell which")
        return out
    if len(boots) > 1:
        out.append(f"the Pi booted {len(boots)} times (it restarted, or was switched off and on)")
    start = boots[-1] if boots else first
    last = texts[start:]
    stages = [(k, STAGE.match(t)) for k, t in enumerate(last) if STAGE.match(t)]
    panic = [t for t in last if "PANIC" in t or "exception in the kernel" in t or t.startswith("leanos: stopped ")
             or "a fault while stopping" in t]
    if stages:
        k, m = stages[-1]
        n, total, what = int(m.group(1)), int(m.group(2)), m.group(3)
        if panic:
            out.append(f"the kernel stopped in boot step [{n}/{total}] {what}")
        elif n == total:
            out.append(f"the kernel finished booting: [{n}/{total}] {what}")
        else:
            out.append(f"last boot step reached: [{n}/{total}] {what} (it has not finished: this is where it is, "
                       f"or where it stopped)")
        after = [t for t in last[k + 1:] if not STAGE.match(t)][:6]
        if after and not (n == total and not panic):
            out.append("after it: " + " | ".join(after))
        if n < total and not panic:
            hint = HINTS.get(what.split(":")[0])
            if hint:
                out.append("this step: " + hint)
    else:
        out.append("no boot step lines: an older kernel, or it stopped before its UART was set up")
    for t in panic:
        out.append("stop: " + t)
    if any(t.startswith("display: ") for t in last):
        out.append("the display server is running" +
                   (" and the system settled (idle)" if any(t.startswith("leanos: idle") for t in last) else ""))
    faults = [t for t in last if re.match(r"^leanos: .* stopped: ", t)]
    expected = [t for t in faults if re.match(r"^leanos: (mallory|carol) stopped: ", t)]
    if len(faults) > len(expected):
        out.append("tasks stopped by a fault: " + " | ".join(t for t in faults if t not in expected))
    return out


class Capture:
    """Turns bytes into timestamped lines: printed, logged and kept. A line left without its
    end for a second is printed as it is (a machine that stopped mid-line)."""

    def __init__(self, log, echo):
        self.log, self.echo = log, echo
        self.partial, self.t_partial = b"", None
        self.lines, self.t0, self.received = [], None, 0

    def stamp(self, t):
        host = datetime.datetime.fromtimestamp(t).strftime("%H:%M:%S.%f")[:-3]
        return host, t - self.t0

    def emit(self, raw, t):
        text = raw.replace(b"\r", b"").decode("utf-8", errors="replace")
        host, rel = self.stamp(t)
        self.lines.append((host, rel, text))
        row = f"{host} {rel:+8.3f}  {text}"
        self.echo(row)
        self.log.write(row + "\n")
        self.log.flush()
        return text

    def feed(self, data):
        now = time.time()
        if self.t0 is None:
            self.t0 = now
        self.received += len(data)
        if not self.partial:
            self.t_partial = now
        self.partial += data
        done = []
        while b"\n" in self.partial:
            raw, self.partial = self.partial.split(b"\n", 1)
            done.append(self.emit(raw, self.t_partial))
            self.t_partial = now
        return done

    def idle(self, force=False):
        if self.partial.strip(b"\r") and (force or time.time() - self.t_partial > 1.0):
            text = self.emit(self.partial, self.t_partial)
            self.partial = b""
            return [text]
        return []


def raw_terminal(fd):
    """This terminal, raw for keys but still turning line ends into CR LF for output: the old
    settings, to put back."""
    old = termios.tcgetattr(fd)
    new = termios.tcgetattr(fd)
    new[0] &= ~(termios.IXON | termios.ICRNL | termios.INLCR | termios.IGNCR | termios.ISTRIP | termios.BRKINT)
    new[3] &= ~(termios.ICANON | termios.ECHO | termios.ISIG | termios.IEXTEN)
    new[6][termios.VMIN] = 1
    new[6][termios.VTIME] = 0
    termios.tcsetattr(fd, termios.TCSANOW, new)
    return old


MOUSE_ON = "\x1b[?1000h\x1b[?1002h\x1b[?1006h"
MOUSE_OFF = "\x1b[?1006l\x1b[?1002l\x1b[?1000l"


def run(args):
    path = args.device or pick_device(args.wait)
    fd = open_port(path, args.baud)
    log_path = args.log or os.path.join(ROOT, "build", "serial-" + datetime.datetime.now().strftime("%Y%m%d-%H%M%S") + ".log")
    os.makedirs(os.path.dirname(os.path.abspath(log_path)), exist_ok=True)
    log = open(log_path, "a")
    keys = args.keys and os.isatty(0)
    if args.keys and not keys:
        print("serial.py: --keys needs a terminal on standard input; only watching", file=sys.stderr)
    stdin_old = None
    lines_out = sys.stdout

    def echo(row):
        lines_out.write(row + "\n")
        lines_out.flush()

    cap = Capture(log, echo)
    screen = tuple(int(v) for v in args.screen.lower().split("x")) if args.mouse else None
    translate = Keys(screen, lambda: tuple(os.get_terminal_size(0)))
    how = "Ctrl+] stops; keys go to leanos" if keys else "Ctrl+C stops"
    print(f"serial.py: listening on {path} at {args.baud} 8N1, logging to {log_path} ({how})", file=sys.stderr,
          flush=True)
    status, reason = 0, None
    deadline = time.monotonic() + args.timeout if args.timeout else None
    try:
        if keys:
            stdin_old = raw_terminal(0)
            if args.mouse:
                sys.stdout.write(MOUSE_ON)
                sys.stdout.flush()
        if args.until:
            status = 124
        while True:
            wait = 0.2
            if deadline is not None:
                wait = max(0.0, min(wait, deadline - time.monotonic()))
            ready, _, _ = select.select([fd] + ([0] if keys else []), [], [], wait)
            got = []
            if fd in ready:
                try:
                    data = os.read(fd, 4096)
                except BlockingIOError:
                    data = None
                except OSError as e:
                    reason = f"the serial device went away ({e.strerror})"
                    break
                if data == b"":
                    reason = "the serial device closed"
                    break
                if data:
                    got += cap.feed(data)
            if keys and 0 in ready:
                typed = os.read(0, 1024)
                if not typed:
                    keys = False
                else:
                    out, quit_ = translate.feed(typed)
                    if out:
                        os.write(fd, out)
                    if quit_:
                        reason = "stopped (Ctrl+])"
                        break
            got += cap.idle()
            if args.until and any(t.startswith(args.until) for t in got):
                status = 0
                reason = f"saw {args.until!r}"
                break
            if deadline is not None and time.monotonic() >= deadline:
                reason = f"{args.timeout:g} s passed"
                break
    except KeyboardInterrupt:
        reason = "stopped (Ctrl+C)"
    finally:
        if stdin_old is not None:
            if args.mouse:
                sys.stdout.write(MOUSE_OFF)
                sys.stdout.flush()
            termios.tcsetattr(0, termios.TCSANOW, stdin_old)
        cap.idle(force=True)
        os.close(fd)
    if reason:
        print(f"serial.py: {reason}; {cap.received} bytes, {len(cap.lines)} lines, in {log_path}", file=sys.stderr)
    if args.summary:
        rows = ["", "summary:"] + ["  " + r for r in summarize(cap.lines, cap.received)]
        for r in rows:
            print(r)
        log.write("\n".join(rows) + "\n")
    log.close()
    return status


# ---- the self-test: pseudo-terminals stand in for the cable and for the keyboard ----

def self_test():
    import pty
    import struct
    import subprocess
    import tempfile
    import fcntl

    def check(cond, what):
        if not cond:
            print(f"serial.py: self-test FAILED: {what}")
            sys.exit(1)

    # The key translation.
    k = Keys(screen=(1024, 600), size=lambda: (100, 30))
    check(k.feed(b"hi\r") == (b"hi\r", False), "plain keys")
    check(k.feed(b"\x1b[A\x1bOB\x1b[C\x1b[D") == (b"\x1b[A\x1b[B\x1b[C\x1b[D", False), "arrow keys")
    check(k.feed(b"\x08\x7f\n\t\x03\x16") == (b"\x7f\x7f\r\t\x03\x16", False), "editing and copy/paste keys")
    check(k.feed(b"\x1b[3~\x1b[1;5Ax\xc3\xa9") == (b"x", False), "unknown sequences and non-ASCII dropped")
    check(k.feed(b"\x1b") == (b"", False) and k.feed(b"[") == (b"", False) and k.feed(b"B") == (b"\x1b[B", False),
          "a sequence split across reads")
    check(k.feed(b"\x1b[<0;50;15M") == (b"\x1bmd506290", False), "a click")
    check(k.feed(b"\x1b[<32;100;30M\x1b[<0;1;1m") == (b"\x1bmv999590\x1bmu005010", False), "a drag and release")
    check(k.feed(b"\x1b[<2;5;5M\x1b[<64;5;5M") == (b"", False), "right button and wheel ignored")
    check(Keys().feed(b"\x1b[<0;50;15M") == (b"", False), "no mouse unless asked")
    check(k.feed(b"ab\x1dcd") == (b"ab", True), "Ctrl+] quits")

    # The summary.
    L = lambda *ts: [("00:00:00.000", 0.0, t) for t in ts]
    s = summarize([])
    check(len(s) == 1 and "pin 8" in s[0], "no bytes: wiring advice")
    s = summarize(L("leanos \u00a9 2026 Keith Adler", "leanos: [1/13] serial console: x", "leanos: [3/13] Lean runtime: x",
                    "leanos: [6/13] SD card: EMMC2, then EMMC"))
    check(s[0].startswith("last boot step reached: [6/13] SD card") and any("EMMC2" in r for r in s), f"stuck: {s}")
    s = summarize(L("MESS:00:00:01.0: loading kernel8.img", "leanos \u00a9 2026 Keith Adler", "leanos: [6/13] SD card: x",
                    "leanos: exception in the kernel, kind 2 esr 0x96000045 elr 0x1 far 0x2",
                    "leanos: PANIC: exception in the kernel: data abort", "leanos: stopped in boot step [6/13] SD card: x"))
    check(any(r.startswith("1 line(s) before leanos") for r in s), f"firmware lines: {s}")
    check(any(r.startswith("the kernel stopped in boot step [6/13]") for r in s), f"panic step: {s}")
    check(sum(r.startswith("stop: ") for r in s) == 3, f"panic lines: {s}")
    s = summarize(L("leanos \u00a9 2026 Keith Adler", "leanos: [13/13] first task: x", "leanos: carol stopped: y",
                    "display: boot logo drawn", "leanos: idle, 5 tasks waiting"))
    check(s[0].startswith("the kernel finished booting") and any("settled" in r for r in s)
          and not any("fault" in r for r in s), f"finished: {s}")
    s = summarize(L("MESS:00:00:01.0: Loaded 'kernel8.img' to 0x200000 size 0x100000"))
    check(any("leanos never printed" in r for r in s) and any("at 0x200000: leanos must be at 0x80000" in r for r in s),
          f"firmware only, wrong address: {s}")
    s = summarize(L("MESS:00:00:01.0: Loaded 'kernel8.img' to 0x80000 size 0x100000", "leanos \u00a9 2026 Keith Adler"))
    check(any(r == "the firmware loaded kernel8.img at 0x80000" for r in s), f"firmware, right address: {s}")
    s = summarize(L("\ufffd\ufffd\x01\x02\ufffd" * 10))
    check(any("baud" in r for r in s), f"garbage: {s}")

    tmp = tempfile.mkdtemp(prefix="serial-test-")
    me = os.path.abspath(__file__)

    def ptys():
        m, s = pty.openpty()
        return m, s, os.ttyname(s)

    def read_until(fd, want, timeout=5):
        got, end = b"", time.monotonic() + timeout
        while want not in got and time.monotonic() < end:
            r, _, _ = select.select([fd], [], [], 0.1)
            if r:
                try:
                    got += os.read(fd, 4096)
                except OSError:
                    break
        return got

    def started(proc):
        line = proc.stderr.readline()
        check("listening on" in line, f"the tool did not start: {line!r}")

    # Watching: a boot that stops with a panic, its last line cut off.
    dev_m, dev_s, dev = ptys()
    log = os.path.join(tmp, "watch.log")
    proc = subprocess.Popen([sys.executable, me, "--device", dev, "--summary", "--timeout", "3", "--log", log],
                            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    started(proc)
    check(termios.tcgetattr(dev_s)[2] & termios.CSIZE == termios.CS8, "the port is not 8 bits")
    check(termios.tcgetattr(dev_s)[4] == termios.B115200, "the port is not at 115200 baud")
    boot = ("leanos \u00a9 2026 Keith Adler\r\nleanos: [1/13] serial console: PL011\r\n"
            "leanos: [6/13] SD card: EMMC2, then EMMC\r\nleanos: exception in the kernel, kind 2 esr 0x96000045\r\n"
            "leanos: PANIC: exception in the kernel: data abort\r\nleanos: stopped in boot step [6/13] SD card: EMMC2\r\n"
            "leanos: half a li")
    for chunk in (boot[:30], boot[30:77], boot[77:]):
        os.write(dev_m, chunk.encode())
        time.sleep(0.2)
    out, err = proc.communicate(timeout=10)
    check(proc.returncode == 0, f"watching ended with status {proc.returncode}: {err}")
    rows = out.splitlines()
    check(re.match(r"^\d\d:\d\d:\d\d\.\d{3} +\+\d+\.\d{3}  leanos \u00a9 2026", rows[0] or ""), f"no timestamp: {rows[:1]}")
    check(any(r.endswith("  leanos: half a li") for r in rows), "the cut-off line was not shown")
    check(any("the kernel stopped in boot step [6/13] SD card" in r for r in rows), f"summary: {out}")
    logged = open(log).read()
    check("leanos: [1/13] serial console" in logged and "summary:" in logged, "the log is incomplete")

    # Typing: keys and the mouse from a terminal (a second pseudo-terminal) reach the device.
    dev_m, dev_s, dev = ptys()
    kb_m, kb_s, _ = ptys()
    fcntl.ioctl(kb_s, termios.TIOCSWINSZ, struct.pack("HHHH", 30, 100, 0, 0))
    before = termios.tcgetattr(kb_s)
    proc = subprocess.Popen([sys.executable, me, "--device", dev, "--keys", "--mouse", "--timeout", "8",
                             "--log", os.path.join(tmp, "keys.log")],
                            stdin=kb_s, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    started(proc)
    os.write(kb_m, b"ls\r\x1bOA\x1b[<0;50;15M\x1b[<0;50;15m\x7f")
    want = b"ls\r\x1b[A\x1bmd506290\x1bmu506290\x7f"
    got = read_until(dev_m, want)
    check(got == want, f"keys: sent {want!r}, the device got {got!r}")
    os.write(dev_m, b"display: key 'l' to terminal\r\n")
    time.sleep(0.3)
    os.write(kb_m, bytes([QUIT]))
    out, err = proc.communicate(timeout=10)
    check(proc.returncode == 0 and "stopped (Ctrl+])" in err, f"Ctrl+] did not stop it: {err}")
    check(out.startswith("\x1b[?1000h") and out.rstrip().endswith("\x1b[?1000l"), "mouse reporting not switched on and off")
    check("display: key 'l' to terminal" in out, "a line received while typing was lost")
    after = termios.tcgetattr(kb_s)
    pendin = getattr(termios, "PENDIN", 0)     # a status bit the tty driver sets itself
    after[3] &= ~pendin
    before[3] &= ~pendin
    check(after == before, "the terminal's settings were not put back")

    # --until: stop at a line, status 0; not seen before the timeout: 124.
    for until, status in (("leanos: idle", 0), ("never", 124)):
        dev_m, dev_s, dev = ptys()
        proc = subprocess.Popen([sys.executable, me, "--device", dev, "--until", until, "--timeout", "2",
                                 "--log", os.path.join(tmp, "until.log")],
                                stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        started(proc)
        os.write(dev_m, b"leanos: idle, 5 tasks waiting\r\nmore\r\n")
        proc.communicate(timeout=10)
        check(proc.returncode == status, f"--until {until!r}: status {proc.returncode}, not {status}")
    print("serial.py: self-test ok: keys, arrows and the mouse translated; the summary finds the step, the panic, "
          "firmware lines and bad wiring; a pseudo-terminal at 115200 8N1 is watched, logged, typed into and let go")
    return 0


def main():
    ap = argparse.ArgumentParser(description="Watch (and type into) a Raspberry Pi 4's serial console running leanos.")
    ap.add_argument("--device", help="the serial device (default: the USB-serial adapter plugged in)")
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--keys", action="store_true", help="send what you type to leanos (Ctrl+] stops)")
    ap.add_argument("--mouse", action="store_true", help="with --keys: clicks in this terminal are the Pi's mouse")
    ap.add_argument("--screen", default="1024x600", help="the Pi's screen, for --mouse")
    ap.add_argument("--summary", action="store_true", help="at the end, say where the boot got to")
    ap.add_argument("--until", help="stop after a line starting with this (status 124 if the timeout comes first)")
    ap.add_argument("--timeout", type=float, help="stop after this many seconds")
    ap.add_argument("--wait", type=float, default=600, help="how long to wait for an adapter to be plugged in")
    ap.add_argument("--log", help="the log file (default: build/serial-DATE.log)")
    ap.add_argument("--list", action="store_true", help="list the serial devices found")
    ap.add_argument("--self-test", action="store_true", help="test this tool with pseudo-terminals")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    if args.list:
        for p in candidates():
            print(p)
        return 0
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
