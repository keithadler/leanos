#!/bin/bash
# The first-boot kit without a Pi: tools/serial.py's self-test (pseudo-terminals for the cable
# and the keyboard), then QEMU's Pi 4 with its serial port on a pseudo-terminal, watched by
# serial.py as it would watch a USB-serial cable: every boot step is announced in order,
# before the display server takes over, and the summary finds the finished boot. Then keys
# typed into serial.py reach Notes through the UART and the input driver.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

python3 tools/serial.py --self-test || fail "serial.py's self-test"

cp build/sd-template.img "$T/sd-serial.img"
python3 - "$T" <<'PY' || fail "serial.py did not watch and drive leanos over a pseudo-terminal"
import os, pty, re, select, struct, subprocess, sys, tempfile, time, fcntl, termios
sys.path.insert(0, "test")
from run import Qmp
T = sys.argv[1]
sock = os.path.join(tempfile.mkdtemp(prefix="leanos-"), "qmp.sock")
# -S: stopped until serial.py has the pseudo-terminal open, so no line is lost
qemu = subprocess.Popen(["qemu-system-aarch64", "-M", "raspi4b", "-display", "none", "-serial", "pty", "-S",
                         "-semihosting", "-qmp", f"unix:{sock},server,nowait", "-kernel", "build/kernel8.img",
                         "-drive", f"if=sd,format=raw,file={T}/sd-serial.img"],
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
qmp = None
try:
    said = qemu.stdout.readline()
    m = re.search(r"char device redirected to (/dev/\S+)", said)
    assert m, f"QEMU did not say where its serial port is: {said!r}"
    qmp = Qmp(sock)
    kb_m, kb_s = pty.openpty()           # the keyboard: a terminal serial.py reads keys from
    fcntl.ioctl(kb_s, termios.TIOCSWINSZ, struct.pack("HHHH", 30, 100, 0, 0))
    log = os.path.join(T, "serial.log")
    tool = subprocess.Popen([sys.executable, "tools/serial.py", "--device", m.group(1), "--keys", "--summary",
                             "--until", "display: key 'i' to alice", "--timeout", "60", "--log", log],
                            stdin=kb_s, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    assert "listening on" in tool.stderr.readline(), "serial.py did not start"
    time.sleep(1.5)                      # QEMU looks for a reader on the terminal once a second
    qmp.cmd("cont")
    out, typed = [], False
    end = time.monotonic() + 60
    while time.monotonic() < end:
        line = tool.stdout.readline()
        if not line:
            break
        out.append(line.rstrip("\n"))
        if not typed and "  leanos: idle" in line:
            os.write(kb_m, b"Hi")        # typed at the terminal, sent down the serial line
            typed = True
    tool.wait(timeout=10)
    text = [re.sub(r"^\d\d:\d\d:\d\d\.\d{3} +[+-]\d+\.\d{3}  ", "", l) for l in out]
    print("\n".join("  | " + l for l in out if "leanos" in l or l.startswith("  ") or "summary" in l))
    assert tool.returncode == 0, f"serial.py ended with status {tool.returncode}"
    assert all(re.match(r"^\d\d:\d\d:\d\d\.\d{3} +\+\d+\.\d{3}  ", l) for l in out if l and not l.startswith(("summary", "  "))), \
        "a line without its timestamps"
    stages = [l for l in text if l.startswith("leanos: [")]
    want = [f"leanos: [{n}/13] " for n in range(1, 14)]
    assert [s[:len(w)] for s, w in zip(stages, want)] == want and len(stages) == 13, f"boot steps: {stages}"
    first_task = text.index(stages[-1])
    assert not any(l.startswith(("display:", "leanos: core")) for l in text[:first_task]), \
        "something ran before the last boot step"
    assert text[0].startswith("leanos \u00a9 2026"), f"the first line: {text[0]!r}"
    assert "display: key 'H' to alice" in text and "display: key 'i' to alice" in text, "the keys did not reach Notes"
    assert "  the kernel finished booting: [13/13] first task: the display server takes the screen" in out, "summary"
    assert "  the display server is running and the system settled (idle)" in out, "summary: idle"
    logged = open(log).read()
    assert "leanos: [6/13] SD card" in logged and "summary:" in logged, "the log file"
    print("ok: serial.py watched QEMU's Pi 4 through a pseudo-terminal: 13 boot steps in order, each before "
          "the tasks ran, the summary found the finished boot, and keys typed into it reached Notes")
finally:
    if qmp:
        qmp.cmd("quit")
    try:
        qemu.wait(timeout=10)
    except subprocess.TimeoutExpired:
        qemu.kill()
PY
