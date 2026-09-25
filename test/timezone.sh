#!/bin/bash
# The time zone. A time server on the host (NTP, as in test/net.sh) says it is 2026-12-31
# 20:00:00 UTC, and Terminal's ntp sets the kernel's time from it. Clock runs; Settings steps
# the time zone up to UTC+5:30 and down to UTC-3:30. The display server shows the menu bar's
# clock in each zone at once, Clock follows within a second, and Apps saves the choice on the
# card. Each program logs the local time it shows beside the Unix time it read, so the check
# below needs no real clock: it works out what each should show, the date turning over at
# local midnight included (UTC+5:30 is already 2027 there). Then the Pi starts again from the
# same card: Apps gives the display the saved zone at boot, and Settings, Clock and the menu
# bar show it.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }

ntp_port=$((20000 + RANDOM % 20000))
python3 - $ntp_port <<'NTP' &
import socket, struct, sys
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind(("127.0.0.1", int(sys.argv[1])))
when = 1798747200 + 2208988800           # 2026-12-31 20:00:00 UTC, in NTP's seconds since 1900
while True:
    q, a = s.recvfrom(512)
    if len(q) >= 48 and q[0] & 7 == 3:
        s.sendto(bytes([0x24, 2, 6, 0xec]) + bytes(20) + q[40:48] + struct.pack(">IIII", when, 0, when, 0), a)
NTP
ntp=$!
trap 'kill $ntp 2>/dev/null; wait $ntp 2>/dev/null' EXIT
sleep 1

# Settings is the fourth window (Notes, Terminal, Clock, Settings), at the display's fourth
# cascade place, pushed up off the dock: its pixels start at (216, 166). The stepper's - and
# + are at (318 + 17, 62) and (318 + 138 - 17, 62) in them.
out=$(NTP=$ntp_port python3 - <<'PY'
import os, sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK, TEST_CARD
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
MINUS, PLUS = (216 + 335, 166 + 62), (216 + 439, 166 + 62)
first = [wait_for("usb: network: ", 2), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys(f"ntp 10.0.2.2:{os.environ['NTP']}\r"), wait_for("terminal: ntp"),
         wait_for("display: time zone UTC; the menu bar"),
         *keys("run clock\r"), wait_for("clock: in UTC it is"),
         *click(*DOCK["Settings"]), wait_for("settings: time zone UTC")]
for i in range(8):                  # UTC+1, +2, +3, +3:30, +4, +4:30, +5, +5:30
    first += [*click(*PLUS), wait_for("display: time zone UTC+", i + 1)]
first += [wait_for("clock: in UTC+5:30 it is"), wait_for("apps: saved the time zone, UTC+5:30")]
for i in range(12):                 # +5, +4:30, +4, +3:30, +3, +2, +1, UTC, -1, -2, -3, -3:30
    first += [*click(*MINUS), wait_for("settings: time zone set to", 8 + i + 1)]
first += [wait_for("clock: in UTC-3:30 it is"), wait_for("apps: saved the time zone, UTC-3:30"),
          *click(216 + 64, 166 + 62)]    # then Indigo, the background already chosen: a last line
status = boot(240, net=True, steps=first, until="settings: background set to Indigo", settle=1.5)
print("--- restart ---", flush=True)
if status:
    sys.exit(status)
# The same card again: the zone comes back from it before anyone touches anything.
again = [wait_for("usb: network: ", 2), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *keys(f"ntp 10.0.2.2:{os.environ['NTP']}\r"), wait_for("terminal: ntp"),
         *keys("run clock\r"), wait_for("clock: in "),
         *click(*DOCK["Settings"]), wait_for("settings: time zone UTC")]
sys.exit(boot(240, net=True, sd=TEST_CARD, steps=again, until="settings: time zone UTC", settle=1.5))
PY
)
status=$?
echo "$out" | grep -E "^(--- restart|terminal: ntp|settings: time zone|display: (time zone|start Apps)|apps: (saved|time zone)|clock: in )" \
  | sed "s/:$ntp_port/:NTP/; s/^/  | /"
[ $status -eq 0 ] || fail "the runs did not finish (status $status)"
first=$(echo "$out" | sed '/^--- restart ---$/q')
again=$(echo "$out" | sed '1,/^--- restart ---$/d')

echo "$first" | grep -qx "terminal: ntp 10.0.2.2:$ntp_port -> 2026-12-31 20:00:00 UTC" || fail "the time server's time was not set"

# Settings steps through real zones, one click each, and the display takes each one.
steps=$(echo "$first" | grep "^settings: time zone")
expected=$(printf 'settings: time zone %s\n' UTC; for z in +1 +2 +3 +3:30 +4 +4:30 +5 +5:30 +5 +4:30 +4 +3:30 \
  +3 +2 +1 "" -1 -2 -3 -3:30; do echo "settings: time zone set to UTC$z -> ok"; done)
[ "$steps" = "$expected" ] || { echo "got:"; echo "$steps"; fail "Settings did not step through the zones"; }
[ "$(echo "$first" | grep -c "^display: time zone .*, as Settings asked; the menu bar shows ")" = 20 ] \
  || fail "the display did not take every zone Settings chose"

# What the menu bar and Clock show is the time they read, in the zone they name.
python3 - "$first" "$again" <<'CHECK' || fail "the menu bar or Clock showed the wrong local time"
import re, sys, datetime
first, again = sys.argv[1], sys.argv[2]
def zone(z):
    m = re.fullmatch(r"UTC(?:([+-])(\d+)(?::(\d\d))?)?", z)
    assert m, z
    return 0 if not m.group(1) else (1 if m.group(1) == "+" else -1) * (int(m.group(2)) * 60 + int(m.group(3) or 0))
def local(t, z):
    return datetime.datetime(1970, 1, 1) + datetime.timedelta(seconds=t + zone(z) * 60)
def bar(d):
    return f"{d:%a %b} {d.day}  {d:%H:%M}"
checked = {"bar": 0, "clock": 0}
for text in (first, again):
    for m in re.finditer(r"^display: time zone (\S+?)(?:, [^;]*)?; the menu bar shows (.*) at Unix time (\d+)$", text, re.M):
        z, shown, t = m.group(1), m.group(2), int(m.group(3))
        assert shown == bar(local(t, z)), (m.group(0), bar(local(t, z)))
        checked["bar"] += 1
    for m in re.finditer(r"^clock: in (\S+) it is (.*) \(Unix time (\d+)\)$", text, re.M):
        z, shown, t = m.group(1), m.group(2), int(m.group(3))
        assert shown == f"{local(t, z):%Y-%m-%d %H:%M:%S}", (m.group(0), local(t, z))
        checked["clock"] += 1
assert checked["bar"] >= 22 and checked["clock"] >= 4, checked
# The time server's time (a moment after 20:00 UTC on December 31): half past one on New
# Year's Day in UTC+5:30, half past four the afternoon before in UTC-3:30.
for who, line in (("the menu bar", r"display: time zone UTC\+5:30, as Settings asked; the menu bar shows Fri Jan 1  01:3\d at"),
                  ("the menu bar", r"display: time zone UTC-3:30, as Settings asked; the menu bar shows Thu Dec 31  16:3\d at"),
                  ("Clock", r"clock: in UTC\+5:30 it is 2027-01-01 01:3\d:\d\d "),
                  ("Clock", r"clock: in UTC-3:30 it is 2026-12-31 16:3\d:\d\d ")):
    assert re.search("^" + line, first, re.M), (who, line)
print(f"ok: {checked['bar']} menu bar times and {checked['clock']} Clock times match their zones")
CHECK

# The last choice was saved on the card, and came back after the restart.
echo "$first" | grep -E "^apps: saved the time zone" | tail -1 | grep -qx "apps: saved the time zone, UTC-3:30, in timezone.txt -> ok" \
  || fail "Apps did not save the last zone"
echo "$again" | grep -qx "apps: time zone UTC-3:30, from timezone.txt -> ok" || fail "Apps did not read the zone back"
echo "$again" | grep -qE "^display: time zone UTC-3:30, saved on the card; " || fail "the display did not take the saved zone"
echo "$again" | grep -qE "^display: time zone UTC-3:30(, saved on the card)?; the menu bar shows " \
  || fail "the menu bar did not show the saved zone"
echo "$again" | grep -qE "^clock: in UTC-3:30 it is 2026-12-31 16:3[0-9]:[0-9][0-9] " || fail "Clock did not show the saved zone"
echo "$again" | grep -qx "settings: time zone UTC-3:30" || fail "Settings did not show the saved zone"
echo "$again" | grep -q "^apps: saved" && fail "Apps saved a zone nobody changed"

echo "$out" | grep -q "PANIC" && fail "kernel panicked"
echo "$out" | grep -qE "SHOULD NOT|CHANGED" && fail "a protection failed"
echo "ok: the time zone applies at once to the menu bar and Clock, and survives a restart"
