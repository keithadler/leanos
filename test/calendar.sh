#!/bin/bash
# The calendar (user/progs/calendar.c), from Terminal, on one card booted twice.
#
#   1. The date math first, without a Pi: user/date.h's leap_year, month_days, days_of and
#      weekday_of, compiled for this machine, against Python's calendar for every month of
#      the years 1 to 9999, and against date_of (the same algorithm run backward) from 1970.
#      (date.h brings lib.h, whose system calls are arm64 code: on another host this part is
#      skipped, and says so.)
#   2. The Pi with no network, so no time server: calendar says the date is not set, shows
#      January 2026 and no today. Terminal then writes apps/calendar/events.txt by hand: two
#      events, out of order, and two lines that are not events (words, and February 30th).
#      Started again, calendar reads the two and skips the two.
#   3. The same card, with the network and a time server on the host (as test/timezone.sh
#      has) that says it is 2027-12-30 12:00 UTC. Calendar is open before Terminal's ntp sets
#      the kernel's time (if pool.ntp.org answered at boot, it shows that day first); within
#      a second of it, calendar selects 2027-12-30. The keys and the buttons go through the
#      months: Right into 2028, Page Down to February 2028 (29 days), End, Down into March, Up,
#      Home, Left, Page Up back into 2027; the arrow buttons into November and forward into
#      January again; a click on a day, and on a day of the next month in the last row; the
#      Today button and T. Then on 2027-12-30, Return and a line of text add one event, the
#      New event button another, and N and Escape add none; the first one's x deletes it,
#      and on 2027-12-31 Tab and Delete delete the event from the file.
#
# Checked in the log: each month shown, with its number of days and the weekday of its 1st,
# against Python's calendar; each day selected, as the keys and clicks must move it. On the
# screen, by pixels: today's blue at 2027-12-30's cell (and nowhere without a date), the
# selected day's shade, the grid's number of days of the month (dark numbers; the others'
# are dimmed), the title between the arrows (the same for the same month, different for
# another), the marks under days with events, the rows in the panel. Last, events.txt is read
# off the card image: the two events left, sorted by date, the bad lines gone.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }
rm -f "$T"/cal-*.ppm "$T"/cal-*.png

# 1. The date math.
case "$(uname -m)" in
arm64 | aarch64)
  if command -v xcrun >/dev/null; then CC="xcrun clang"; else CC=$(command -v clang || command -v cc) || fail "no C compiler for the host"; fi
  cat > "$T/dates.c" <<'C'
#include "date.h"
#include <stdio.h>
/* Every month of the years 1 to 9999: year, month, days, the weekday of its 1st, its day number. */
int main(void) {
    int bad = 0;
    for (long y = 1; y <= 9999; y++)
        for (int m = 1; m <= 12; m++) {
            long k = days_of(y, m, 1), next = m == 12 ? days_of(y + 1, 1, 1) : days_of(y, m + 1, 1);
            printf("%ld %d %d %d %ld\n", y, m, month_days(y, m), weekday_of(k), k);
            if (days_of(y, m, month_days(y, m)) + 1 != next || next - k != month_days(y, m)) bad++;
            if (k >= 0) {
                struct date d = date_of((u64)k * 86400);
                if (d.year != y || d.month != m || d.day != 1 || d.weekday != weekday_of(k)) bad++;
            }
        }
    fprintf(stderr, "%d\n", bad);
    return bad != 0;
}
C
  $CC -std=gnu11 -O1 -Wall -Werror -Wno-unused-function -Iuser -o "$T/dates" "$T/dates.c" || fail "the date math did not compile"
  "$T/dates" > "$T/dates.txt" 2> "$T/dates-bad.txt" || fail "days_of and date_of disagree ($(cat "$T/dates-bad.txt") months)"
  python3 - "$T/dates.txt" <<'PY' || fail "the date math is wrong"
import calendar, datetime, sys
epoch = datetime.date(1970, 1, 1).toordinal()
n = 0
for line in open(sys.argv[1]):
    y, m, days, wd, k = map(int, line.split())
    first, length = calendar.monthrange(y, m)            # Monday 0
    assert days == length, (y, m, days, length)
    assert wd == (first + 1) % 7, (y, m, wd, first)       # Sunday 0
    assert k == datetime.date(y, m, 1).toordinal() - epoch, (y, m, k)
    n += 1
assert n == 9999 * 12, n
print(f"ok: {n} months, 1 to 9999: their lengths, the weekday of each 1st and the day numbers match Python's calendar")
PY
  ;;
*) echo "skipped: the date math on the host (date.h brings lib.h, which is arm64 code; this is $(uname -m))" ;;
esac

ntp_port=$((20000 + RANDOM % 20000))
python3 - $ntp_port <<'NTP' &
import socket, struct, sys
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind(("127.0.0.1", int(sys.argv[1])))
when = 1830168000 + 2208988800           # 2027-12-30 12:00:00 UTC, in NTP's seconds since 1900
while True:
    q, a = s.recvfrom(512)
    if len(q) >= 48 and q[0] & 7 == 3:
        s.sendto(bytes([0x24, 2, 6, 0xec]) + bytes(20) + q[40:48] + struct.pack(">IIII", when, 0, when, 0), a)
NTP
ntp=$!
trap 'kill $ntp 2>/dev/null; wait $ntp 2>/dev/null' EXIT
sleep 1

# Where things are in calendar's window, below its title bar (user/progs/calendar.c): the
# grid's cells 46 x 32 from (14, 70); the arrows at (14, 14) and (306, 14), 30 x 26; Today at
# (522, 14); the panel's rows 22 high from y 74, each with its x 13 px from its right end at
# x 582; New event at (360, 238).
out=$(NTP=$ntp_port python3 - <<'PY'
import os, sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, wclick, pause, snap, usb_key, fresh_card, CLOSE, DOCK, TITLE_H, TEST_CARD
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
keys = lambda s: [c.encode() for c in s]
line = lambda s: [s.encode() + b"\r"]
UP, DOWN, RIGHT, LEFT = b"\x1b[A", b"\x1b[B", b"\x1b[C", b"\x1b[D"
HOME, END, DELETE, PGUP, PGDN = b"\x1b[H", b"\x1b[F", b"\x1b[3~", b"\x1b[5~", b"\x1b[6~"
cal = lambda x, y: wclick("calendar", x, TITLE_H + y)
cell = lambda i: cal(14 + i % 7 * 46 + 23, 70 + i // 7 * 32 + 16)
PREV, NEXT, TODAY, NEW = cal(29, 27), cal(321, 27), cal(550, 27), cal(460, 251)
cross = lambda r: cal(569, 74 + 22 * r + 11)
seen = {}
def after(prefix):
    """Wait for the next line starting with prefix (counting those before)."""
    seen[prefix] = seen.get(prefix, 0) + 1
    return wait_for(prefix, seen[prefix])
def sel(day):
    return after("calendar: selected " + day)
FILE = "apps/calendar/events.txt"

# 2. No network: the date is not set. Then events.txt, by hand.
fresh_card()
first = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *line("run calendar"), wait_for("calendar: opened a window"), pause(0.5), snap("cal-unset"),
         *wclick("calendar", *CLOSE), wait_for("calendar: window closed"), *click(*DOCK["Terminal"])]
for text in ("2027-12-31 New Years Eve dinner", "not an event", "2027-02-30 no such day", "2027-12-24 Christmas Eve"):
    first += [*line(f"echo {text} >> {FILE}"), after("terminal: >> " + FILE)]
first += [*line("run calendar")]
status = boot(90, steps=first, until="calendar: read 2 events", settle=0.5)
print("--- with a time server ---", flush=True)
if status:
    sys.exit(status)

# 3. The same card, the network and a time server: today, the months, and events.
seen.clear()
steps = [wait_for("usb: ready"), wait_for("usb: network: ", 2), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         *line("run calendar"), wait_for("calendar: opened a window"), *click(*DOCK["Terminal"]),
         *line(f"ntp 10.0.2.2:{os.environ['NTP']}"), wait_for("terminal: ntp"),
         wait_for("calendar: today is 2027-12-30 in UTC"), sel("2027-12-30"),
         *cal(100, -15), pause(0.5), snap("cal-today"),
         RIGHT, sel("2027-12-31"), RIGHT, sel("2028-01-01"), pause(0.5), snap("cal-jan"),
         PGDN, sel("2028-02-01"), pause(0.5), snap("cal-feb"),
         END, sel("2028-02-29"), DOWN, sel("2028-03-07"), UP, sel("2028-02-29"), HOME, sel("2028-02-01"),
         LEFT, sel("2028-01-31"), PGUP, sel("2027-12-31"),
         *PREV, sel("2027-11-30"), *NEXT, sel("2027-12-30"), *NEXT, sel("2028-01-30"), pause(0.5), snap("cal-jan-click"),
         *cell(19), sel("2028-01-15"), *cell(41), sel("2028-02-06"),
         *TODAY, sel("2027-12-30"), PGDN, sel("2028-01-30"), b"t", sel("2027-12-30"),
         b"\r", after("calendar: typing an event for 2027-12-30"), *keys("Dentist at 9:30"), b"\r",
         after("calendar: saved"),
         *NEW, after("calendar: typing an event for 2027-12-30"), *keys("New Year party"), b"\r", after("calendar: saved"),
         b"n", after("calendar: typing an event for 2027-12-30"), *keys("nope"), *usb_key("esc"),
         after("calendar: no event added"), pause(0.5), snap("cal-events"),
         *cross(0), after("calendar: saved"),
         RIGHT, sel("2027-12-31"), b"\t", DELETE, after("calendar: saved"), LEFT, sel("2027-12-30"),
         pause(0.5), snap("cal-final"), *wclick("calendar", *CLOSE)]
sys.exit(boot(150, net=True, usb=True, sd=TEST_CARD, steps=steps, until="calendar: window closed", settle=0.3))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(--- |calendar: |terminal: (ntp|run calendar|>>))" | sed "s/:$ntp_port/:NTP/; s/^/  | /"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
first=$(echo "$out" | sed '/^--- with a time server ---$/q')
second=$(echo "$out" | sed '1,/^--- with a time server ---$/d')

# The log: the months shown are the calendar's, and the days selected where the keys and
# clicks must take them.
python3 - "$first" "$second" <<'CHECK' || fail "the calendar showed the wrong month or selected the wrong day"
import calendar, re, sys
first, second = sys.argv[1], sys.argv[2]
names = list(calendar.month_name)
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
months = 0
for m in re.finditer(r"^calendar: showing (\w+) (\d+), (\d+) days from a (\w+)$", first + "\n" + second, re.M):
    y, mo = int(m.group(2)), names.index(m.group(1))
    wd, n = calendar.monthrange(y, mo)
    assert int(m.group(3)) == n and m.group(4) == days[wd], (m.group(0), n, days[wd])
    months += 1
for want in ("calendar: no events yet (apps/calendar/events.txt is new)",
             "calendar: the date is not set (no time server has answered)",
             "calendar: showing January 2026, 31 days from a Thursday",
             "calendar: read 2 events from apps/calendar/events.txt, skipped 2 lines that are not one"):
    assert want in first.splitlines(), ("missing, with no network:", want)
assert "calendar: today is" not in first, "a date with no time server"
assert "calendar: read 2 events from apps/calendar/events.txt, skipped 2 lines that are not one" in second.splitlines()
after_ntp = second.split("calendar: today is 2027-12-30 in UTC\n", 1)
assert len(after_ntp) == 2, "calendar did not take the time server's date"
selected = re.findall(r"^calendar: selected (\S+)$", after_ntp[1], re.M)
expected = ["2027-12-30",                                         # the time server's today
            "2027-12-31", "2028-01-01", "2028-02-01", "2028-02-29",   # Right, Right, Page Down, End
            "2028-03-07", "2028-02-29", "2028-02-01", "2028-01-31",   # Down, Up, Home, Left
            "2027-12-31", "2027-11-30", "2027-12-30", "2028-01-30",   # Page Up, <, >, >
            "2028-01-15", "2028-02-06",                               # a day, a day of the next month
            "2027-12-30", "2028-01-30", "2027-12-30",                 # Today, Page Down, T
            "2027-12-31", "2027-12-30"]                               # Right, Left
assert selected == expected, ("selected", selected)
events = [l for l in after_ntp[1].splitlines() if re.match(r"calendar: (added|deleted|saved|no event|typing)", l)]
assert events == ["calendar: typing an event for 2027-12-30",
                  "calendar: added an event on 2027-12-30: Dentist at 9:30",
                  "calendar: saved 3 events in apps/calendar/events.txt (84 bytes) -> ok",
                  "calendar: typing an event for 2027-12-30",
                  "calendar: added an event on 2027-12-30: New Year party",
                  "calendar: saved 4 events in apps/calendar/events.txt (110 bytes) -> ok",
                  "calendar: typing an event for 2027-12-30",
                  "calendar: no event added (Escape)",
                  "calendar: deleted an event on 2027-12-30: Dentist at 9:30",
                  "calendar: saved 3 events in apps/calendar/events.txt (83 bytes) -> ok",
                  "calendar: deleted an event on 2027-12-31: New Years Eve dinner",
                  "calendar: saved 2 events in apps/calendar/events.txt (51 bytes) -> ok"], events
before = after_ntp[0].splitlines()
start = "with the date not set" if "calendar: the date is not set (no time server has answered)" in before else \
    "on " + next(l.split()[3] for l in before if l.startswith("calendar: today is")) + " (pool.ntp.org answered at boot)"
print(f"ok: calendar started {start}, and went to the time server's 2027-12-30 when Terminal's ntp set it")
print(f"ok: {months} months shown, each with Python's number of days and weekday of the 1st; "
      f"{len(selected)} days selected as the keys and clicks go; 2 events added, 1 cancelled, 2 deleted")
CHECK

# The screen.
python3 - "$T" "$first" "$second" <<'PIX' || fail "the calendar drew the wrong thing"
import calendar, os, sys
sys.path.insert(0, "test")
from run import window_pos, TITLE_H
T, first, second = sys.argv[1], sys.argv[2], sys.argv[3]
ACCENT, SEL, DOT, WARN, WHITE, BG, PANEL = (58, 110, 230), (222, 231, 252), (236, 128, 52), (190, 104, 16), \
    (255, 255, 255), (252, 252, 253), (242, 243, 247)
def load(name, log):
    wx, wy = window_pos(log, "calendar")
    data = open(os.path.join(T, name + ".ppm"), "rb").read()
    _, dims, _, px = data.split(b"\n", 3)
    w, h = map(int, dims.split())
    def at(x, y):
        i = ((wy + TITLE_H + y) * w + wx + x) * 3
        return tuple(px[i:i + 3])
    return at
def cell(i):
    return 14 + i % 7 * 46, 70 + i // 7 * 32
def dark_days(at):
    """The cells whose number is drawn dark: the month's own days (not today's, white on blue)."""
    return sum(any(sum(at(x, y)) < 250 for y in range(y0 + 6, y0 + 24) for x in range(x0 + 10, x0 + 36))
               for x0, y0 in map(cell, range(42)))
def today_cells(at):
    return [i for i in range(42) if at(cell(i)[0] + 8, cell(i)[1] + 16) == ACCENT]
def selected(at):
    return [i for i in range(42) if at(cell(i)[0] + 3, cell(i)[1] + 16) == SEL]
def title(at):
    return bytes(v for y in range(14, 42) for x in range(46, 304) for v in at(x, y))
def grid_col(y, m, d):
    return calendar.monthrange(y, m)[0] + d - 1         # Monday first, the 1st in the first week

unset = load("cal-unset", first)
assert today_cells(unset) == [], ("a today with no date", today_cells(unset))
assert not any(unset(x, y) == ACCENT for y in range(70, 262, 2) for x in range(14, 336, 2)), "blue in the grid with no date"
assert dark_days(unset) == 31, ("January 2026's days", dark_days(unset))
assert selected(unset) == [grid_col(2026, 1, 1)], ("January 1st, 2026, selected", selected(unset))
assert any(unset(x, y) == WARN for y in range(52, 68) for x in range(364, 580)), "no note that the date is not set"

shots = {n: load(n, second) for n in ("cal-today", "cal-jan", "cal-feb", "cal-jan-click", "cal-events", "cal-final")}
today = shots["cal-today"]
assert today_cells(today) == [grid_col(2027, 12, 30)], ("today's cell", today_cells(today), grid_col(2027, 12, 30))
assert selected(today) == [grid_col(2027, 12, 30)], ("today selected", selected(today))
assert dark_days(today) == 30, ("December 2027's days, and today", dark_days(today))
jan, feb = shots["cal-jan"], shots["cal-feb"]
assert dark_days(jan) == 31 and dark_days(feb) == 29, ("January and February 2028's days", dark_days(jan), dark_days(feb))
assert today_cells(jan) == [3], ("December 30th in January's first week", today_cells(jan))
assert today_cells(feb) == [], today_cells(feb)
assert selected(jan) == [grid_col(2028, 1, 1)] and selected(feb) == [grid_col(2028, 2, 1)], (selected(jan), selected(feb))
t = {n: title(at) for n, at in shots.items()}
assert t["cal-jan"] == t["cal-jan-click"], "January 2028's title, by key and by click"
assert t["cal-today"] == t["cal-final"], "December 2027's title, twice"
assert len({t["cal-today"], t["cal-jan"], t["cal-feb"]}) == 3, "the same title for different months"
assert all(any(sum(c) < 250 for c in zip(*[iter(t[n])] * 3)) for n in t), "no title"

def dot(at, day):
    x0, y0 = cell(grid_col(2027, 12, day))
    return at(x0 + 23, y0 + 26)
def row(at, r):
    return at(560, 74 + 22 * r + 3)
ev, fin = shots["cal-events"], shots["cal-final"]
assert (dot(ev, 30), dot(ev, 31), dot(ev, 24), dot(ev, 23)) == (WHITE, DOT, DOT, BG), \
    ("the marks under the days with events", dot(ev, 30), dot(ev, 31), dot(ev, 24), dot(ev, 23))
assert (row(ev, 0), row(ev, 1), row(ev, 2)) == (WHITE, WHITE, PANEL), ("two events in the panel", row(ev, 0), row(ev, 1), row(ev, 2))
assert (dot(fin, 30), dot(fin, 31), dot(fin, 24)) == (WHITE, BG, DOT), ("the marks, after deleting", dot(fin, 30), dot(fin, 31), dot(fin, 24))
assert (row(fin, 0), row(fin, 1)) == (WHITE, PANEL), ("one event left in the panel", row(fin, 0), row(fin, 1))
print("ok: no today with no date, today's blue at 2027-12-30, 31, 29 and 31 days in the grids, the titles, "
      "the marks and the rows of events")
PIX

# events.txt, off the card image (tools/mksd.py's layout: the data partition from block 2048,
# the superblock, 64-byte inodes, folders of 64-byte entries, 4 KiB clusters).
python3 - "$T/sd-test.img" <<'CARD' || fail "events.txt on the card is not what calendar kept"
import struct, sys
card = open(sys.argv[1], "rb").read()
part = 2048 * 512
magic, _, _, _, _, _, _, inode_start, _, data_start, _ = struct.unpack_from("<8s10I", card, part)
assert magic == b"LEANOSF2", magic
def inode(n):
    kind, _, size, *rest = struct.unpack_from("<HHI12III", card, part + inode_start * 512 + 64 * n)
    return kind, size, rest[:12]
def read(n):
    kind, size, direct = inode(n)
    body = b"".join(card[part + (data_start + c * 8) * 512:][:4096] for c in direct if c)
    assert size <= len(body), "a file larger than its direct clusters"
    return body[:size]
def find(folder, name):
    body = read(folder)
    for i in range(0, len(body), 64):
        ino, kind, raw = struct.unpack_from("<II56s", body, i)
        if ino and raw.rstrip(b"\0").decode() == name:
            return ino
    raise AssertionError("no " + name)
text = read(find(find(find(1, "apps"), "calendar"), "events.txt")).decode()
assert text == "2027-12-24 Christmas Eve\n2027-12-30 New Year party\n", repr(text)
print("ok: apps/calendar/events.txt on the card: " + " | ".join(text.splitlines()))
CARD

echo "ok: calendar shows the month with today in it (and says when the date is not set), goes through the months by keys and clicks, and keeps its events on the card"
