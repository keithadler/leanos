#!/bin/bash
# Terminal's text and file commands beyond the first ones: sort, uniq, rev, tr, cut, nl, tee,
# seq, touch, stat, du, tree, cal, sleep, time, calc, and !! and !N. On a card of its own
# (tools/mksd.py) with known files: lines.txt (12 lines), nums.txt (numbers out of order,
# one twice), dup.txt (runs of the same line), csv.txt (fields split by commas, one line
# short of a field, one with none). What a command printed is checked exactly by copying it
# (Ctrl+C with an empty command line) and pasting it back onto the command line after echo
# (Terminal logs the paste), and by the log lines.
#
#   sort: byte order, -r, -n (a negative number, one twice), -rn; of a file and after a |
#       (ls | sort -r | head, seq 10 | sort -n -r | uniq); more than 10240 lines and more
#       than 64 KiB refused. uniq: runs once, -c counts them. rev, tr a-z A-Z (and a set
#       shorter than the other), cut -d C -f N (-d, -f2 too; a line short of the field, one
#       with no C), nl. tee: into a file and on to the next command; without a | refused.
#       seq: 1 to N, A to B, into a pipe; too many refused.
#   touch: a new empty file, one already there left alone. stat: a file's size, a folder's
#       names, a missing one. du and tree: a small tree, and a missing folder.
#   cal: no date known (no network in the first boot) refused without MONTH YEAR; months
#       checked against Python's calendar (Monday first), a leap February; a bad month.
#   sleep 1, and time sleep 1 (at least 1000 ms); time CMD in a pipe, and time run refused
#       there as run is. calc: precedence, parentheses, unary minus, % and /, wrapping at
#       64 bits, division by zero, a ( without its ), nothing.
#   !! and !N: the last command and command N again, inside a line with a |; an N history
#       does not have refused, and the line not kept. Tab completes the new names.
#   Then a second boot with the network and a time server on the host (as test/net.sh has)
#   that says it is 2027-02-14 12:00 UTC: cal with no MONTH YEAR is that month, [14] marked.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

files=$T/term-more-files
rm -rf "$files" && mkdir -p "$files"
printf '%s\n' "alpha one" "Beta two" "gamma three" "delta four ALPHA" "epsilon five" "zeta six" \
  "eta seven" "theta eight" "iota nine" "kappa ten" "lambda eleven" "mu twelve" > "$files/lines.txt"
printf '%s\n' 10 9 2 33 2 -5 100 > "$files/nums.txt"
printf '%s\n' a a b a c c c > "$files/dup.txt"
printf '%s\n' name,age,city ann,31,oslo bob,27,rome cy,45 nocomma > "$files/csv.txt"
card=$T/sd-term-more.img
python3 tools/mksd.py "$card" lines.txt="$files/lines.txt" nums.txt="$files/nums.txt" \
  dup.txt="$files/dup.txt" csv.txt="$files/csv.txt" >/dev/null || fail "no card"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
COPY, PASTE = b"\x03", b"\x16"
seen = {}
def after(prefix):
    """Wait for the next line starting with prefix (counting those before)."""
    seen[prefix] = seen.get(prefix, 0) + 1
    return wait_for(prefix, seen[prefix])
def cmd(line, done=None):
    return [(line + "\r").encode(), after(done or "terminal: " + line.split()[0] + " ")]
def shown():
    """What the last command printed, copied, and pasted onto the command line after echo."""
    return [COPY, after("terminal: copied the last command's output"), b"echo ", PASTE, after("terminal: pasted"), b"\r"]
steps = [*click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         # !! and !N, while history is short
         *cmd("calc 1+1"), *cmd("!!", "terminal: !! -> "), *cmd("!! | wc", "terminal: wc -> "),
         *cmd("!1 | tr 2 x", "terminal: tr -> "), *shown(), *cmd("!999", "terminal: !999 -> "),
         *cmd("history | wc", "terminal: wc -> "),
         # sort
         *cmd("sort lines.txt | head -n 3", "terminal: head -> "), *shown(),
         *cmd("sort -r lines.txt | head -n 2", "terminal: head -> "), *shown(),
         *cmd("sort nums.txt"), *shown(), *cmd("sort -n nums.txt"), *shown(),
         *cmd("sort -rn nums.txt"), *shown(),
         *cmd("ls | sort -r | head -n 3", "terminal: head -> "), *shown(),
         *cmd("seq 10 | sort -n -r | uniq", "terminal: uniq -> "), *shown(),
         *cmd("seq 11000 > many.txt", "terminal: > many.txt"), *cmd("sort many.txt"),
         *cmd("seq 10000 | sort -n -r | head -n 2", "terminal: head -> "), *shown(),
         *cmd("fill huge.txt 70 a"), *cmd("sort huge.txt"), *cmd("sort"),
         # uniq, rev, tr, cut, nl
         *cmd("uniq dup.txt"), *shown(), *cmd("uniq -c dup.txt"), *shown(),
         *cmd("sort -rn nums.txt | uniq -c", "terminal: uniq -> "), *shown(),
         *cmd("rev lines.txt | head -n 2", "terminal: head -> "), *shown(),
         *cmd("cat lines.txt | tr a-z A-Z | head -n 2", "terminal: head -> "), *shown(),
         *cmd("tr a-y b-z dup.txt"), *shown(), *cmd("tr abc x dup.txt"), *shown(), *cmd("tr a dup.txt"),
         *cmd("cut -d , -f 2 csv.txt"), *shown(), *cmd("cut -d, -f3 csv.txt"), *shown(),
         *cmd("cat lines.txt | cut -f 2 | head -n 3", "terminal: head -> "), *shown(),
         *cmd("cut -d , csv.txt"),
         *cmd("nl lines.txt | tail -n 2", "terminal: tail -> "), *shown(),
         # tee, seq
         *cmd("echo hello | tee t.txt | tr a-z A-Z", "terminal: tr -> "), *shown(), *cmd("cat t.txt"), *shown(),
         *cmd("seq 3 | tee s.txt > s2.txt", "terminal: > s2.txt"), *cmd("wc s.txt"), *cmd("wc s2.txt"),
         *cmd("tee t.txt"),
         *cmd("seq 3 5"), *shown(), *cmd("seq 5 | wc", "terminal: wc -> "), *cmd("seq 200000"),
         # touch, stat, du, tree
         *cmd("touch new.txt"), *cmd("touch new.txt"), *cmd("stat new.txt"), *shown(), *cmd("stat lines.txt"),
         *cmd("mkdir d"), *cmd("write d/a.txt hello"), *cmd("mkdir d/e"), *cmd("write d/e/b.txt abc"),
         *cmd("stat d"), *shown(), *cmd("stat nope"), *cmd("du d"), *shown(), *cmd("tree d"), *shown(),
         *cmd("tree d | wc", "terminal: wc -> "), *cmd("du nope"),
         # cal
         *cmd("cal"), *cmd("cal 9 2026 | head -n 4", "terminal: head -> "), *shown(),
         *cmd("cal 9 2026 | tail -n 4", "terminal: tail -> "), *shown(),
         *cmd("cal 2 2024 | tail -n 3", "terminal: tail -> "), *shown(), *cmd("cal 13 2026"),
         # sleep, time, calc
         *cmd("sleep 1"), *cmd("time sleep 1", "terminal: time sleep 1 -> "),
         *cmd("time seq 3 | wc", "terminal: wc -> "), *cmd("time run hello | wc", "terminal: time run hello | wc -> "),
         *cmd("time time run hello > x", "terminal: time time run hello > x -> "),
         *cmd("calc 2+3*4"), *cmd("calc (2 + 3) * 4"), *cmd("calc -7 / 2"), *cmd("calc -7 % 3"),
         *cmd("calc 10 - 2 - 3"), *cmd("calc 9223372036854775807 + 1"), *cmd("calc 1/0"),
         *cmd("calc 2*(3"), *cmd("calc 2)"), *cmd("calc"), *cmd("calc 6*7 | wc", "terminal: wc -> "),
         # Tab
         b"tre\t", after("terminal: completed tre"), b"d\r", after("terminal: tree "),
         b"cal\t\t", after("terminal: completions for cal"), b"\x7f\x7f\x7f",
         *cmd("wc dup.txt")]
sys.exit(boot(150, steps=steps, until="terminal: wc dup.txt -> ", sd=card))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^terminal: " | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"

has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }
pasted() { local n; n=$(printf '%s' "$1" | wc -c | tr -d ' '); has "terminal: pasted $n bytes: $1"; }
# the rows of Python's calendar (Monday first) as cal shows them: one column in, each row
# joined to the next by a space as a paste joins them; rows FROM to TO
pycal() {
  python3 -c "import calendar,sys; m,y,a,b=map(int,sys.argv[1:]); r=calendar.TextCalendar().formatmonth(y,m).rstrip('\n').split('\n'); t=r[0].strip(); r=[' '*((21-len(t))//2)+t]+[' '+x.rstrip() for x in r[1:]]; print(' '.join(r[a:b]))" "$@"
}

# sort: byte order, -r, -n, -rn, after a |; too many lines, too many bytes, nothing to sort
count 2 "terminal: sort -> 12 lines"
pasted "Beta two alpha one delta four ALPHA"
pasted "zeta six theta eight"
count 4 "terminal: sort -> 7 lines"                                   # and sort -rn | uniq -c
pasted "-5 10 100 2 2 33 9"
pasted "-5 2 2 9 10 33 100"
pasted "100 33 10 9 2 2 -5"
has "terminal: sort -> 5 lines"                                        # ls | sort -r | head -n 3
pasted "welcome.txt                   169 bytes nums.txt                      19 bytes lines.txt                     136 bytes"
has "terminal: sort -> 10 lines"
has "terminal: uniq -> 10 lines"
pasted "10 9 8 7 6 5 4 3 2 1"
has "terminal: > many.txt -> 54894 bytes"
has "terminal: sort many.txt -> more than 10240 lines"
has "terminal: sort -> 10000 lines"
pasted "10000 9999"
has "terminal: sort huge.txt -> more than 64 KiB"
has "terminal: sort -> not understood"

# uniq, rev, tr, cut, nl
count 2 "terminal: uniq -> 4 lines"
pasted "a b a c"
pasted "   2 a    1 b    1 a    3 c"
has "terminal: uniq -> 6 lines"
pasted "   1 100    1 33    1 10    1 9    2 2    1 -5"
has "terminal: rev -> 12 lines"
pasted "eno ahpla owt ateB"
has "terminal: tr -> 12 lines"
pasted "ALPHA ONE BETA TWO"
count 2 "terminal: tr -> 7 lines"
pasted "b b c b d d d"
pasted "x x x x x x x"                                                    # abc to x: B's last again
has "terminal: tr -> not understood"                                   # tr a FILE: no second set
count 2 "terminal: cut -> 5 lines"
pasted "age 31 27 45 nocomma"
pasted "city oslo rome  nocomma"                                        # cy,45 has no third: empty
has "terminal: cut -> 12 lines"
pasted "one two three"
has "terminal: cut -> not understood"                                  # no -f
has "terminal: nl -> 12 lines"
pasted "  11  lambda eleven   12  mu twelve"

# tee, seq
has "terminal: tee t.txt -> 6 bytes"
pasted "HELLO"
has "terminal: cat t.txt -> 6 bytes"
pasted "hello"
has "terminal: tee s.txt -> 6 bytes"
has "terminal: > s2.txt -> 6 bytes"
has "terminal: wc s.txt -> 3 lines, 3 words, 6 bytes"
has "terminal: wc s2.txt -> 3 lines, 3 words, 6 bytes"
has "terminal: tee -> not understood"
pasted "3 4 5"
has "terminal: wc -> 5 lines, 5 words, 10 bytes"
has "terminal: seq -> not understood"                                  # 200000 numbers

# touch, stat, du, tree
has "terminal: touch new.txt -> ok"
has "terminal: touch new.txt -> already there"
has "terminal: stat new.txt -> file, 0 bytes"
pasted "new.txt: file, 0 bytes"
has "terminal: stat lines.txt -> file, 136 bytes"
has "terminal: stat d -> folder, 2 names"
pasted "d: folder, 2 names"
has "terminal: stat nope -> no such file"
has "terminal: du d -> 8 bytes in 2 files, 1 folder"
pasted "8 bytes in 2 files, 1 folder"
count 3 "terminal: tree d -> 2 files, 1 folder"                         # and tree d | wc, and Tab's
pasted "d   a.txt   e/     b.txt"
has "terminal: wc -> 4 lines, 4 words, 25 bytes"                       # d, a.txt, e/, b.txt
has "terminal: du nope -> no such folder"

# cal: no date known without MONTH YEAR; months as Python's calendar has them
count 2 "terminal: cal -> not understood"                              # cal, and cal 13 2026
count 2 "terminal: cal -> September 2026"
pasted "$(pycal 9 2026 0 4)"
pasted "$(pycal 9 2026 3 7)"
has "terminal: cal -> February 2024"
pasted "$(pycal 2 2024 4 7)"

# sleep, time, calc
count 2 "terminal: sleep -> 1 second"
ms=$(echo "$out" | sed -n 's/^terminal: time sleep 1 -> \([0-9]*\) ms$/\1/p')
[ -n "$ms" ] && [ "$ms" -ge 950 ] && [ "$ms" -lt 3000 ] || fail "time sleep 1 took ${ms:-nothing} ms"
echo "$out" | grep -qE "^terminal: time seq 3 -> [0-9]+ ms$" || fail "time seq 3 did not say how long"
has "terminal: wc -> 3 lines, 3 words, 6 bytes"
has "terminal: time run hello | wc -> run cannot be piped or redirected"
has "terminal: time time run hello > x -> run cannot be piped or redirected"
echo "$out" | grep -qE "^terminal: (run hello|time run hello|time time run hello) -> " && fail "time run hello ran"
has "terminal: calc 2+3*4 -> 14"
has "terminal: calc (2 + 3) * 4 -> 20"
has "terminal: calc -7 / 2 -> -3"
has "terminal: calc -7 % 3 -> -1"
has "terminal: calc 10 - 2 - 3 -> 5"
has "terminal: calc 9223372036854775807 + 1 -> -9223372036854775808"
has "terminal: calc 1/0 -> division by zero"
has "terminal: calc 2*(3 -> a ( without its )"
has "terminal: calc 2) -> a ) without its ("
has "terminal: calc -> calc EXPR, such as (2+3)*4"
has "terminal: calc 6*7 -> 42"
has "terminal: wc -> 1 line, 1 word, 3 bytes"

# !! and !N: the line as it ran, kept for Up once; !999 refused and not kept
has "terminal: !! -> calc 1+1"
has "terminal: !! | wc -> calc 1+1 | wc"
has "terminal: !1 | tr 2 x -> calc 1+1 | tr 2 x"
count 4 "terminal: calc 1+1 -> 2"
has "terminal: wc -> 1 line, 1 word, 2 bytes"
has "terminal: tr -> 1 line"
pasted "x"
has "terminal: !999 -> !N: no command N in history"
# calc 1+1, calc 1+1 | wc, calc 1+1 | tr 2 x, the echo x that checked it, history | wc
has "terminal: history -> 5 commands"

# Tab
has "terminal: completed tre -> tree"
has "terminal: completions for cal -> 2: cal calc"

# the second boot: a time server on the host says it is 2027-02-14 12:00 UTC (the zone is UTC:
# the card has no settings.txt)
ntp_port=$((20000 + RANDOM % 20000))
python3 - $ntp_port <<'NTP' &
import socket, struct, sys
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.bind(("127.0.0.1", int(sys.argv[1])))
when = 1802606400 + 2208988800           # 2027-02-14 12:00:00 UTC, in NTP's seconds since 1900
while True:
    q, a = s.recvfrom(512)
    if len(q) >= 48 and q[0] & 7 == 3:
        s.sendto(bytes([0x24, 2, 6, 0xec]) + bytes(20) + q[40:48] + struct.pack(">IIII", when, 0, when, 0), a)
NTP
ntp=$!
trap 'kill $ntp 2>/dev/null; wait $ntp 2>/dev/null' EXIT
sleep 1
out=$(NTP=$ntp_port python3 - "$card" <<'PY'
import os, sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
COPY, PASTE = b"\x03", b"\x16"
def shown(n):
    return [COPY, wait_for("terminal: copied the last command's output", n), b"echo ", PASTE,
            wait_for("terminal: pasted", n), b"\r"]
# after the boot's own try at pool.ntp.org (the second "usb: network: " line), ntp to the host
steps = [wait_for("usb: network: ", 2), *click(*DOCK["Terminal"]), wait_for("terminal: opened"),
         f"ntp 10.0.2.2:{os.environ['NTP']}\r".encode(), wait_for("terminal: ntp"),
         b"cal | tail -n 3\r", wait_for("terminal: tail -> "), *shown(1),
         b"cal 2 2027 | head -n 3\r", wait_for("terminal: head -> "), *shown(2),
         b"cal 3 2027 | tail -n 3\r", wait_for("terminal: tail -> ", 2), *shown(3),
         b"date\r", wait_for("terminal: date")]
sys.exit(boot(150, net=True, sd=card, steps=steps, until="terminal: date", settle=0.3))
PY
)
status=$?
echo "$out" >> "$T/serial.txt"
echo "$out" | grep -E "^terminal: " | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the second run did not finish (status $status)"
echo "$out" | grep -qE "^terminal: date -> 2027-02-14 12:00:[0-5][0-9] UTC$" || fail "the time server's date did not stick"
count 2 "terminal: cal -> February 2027"
has "terminal: cal -> March 2027"
pasted "  8  9 10 11 12 13[14]  15 16 17 18 19 20 21  22 23 24 25 26 27 28"   # today marked
pasted "$(pycal 2 2027 0 3)"
pasted "$(pycal 3 2027 4 7)"                                                 # another month: no mark

echo "ok: sort, uniq, rev, tr, cut, nl, tee, seq, touch, stat, du, tree, cal (today marked once the date is known), sleep, time, calc, !! and !N, each output as expected, in pipes too"
