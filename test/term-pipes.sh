#!/bin/bash
# Terminal's > , >> and |: a command's output into a file, at a file's end, or into the next
# command. On a card of its own (tools/mksd.py) with known files: lines.txt (12 lines) and
# big.txt (4000 lines, 41142 bytes, more than two of the file server's pieces, every 7th
# line with an x). What a command printed is checked exactly by copying it (Ctrl+C with an
# empty command line) and pasting it back onto the command line after echo (Terminal logs
# the paste), by cat of the file it went into, and by the log lines.
#
#   > and >>: echo hi > a.txt, then >> adds; ls > list.txt is what ls shows; cat of a file
#       of 41142 bytes into another is the same bytes (its pieces joined as they were);
#       df > d.txt is what df shows. With no spaces around them too.
#   |: cat big.txt | grep x | wc; history | tail -n 2; find | grep .txt | head -n 3 (grep
#       completed by Tab after the |); head | cat; Up brings a line with | back and it runs.
#   A line of 1024 bytes: 200 on the screen, all of it through > and |.
#   An overwrite that cannot be made (FILE.tmp is a folder), a command that fails (cat of a
#       missing file), and more than 64 KiB of output all leave the old file as it was.
#   Refused, with nothing run and nothing written: > with no file, | at the start or the
#       end, > before a |, a file that is a folder, a command that is not one, and run,
#       tour, cd and kill.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

files=$T/term-pipes-files
rm -rf "$files" && mkdir -p "$files"
printf '%s\n' "alpha one" "Beta two" "gamma three" "delta four ALPHA" "epsilon five" "zeta six" \
  "eta seven" "theta eight" "iota nine" "kappa ten" "lambda eleven" "mu twelve" > "$files/lines.txt"
for i in $(seq 1 4000); do
  if [ $((i % 7)) = 0 ]; then printf 'line %04d x\n' "$i"; else printf 'line %04d\n' "$i"; fi
done > "$files/big.txt"
card=$T/sd-term-pipes.img
python3 tools/mksd.py "$card" lines.txt="$files/lines.txt" big.txt="$files/big.txt" >/dev/null || fail "no card"
big_bytes=$(wc -c < "$files/big.txt" | tr -d ' ')
big_words=$(wc -w < "$files/big.txt" | tr -d ' ')
read -r x_lines x_words x_bytes <<<"$(grep x "$files/big.txt" | wc | tr -s ' ' | sed 's/^ //')"

out=$(python3 - "$card" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot, mouse, wait_for, DOCK
card = sys.argv[1]
click = lambda x, y: [mouse("d", x, y), mouse("u", x, y)]
COPY, PASTE, UP = b"\x03", b"\x16", b"\x1b[A"
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
         # > and >>, and the history of those lines
         *cmd("echo hi > a.txt", "terminal: > a.txt"), *cmd("cat a.txt"), *shown(),
         *cmd("echo there >> a.txt", "terminal: >> a.txt"), *cmd("cat a.txt"), *shown(),
         *cmd("history | tail -n 2", "terminal: tail -> "), *shown(),
         *cmd("echo no spaces>>a.txt", "terminal: >> a.txt"), *cmd("cat a.txt"),
         *cmd("echo a b|wc", "terminal: wc -> "),
         # ls > list.txt is what ls showed
         *cmd("ls"), *shown(), *cmd("ls > list.txt", "terminal: > list.txt"), *cmd("wc list.txt"),
         *cmd("cat list.txt"), *shown(),
         # a pipe of three, again from Up; a file of 41142 bytes through > and through cat |
         *cmd("cat big.txt | grep x | wc", "terminal: wc -> "),
         UP, b"\r", after("terminal: wc -> "),
         *cmd("cat big.txt > copy.txt", "terminal: > copy.txt"), *cmd("wc copy.txt"),
         *cmd("cat big.txt | cat | wc", "terminal: wc -> "),
         *cmd("head -n 2 lines.txt | cat", "terminal: cat -> "), *shown(),
         # Tab completes a command after a |
         *cmd("find", "terminal: find -> "), *shown(),
         b"find | gr\t", after("terminal: completed gr -> grep"),
         *cmd(".txt | head -n 3", "terminal: head -> "), *shown(),
         # df > d.txt is what df showed
         *cmd("df"), *shown(), *cmd("df > d.txt", "terminal: > d.txt"), *cmd("cat d.txt"), *shown(),
         # a line of 1024 bytes: 200 of it on the screen, all of it through > and |
         *cmd("fill long.txt 1 z"), *cmd("head -n 1 long.txt"),
         *cmd("head -n 1 long.txt > h.txt", "terminal: > h.txt"), *cmd("wc h.txt"),
         *cmd("cat long.txt | grep zzz | wc", "terminal: wc -> "),
         # the old file stays when the new one cannot be made, the command fails, or it is too much
         *cmd("echo old > keep.txt", "terminal: > keep.txt"), *cmd("mkdir keep.txt.tmp"),
         *cmd("echo new > keep.txt", "terminal: > keep.txt"),
         *cmd("cat nope.txt > keep.txt", "terminal: > keep.txt"), *shown(),
         *cmd("fill huge.txt 70 a"), *cmd("cat huge.txt > keep.txt", "terminal: > keep.txt"),
         *cmd("cat huge.txt | wc", "terminal: | -> "),
         *cmd("echo x > nodir/x.txt", "terminal: > nodir/x.txt"),
         *cmd("cat keep.txt"), *shown(),
         # refused
         *cmd("echo x >", "terminal: echo x > -> "), *cmd("| wc", "terminal: | wc -> "),
         *cmd("ls |", "terminal: ls | -> "), *cmd("ls > x | wc", "terminal: ls > x | wc -> "),
         *cmd("ls > keep.txt.tmp", "terminal: ls > keep.txt.tmp -> "),
         *cmd("ls | nosuch", "terminal: ls | nosuch -> "),
         *cmd("run hello > x", "terminal: run hello > x -> "), *cmd("tour | wc", "terminal: tour | wc -> "),
         *cmd("cd .. > x", "terminal: cd .. > x -> "), *cmd("kill 10 | wc", "terminal: kill 10 | wc -> "),
         *cmd("> x", "terminal: > x -> "),
         *cmd("cat x"), *cmd("ls -a", "terminal: ls -a -> ")]
sys.exit(boot(120, steps=steps, until="terminal: ls -a -> ", sd=card))
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

# > and >>: "hi\n", then "there\n" and "no spaces\n" added
has "terminal: > a.txt -> 3 bytes"
has "terminal: cat a.txt -> 3 bytes"
pasted "hi"
has "terminal: >> a.txt -> 6 bytes"
has "terminal: cat a.txt -> 9 bytes"
pasted "hi there"
has "terminal: >> a.txt -> 10 bytes"
has "terminal: cat a.txt -> 19 bytes"
has "terminal: wc -> 1 line, 2 words, 4 bytes"                        # echo a b|wc: "a b\n"

# history | tail -n 2: the line before, and the line itself
has "terminal: history -> 7 commands"
has "terminal: tail -> 2 lines of 7"
pasted "6   echo hi there 7   history | tail -n 2"

# ls > list.txt: what ls showed (4 rows: 39 + 39 + 41 + 38 bytes and their '\n's)
count 2 "terminal: ls -> 4 files"                                     # ls, and ls > list.txt
has "terminal: > list.txt -> 161 bytes"
has "terminal: wc list.txt -> 4 lines, 12 words, 161 bytes"
count 2 "terminal: copied the last command's output, 160 bytes -> ok"
count 2 "terminal: pasted 155 bytes: welcome.txt                   169 bytes lines.txt                     136 bytes big.txt                       41142 bytes a.txt                         19 "

# pipes of three; the same bytes through > and through cat |
count 4 "terminal: cat big.txt -> $big_bytes bytes"
count 2 "terminal: grep x -> $x_lines lines"
count 2 "terminal: wc -> $x_lines lines, $x_words words, $x_bytes bytes"   # typed, and again from Up
has "terminal: > copy.txt -> $big_bytes bytes"
has "terminal: wc copy.txt -> 4000 lines, $big_words words, $big_bytes bytes"
has "terminal: cat -> $big_bytes bytes"
has "terminal: wc -> 4000 lines, $big_words words, $big_bytes bytes"
has "terminal: head lines.txt -> 2 lines"
has "terminal: cat -> 19 bytes"
pasted "alpha one Beta two"

# find | grep .txt | head -n 3, grep completed by Tab
has "terminal: find -> 6 found"
pasted "welcome.txt lines.txt big.txt a.txt list.txt copy.txt"
has "terminal: completed gr -> grep"
count 2 "terminal: find -> 6 found"
has "terminal: grep .txt -> 6 lines"
has "terminal: head -> 3 lines"
pasted "welcome.txt lines.txt big.txt"

# df > d.txt: what df showed
df=$(echo "$out" | sed -n 's/^terminal: pasted [0-9]* bytes: \(size .*\)$/\1/p' | sort -u)
[ "$(echo "$df" | wc -l | tr -d ' ')" = 1 ] || fail "df > d.txt is not what df showed: $df"
count 2 "terminal: pasted $(printf '%s' "$df" | wc -c | tr -d ' ') bytes: $df"
# the two lines as pasted, a space between them, and the file's: a '\n' between and one after
has "terminal: > d.txt -> $(( $(printf '%s' "$df" | wc -c) + 1 )) bytes"
has "terminal: cat d.txt -> $(( $(printf '%s' "$df" | wc -c) + 1 )) bytes"

# a long line, whole through > and |
has "terminal: head long.txt -> 1 line"
count 2 "terminal: head long.txt -> 1 line"
has "terminal: > h.txt -> 1025 bytes"
has "terminal: wc h.txt -> 1 line, 1 word, 1025 bytes"
has "terminal: grep zzz -> 1 line"
has "terminal: wc -> 1 line, 1 word, 1025 bytes"

# the old file stays
has "terminal: > keep.txt -> 4 bytes"
has "terminal: > keep.txt -> not written: a folder"                   # keep.txt.tmp is one
has "terminal: cat nope.txt -> no such file"
has "terminal: > keep.txt -> stopped, the command failed"
pasted "no such file nothing written"
has "terminal: cat huge.txt -> 71680 bytes"
has "terminal: > keep.txt -> stopped, more than 64 KiB of output"
has "terminal: | -> stopped, more than 64 KiB of output"
has "terminal: > nodir/x.txt -> not written: no such file"
has "terminal: cat keep.txt -> 4 bytes"
pasted "old"

# refused, and nothing ran: no ls, no program started, no file x
has "terminal: echo x > -> > needs one file name"
has "terminal: | wc -> | needs a command on both sides"
has "terminal: ls | -> | needs a command on both sides"
has "terminal: ls > x | wc -> > FILE goes at the end, once"
has "terminal: ls > keep.txt.tmp -> a folder, not a file"
has "terminal: ls | nosuch -> not a command: nosuch"
has "terminal: run hello > x -> run cannot be piped or redirected"
has "terminal: tour | wc -> tour cannot be piped or redirected"
has "terminal: cd .. > x -> cd cannot be piped or redirected"
has "terminal: kill 10 | wc -> kill cannot be piped or redirected"
has "terminal: > x -> > needs a command before it"
has "terminal: cat x -> no such file"
[ "$(echo "$out" | grep -c "^terminal: ls -> ")" = 2 ] || fail "an ls that was refused ran"
echo "$out" | grep -qE "^terminal: (run hello|run tour|kill 10|cd \.\.) -> " && fail "a refused command ran"
# every file the card has now: no FILE.tmp left behind, no x, no huge output written
has "terminal: ls -a -> 12 files"
echo "ok: > and >> write and add, | hands output on ($x_lines of 4000 lines through cat | grep | wc), ls, df and cat big.txt through > are what they show, the old file stays when the new one cannot be written, refused lines run nothing"
