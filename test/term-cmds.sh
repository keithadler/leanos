#!/bin/bash
# Terminal's commands for files: cp, head, tail, wc, grep, find, df, and history. On a card of
# its own (tools/mksd.py) with known files: lines.txt (12 lines), numbers.txt (3000 lines of
# 10 bytes, 30000 bytes, more than one of the file server's pieces, so lines straddle them),
# long.txt (one line of 300 bytes) and n000 to n119. What a command printed is checked
# exactly by copying it (Ctrl+C with an empty command line) and pasting it back onto the
# command line (Ctrl+V), which Terminal logs, after an echo (so it runs as nothing more).
#
#   cp: a file of 30000 bytes and one of 40 KiB, in pieces, whole (wc, grep, tail, verify);
#       onto itself; into a folder; a folder, a missing file and one name refused.
#   head, tail: the first and last lines, -n N, a file without a last '\n', a long line
#       shown in its first 200 bytes (4 rows), a missing file, a bad -n.
#   wc: lines, words and bytes; a folder refused. grep: a word, -i, several files (with
#       their names and line numbers), a missing one among them, a line split between two
#       pieces of the file, no match.
#   find: a small tree, by folder and by name, from inside it, a missing folder, nothing
#       found; a chain of folders 17 deep (it goes 16 down) and 120 names (it shows 100).
#   df: the file server's own count at boot, and the totals when a file of 20 KiB comes and
#       goes (5 clusters, one file). history: the commands, oldest first, the last 32.
set -u
cd "$(dirname "$0")/.."
T=${LEANOS_TEST_DIR:-build}
mkdir -p "$T"
fail() { echo "FAIL: $*"; exit 1; }

files=$T/term-cmds-files
rm -rf "$files" && mkdir -p "$files"
printf '%s\n' "alpha one" "Beta two" "gamma three" "delta four ALPHA" "epsilon five" "zeta six" \
  "eta seven" "theta eight" "iota nine" "kappa ten" "lambda eleven" "mu twelve" > "$files/lines.txt"
for i in $(seq 1 3000); do printf 'line %04d\n' "$i"; done > "$files/numbers.txt"
printf '0123456789%.0s' $(seq 1 30) > "$files/long.txt"
names=""
for i in $(seq 0 119); do n=$(printf 'n%03d' "$i"); echo "$i" > "$files/$n"; names="$names $n=$files/$n"; done
card=$T/sd-term-cmds.img
# shellcheck disable=SC2086
python3 tools/mksd.py "$card" lines.txt="$files/lines.txt" numbers.txt="$files/numbers.txt" \
  long.txt="$files/long.txt" $names >/dev/null || fail "no card"
lines_bytes=$(wc -c < "$files/lines.txt" | tr -d ' ')
lines_words=$(wc -w < "$files/lines.txt" | tr -d ' ')

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
         *cmd("df"), *cmd("wc lines.txt"), *cmd("history"), *shown(),
         # head and tail
         *cmd("head -n 3 lines.txt"), *shown(), *cmd("head lines.txt"),
         *cmd("tail -n 2 lines.txt"), *shown(), *cmd("tail lines.txt"), *shown(),
         *cmd("write nonl.txt x y  z"), *cmd("wc nonl.txt"), *cmd("tail -n 1 nonl.txt"), *shown(),
         *cmd("head -n 1 long.txt"), COPY, after("terminal: copied the last command's output"),
         *cmd("head nope.txt"), *cmd("tail -n x lines.txt"), *cmd("wc numbers.txt"),
         *cmd("tail -n 1 numbers.txt"), *shown(),
         # grep
         *cmd("grep ALPHA lines.txt"), *shown(),
         *cmd("grep -i alpha lines.txt nonl.txt nope.txt"), *shown(),
         *cmd("grep zebra lines.txt"), *shown(), *cmd("grep 1613 numbers.txt"), *shown(),
         # cp
         *cmd("cp numbers.txt n2.txt"), *cmd("wc n2.txt"), *cmd("grep 1613 n2.txt"), *shown(),
         *cmd("head -n 1 n2.txt"), *shown(), *cmd("tail -n 1 n2.txt"), *shown(),
         *cmd("fill big 40 q"), *cmd("cp big big2"), *cmd("verify big2"),
         *cmd("cp lines.txt lines.txt"), *cmd("wc lines.txt"),
         *cmd("mkdir t"), *cmd("cp lines.txt t"), *cmd("wc t/lines.txt"),
         *cmd("cp t x"), *cmd("cp nope.txt x"), *cmd("cp lines.txt"), *cmd("wc t"),
         # find
         *cmd("mkdir t/sub"), *cmd("write t/sub/deep.txt x"), *cmd("write t/b.txt y"),
         *cmd("find t"), *shown(), *cmd("find t deep"), *shown(), *cmd("find deep"), *shown(),
         *cmd("cd t"), *cmd("find"), *shown(), *cmd("cd .."),
         *cmd("find nosuch x"), *cmd("find zzz")]
deep = "d"
steps += cmd("mkdir d")
for _ in range(17):
    deep += "/a"
    steps += cmd("mkdir " + deep)
steps += [*cmd("find d"), *cmd("find n")]
# df: a file of 20 KiB comes and goes, in folder t (which has room for its name)
steps += [*cmd("df"), *cmd("fill t/dfx 20 z"), *cmd("df"), *cmd("rm t/dfx"), *cmd("df"),
          b"hi\t\r", after("terminal: history ")]
sys.exit(boot(150, steps=steps, until="terminal: history -> 32", sd=card))
PY
)
status=$?
echo "$out" > "$T/serial.txt"
echo "$out" | grep -E "^(terminal: |fs: (ready|checked))" | grep -v "^terminal: mkdir d" | sed 's/^/  | /'
[ $status -eq 0 ] || fail "the run did not finish (status $status)"
echo "$out" | grep -qE "PANIC|exception in the kernel" && fail "the kernel stopped"
echo "$out" | grep -q "^terminal: .*not a command" && fail "a command was not known"

has() { echo "$out" | grep -qxF "$1" || fail "missing: $1"; }
count() { [ "$(echo "$out" | grep -cxF "$2")" = "$1" ] || fail "not $1 times: $2"; }
pasted() { local n; n=$(printf '%s' "$1" | wc -c | tr -d ' '); has "terminal: pasted $n bytes: $1"; }

# history: the commands so far, oldest first
has "terminal: history -> 3 commands"
pasted "1   df 2   wc lines.txt 3   history"

# head, tail, wc
count 2 "terminal: wc lines.txt -> 12 lines, $lines_words words, $lines_bytes bytes"
has "terminal: head lines.txt -> 3 lines"
pasted "alpha one Beta two gamma three"
has "terminal: head lines.txt -> 10 lines"
has "terminal: tail lines.txt -> 2 lines of 12"
pasted "lambda eleven mu twelve"
has "terminal: tail lines.txt -> 10 lines of 12"
pasted "gamma three delta four ALPHA epsilon five zeta six eta seven theta eight iota nine kappa ten lambda eleven mu twelve"
has "terminal: wc nonl.txt -> 0 lines, 3 words, 6 bytes"
has "terminal: tail nonl.txt -> 1 line of 1"
pasted "x y  z"
has "terminal: head long.txt -> 1 line"
has "terminal: copied the last command's output, 200 bytes -> ok"     # a line of 300: 200 shown, in 4 rows
has "terminal: head nope.txt -> no such file"
has "terminal: tail -> not understood"
has "terminal: wc numbers.txt -> 3000 lines, 6000 words, 30000 bytes"
has "terminal: tail numbers.txt -> 1 line of 3000"
pasted "line 3000"

# grep
has "terminal: grep ALPHA -> 1 line"
pasted "delta four ALPHA"
has "terminal: grep -i alpha -> 2 lines"
pasted "lines.txt:1: alpha one lines.txt:4: delta four ALPHA nope.txt: no such file"
has "terminal: grep zebra -> 0 lines"
pasted "no match"
count 2 "terminal: grep 1613 -> 1 line"                                 # it straddles two pieces
count 2 "terminal: pasted 9 bytes: line 1613"

# cp
has "terminal: cp numbers.txt n2.txt -> 30000 bytes"
has "terminal: wc n2.txt -> 3000 lines, 6000 words, 30000 bytes"
has "terminal: head n2.txt -> 1 line"
pasted "line 0001"
has "terminal: tail n2.txt -> 1 line of 3000"
count 2 "terminal: pasted 9 bytes: line 3000"
has "terminal: cp big big2 -> 40960 bytes"
has "terminal: verify big2 -> 40960 bytes of 'q'"
has "terminal: cp lines.txt lines.txt -> $lines_bytes bytes"
has "terminal: cp lines.txt t -> $lines_bytes bytes"
has "terminal: wc t/lines.txt -> 12 lines, $lines_words words, $lines_bytes bytes"
has "terminal: cp t x -> cp copies files, not folders"
has "terminal: cp nope.txt x -> no such file"
has "terminal: cp lines.txt -> cp FROM TO"
has "terminal: wc t -> a folder, not a file"

# find
has "terminal: find t -> 4 found"
pasted "t/lines.txt t/sub/ t/sub/deep.txt t/b.txt"
has "terminal: find t deep -> 1 found"
has "terminal: find deep -> 1 found"
count 2 "terminal: pasted 14 bytes: t/sub/deep.txt"
has "terminal: find -> 4 found"
pasted "lines.txt sub/ sub/deep.txt b.txt"
has "terminal: find nosuch -> no such folder"
has "terminal: find zzz -> 0 found"
has "terminal: find d -> 16 found, not below 16 folders"
has "terminal: find n -> 100 found, stopped"

# df: as the file server counted at boot; then a file of 20 KiB is 5 clusters and one file
checked=$(echo "$out" | sed -n 's/^fs: checked: \([0-9]*\) files\{0,1\} in \([0-9]*\) folders\{0,1\}, \([0-9]*\) KiB free of \([0-9]*\),.*/\1 \2 \3 \4/p')
[ -n "$checked" ] || fail "the file server's count at boot is missing"
read -r f0 d0 free0 size0 <<<"$checked"
dfs=$(echo "$out" | sed -n 's/^terminal: df -> \([0-9]*\) KiB free of \([0-9]*\), \([0-9]*\) files, \([0-9]*\) folders$/\1 \2 \3 \4/p')
[ "$(echo "$dfs" | wc -l | tr -d ' ')" = 4 ] || fail "df did not answer 4 times: $dfs"
first=$(echo "$dfs" | sed -n 1p)
[ "$first" = "$free0 $size0 $f0 $((d0 - 1))" ] || fail "df at first ($first) is not the file server's count at boot ($free0 $size0 $f0 $((d0 - 1)))"
read -r free1 size1 f1 d1 <<<"$(echo "$dfs" | sed -n 2p)"
read -r free2 size2 f2 d2 <<<"$(echo "$dfs" | sed -n 3p)"
[ "$free2 $size2 $f2 $d2" = "$((free1 - 20)) $size1 $((f1 + 1)) $d1" ] \
  || fail "a file of 20 KiB: df went from ($free1 $size1 $f1 $d1) to ($free2 $size2 $f2 $d2)"
[ "$(echo "$dfs" | sed -n 4p)" = "$free1 $size1 $f1 $d1" ] || fail "the file gone, df is not as before: $(echo "$dfs" | sed -n 4p)"
has "terminal: fill t/dfx -> ok"
has "terminal: rm t/dfx -> ok"

# history, completed from hi: the last 32
has "terminal: completed hi -> history"
has "terminal: history -> 32 commands"
echo "ok: cp, head, tail, wc, grep, find, df and history, each output as expected; df $free1 of $size1 KiB free, $((free1 - 20)) with a file of 20 KiB"
