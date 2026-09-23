#!/bin/bash
# The card image a Pi 4 boots (tools/mkpiimage.py), with stand-in firmware: its boot
# partition must be a clean FAT file system holding the four files the firmware reads, and
# leanos booted with the image as its card must find the data partition behind the boot
# partition and read its files, never touching the boot partition.
set -u
cd "$(dirname "$0")/.."
fail() { echo "FAIL: $*"; exit 1; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
head -c 2300000 /dev/urandom > "$tmp/start4.elf"
head -c 5400 /dev/urandom > "$tmp/fixup4.dat"
python3 tools/mkpiimage.py "$tmp/card.img" --firmware "$tmp" --kernel build/kernel8.img hello=build/progs/hello.elf clock=build/progs/clock.elf >/dev/null \
  || fail "the image was not built"
python3 - "$tmp/card.img" "$tmp/boot.img" <<'PY' || fail "the partition table is wrong"
import struct, sys
card = open(sys.argv[1], "rb").read()
assert card[510:512] == b"\x55\xaa"
parts = [struct.unpack_from("<BxxxII", card, 446 + 16 * i + 4) for i in range(2)]
(t1, s1, n1), (t2, s2, n2) = parts
assert (t1, s1) == (0x0E, 2048) and t2 == 0xDA and s2 == s1 + n1 and s2 + n2 == len(card) // 512, parts
open(sys.argv[2], "wb").write(card[s1 * 512:(s1 + n1) * 512])
PY
fsck_msdos -n "$tmp/boot.img" > "$tmp/fsck.txt" 2>&1 || { cat "$tmp/fsck.txt"; fail "the boot partition is not a clean FAT file system"; }
grep -q "4 files" "$tmp/fsck.txt" || { cat "$tmp/fsck.txt"; fail "the boot partition does not hold the four boot files"; }
cp "$tmp/boot.img" "$tmp/boot-before.img"

out=$(python3 - "$tmp/card.img" <<'PY'
import sys
sys.path.insert(0, "test")
from run import boot
sys.exit(boot(40, sd=sys.argv[1]))
PY
)
[ $? -eq 0 ] || fail "leanos did not reach idle on the Pi image"
echo "$out" | grep -qx "leanos: SD card ready, data partition of 63 MiB" || fail "the data partition was not found"
echo "$out" | grep -qx "fs: ready, 3 files on the SD card" || fail "the files on the image were not read"
python3 - "$tmp/card.img" "$tmp/boot-before.img" <<'PY' || fail "leanos wrote to the boot partition"
import sys
card, boot = open(sys.argv[1], "rb").read(), open(sys.argv[2], "rb").read()
assert card[2048 * 512:2048 * 512 + len(boot)] == boot
PY
echo "ok: the Pi 4 image has a clean FAT boot partition, and leanos finds its data partition and leaves the boot partition alone"
