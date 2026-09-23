#!/usr/bin/env python3
"""Builds build/leanos-pi4.img, an SD card image a Raspberry Pi 4 boots leanos from:

  block 0            the partition table
  partition 1        FAT16, 64 MiB, the boot partition: the Pi's firmware (start4.elf,
                     fixup4.dat), config.txt, and kernel8.img
  partition 2        type 0xDA, the rest of 128 MiB, the file server's data
                     (tools/mksd.py): welcome.txt and the programs Terminal can run

Write it to a card with Raspberry Pi Imager ("Use custom") or dd. The firmware files are the
Raspberry Pi Foundation's, not part of leanos: tools/fetch-firmware.sh downloads them into
build/firmware/ first.

Usage: mkpiimage.py OUT.img [--kernel IMG] [--firmware DIR] NAME=FILE ...
  NAME=FILE       the programs for the data partition
  --kernel IMG    the kernel (make pi-image passes build/pi/kernel8.img, built for real
                  hardware; the tests pass the QEMU build)
  --firmware DIR  only to test the image with stand-in files
"""
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mksd import SECTOR, mbr, file_system, program_files  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BOOT_START = 2048                    # 1 MiB in, where card tools put the first partition
BOOT_SECTORS = 64 * 2048             # 64 MiB
CARD_SECTORS = 128 * 2048            # 128 MiB in all (a power of two, which QEMU needs too)
SECTORS_PER_CLUSTER = 4              # 2 KiB clusters: 32 K clusters, so FAT16
RESERVED, FATS, ROOT_ENTRIES = 4, 2, 512

CONFIG = b"""# leanos on a Raspberry Pi 4 (the firmware reads this; see
# https://www.raspberrypi.com/documentation/computers/config_txt.html)
arm_64bit=1
kernel=kernel8.img
# the PL011 UART at 115200 baud on GPIO 14/15 (header pins 8, 10): leanos's console and,
# until there is a USB driver, its keyboard and mouse (the browser console's protocol)
enable_uart=1
# the interrupt controller leanos uses (the GIC-400), not the legacy one
enable_gic=1
# leanos reads no device tree
device_tree=
# the whole screen, and a picture even if the monitor is plugged in after power-on
disable_overscan=1
hdmi_force_hotplug=1
"""


def fat16(files):
    """A FAT16 file system of BOOT_SECTORS sectors with `files` (8.3 name, bytes) in its
    root directory."""
    root_sectors = ROOT_ENTRIES * 32 // SECTOR
    fat_sectors = 1
    while True:
        data_sectors = BOOT_SECTORS - RESERVED - FATS * fat_sectors - root_sectors
        clusters = data_sectors // SECTORS_PER_CLUSTER
        need = ((clusters + 2) * 2 + SECTOR - 1) // SECTOR
        if need <= fat_sectors:
            break
        fat_sectors = need
    assert 4085 <= clusters < 65525, clusters

    image = bytearray(BOOT_SECTORS * SECTOR)
    bs = bytearray(SECTOR)
    bs[0:3] = b"\xeb\x3c\x90"
    bs[3:11] = b"LEANOS  "
    struct.pack_into("<HBHBHHBHHHII", bs, 11, SECTOR, SECTORS_PER_CLUSTER, RESERVED, FATS,
                     ROOT_ENTRIES, 0, 0xF8, fat_sectors, 32, 64, BOOT_START, BOOT_SECTORS)
    struct.pack_into("<BBBI", bs, 36, 0x80, 0, 0x29, 0x1EA2026)
    bs[43:54] = b"LEANOS BOOT"
    bs[54:62] = b"FAT16   "
    bs[510:512] = b"\x55\xaa"
    image[0:SECTOR] = bs

    fat = bytearray(fat_sectors * SECTOR)
    struct.pack_into("<HH", fat, 0, 0xFFF8, 0xFFFF)
    root = bytearray(root_sectors * SECTOR)
    root[0:11] = b"LEANOS BOOT"
    root[11] = 0x08                                   # the volume label
    data_start = RESERVED + FATS * fat_sectors + root_sectors
    cluster_bytes = SECTORS_PER_CLUSTER * SECTOR
    next_cluster = 2
    for i, (name, content) in enumerate(files, start=1):
        base, ext = name.split(".")
        short = base.upper().ljust(8)[:8].encode() + ext.upper().ljust(3)[:3].encode()
        count = max(1, (len(content) + cluster_bytes - 1) // cluster_bytes)
        first = next_cluster
        for k in range(count):
            c = first + k
            struct.pack_into("<H", fat, 2 * c, 0xFFFF if k == count - 1 else c + 1)
        at = (data_start + (first - 2) * SECTORS_PER_CLUSTER) * SECTOR
        image[at:at + len(content)] = content
        next_cluster += count
        e = 32 * i
        root[e:e + 11] = short
        root[e + 11] = 0x20                           # an ordinary file
        # 2026-01-01 00:00 for every time field
        struct.pack_into("<BBHHHHHHHI", root, e + 12, 0, 0, 0, 0x5C21, 0x5C21, 0, 0, 0x5C21,
                         first, len(content))
    if next_cluster - 2 > clusters:
        sys.exit("the boot files do not fit in the boot partition")
    for k in range(FATS):
        at = (RESERVED + k * fat_sectors) * SECTOR
        image[at:at + len(fat)] = fat
    at = (RESERVED + FATS * fat_sectors) * SECTOR
    image[at:at + len(root)] = root
    return image


def main():
    args = sys.argv[1:]
    out = args.pop(0)
    def option(flag, default):
        if flag not in args:
            return default
        i = args.index(flag)
        value = args[i + 1]
        del args[i:i + 2]
        return value
    firmware = option("--firmware", os.path.join(ROOT, "build", "firmware"))
    kernel = option("--kernel", os.path.join(ROOT, "build", "pi", "kernel8.img"))
    specs = args
    needed = ["start4.elf", "fixup4.dat"]
    missing = [f for f in needed if not os.path.exists(os.path.join(firmware, f))]
    if missing:
        sys.exit(f"missing {', '.join(missing)} in build/firmware/: run tools/fetch-firmware.sh first")
    boot_files = [(f, open(os.path.join(firmware, f), "rb").read()) for f in needed]
    boot_files += [("config.txt", CONFIG),
                   ("kernel8.img", open(kernel, "rb").read())]
    data_start = BOOT_START + BOOT_SECTORS
    total = CARD_SECTORS
    card = bytearray(total * SECTOR)
    card[0:SECTOR] = mbr([(0x0E, BOOT_START, BOOT_SECTORS), (0xDA, data_start, total - data_start)])
    card[BOOT_START * SECTOR:data_start * SECTOR] = fat16(boot_files)
    fs = file_system(program_files(specs), total - data_start)
    card[data_start * SECTOR:data_start * SECTOR + len(fs)] = fs
    open(out, "wb").write(card)
    print(f"{out}: {total * SECTOR // (1024 * 1024)} MiB; write it to an SD card and boot a Pi 4")


if __name__ == "__main__":
    main()
