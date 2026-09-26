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
  --bringup       the first-boot card (make pi-bringup): its config.txt is CONFIG, marked as
                  the bring-up card, with the firmware's own log always on (bringup_config)
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

CONFIG = b"""# leanos on a Raspberry Pi 4. The firmware (start4.elf) reads this before it starts the
# kernel. The options: https://www.raspberrypi.com/documentation/computers/config_txt.html
# and, for the older ones used here, .../computers/legacy_config_txt.html. leanos loads no
# device tree and no overlays: the kernel sets up what it needs itself (arch/), and this
# file only makes the firmware leave the board the way the kernel expects.

# The kernel: 64-bit, kernel8.img, loaded at 0x80000, where arch/kernel.ld links it. The
# firmware's default for a 64-bit kernel is 0x200000 (kernel_address), where it cannot run;
# if it ever finds itself anywhere else it lights the green light and stops (arch/boot.S).
arm_64bit=1
kernel=kernel8.img
kernel_address=0x80000

# No device tree ("Disable Device Tree usage": device_tree=), so the peripherals stay at
# 0xFE000000, where the kernel reaches them (arm_peri_high=0, the default without a device
# tree). Without a device tree the firmware would write ATAGs from 0x100; this stops that,
# so the kernel's first page holds only the boot stub and its spin table.
device_tree=
arm_peri_high=0
disable_commandline_tags=1

# Interrupts through the GIC-400, the only controller the kernel drives (enable_gic, Pi 4
# only; 1 is the default). The firmware's boot stub then puts every interrupt in group 1,
# which the kernel, running non-secure, can use.
enable_gic=1

# The serial console on GPIO 14 and 15 (header pins 8 and 10): enable_uart=1 is the
# documented switch for it. The kernel drives the PL011 (UART0) there at 115200 baud and
# routes the pins itself (arch/kmain.c, uart_pins): on a Pi 4 the PL011 is otherwise the
# Bluetooth chip's, and dtoverlay=disable-bt, which would move it, edits a device tree,
# which leanos does not load. The PL011's clock: 48 MHz (init_uart_clock, the default,
# set because the kernel's divisor depends on it; the kernel also asks the firmware).
enable_uart=1
init_uart_clock=48000000
# The firmware's own log on the same pins, before leanos's first line (uart_2ndstage): on a
# first boot it shows whether the firmware found config.txt and kernel8.img, and where it
# put the kernel. Set it to 0 for a quieter boot.
uart_2ndstage=1

# The screen. The kernel asks the firmware for a 1024x600, 32-bit framebuffer through the
# mailbox and checks what it gets; these make the firmware's own framebuffer the same from
# the start: no overscan border, 1024x600, 32 bits with the alpha byte ignored (leanos
# writes 0 there), and HDMI 0 (the micro-HDMI port next to the USB-C power port) in use
# even if the monitor is not detected at power-on (hdmi_force_hotplug). The monitor keeps
# its own mode, from its EDID, and the firmware scales 1024x600 to it. No rainbow splash.
disable_overscan=1
framebuffer_width=1024
framebuffer_height=600
framebuffer_depth=32
framebuffer_ignore_alpha=1
hdmi_force_hotplug=1
disable_splash=1

# Left at their defaults, on purpose:
#   gpu_mem     76 MB on every Pi 4 (all have 1 GB or more): room for the 2.4 MB
#               framebuffer, and the ARM keeps the first 948 MiB, far past the 84 MiB the
#               kernel uses (its image, heap and frame pool; the kernel checks at boot)
#   otg_mode    0: the DWC2 controller, which leanos's USB driver drives, stays on USB-C
#   boot_delay  0
"""



def bringup_config():
    """config.txt for the bring-up card (make pi-bringup): the same as CONFIG, whose kernel
    does the extra reporting, with the firmware's own log forced on even if CONFIG's is
    turned off (tools/serial.py --summary reads where it put the kernel from it)."""
    lines = CONFIG.split(b"\n")
    assert b"uart_2ndstage=1" in lines or b"uart_2ndstage=0" in lines, "CONFIG must set uart_2ndstage"
    lines = [b"uart_2ndstage=1" if l == b"uart_2ndstage=0" else l for l in lines]
    head = (b"# The bring-up card (make pi-bringup): its kernel blinks each boot step on the green light,\n"
            b"# times the steps and prints more of the board; docs/SETUP.md, \"If it does not start\".\n")
    return head + b"\n".join(lines)


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
    bringup = "--bringup" in args
    if bringup:
        args.remove("--bringup")
    specs = args
    needed = ["start4.elf", "fixup4.dat"]
    missing = [f for f in needed if not os.path.exists(os.path.join(firmware, f))]
    if missing:
        sys.exit(f"missing {', '.join(missing)} in build/firmware/: run tools/fetch-firmware.sh first")
    boot_files = [(f, open(os.path.join(firmware, f), "rb").read()) for f in needed]
    boot_files += [("config.txt", bringup_config() if bringup else CONFIG),
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
