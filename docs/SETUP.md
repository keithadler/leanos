# Setting up leanos by hand

This guide takes you from nothing to leanos running, first in an emulated Raspberry Pi 4 on
your computer (about 15 minutes, most of it downloads), then, if you want, on a real Pi 4.

- [1. Install the tools](#1-install-the-tools)
- [2. Get the code and build it](#2-get-the-code-and-build-it)
- [3. Run it in your browser](#3-run-it-in-your-browser)
- [4. Other ways to run it](#4-other-ways-to-run-it)
- [5. Run it on a real Raspberry Pi 4](#5-run-it-on-a-real-raspberry-pi-4)
- [6. Troubleshooting](#6-troubleshooting)

## 1. Install the tools

You need five things:

| Tool | Why | Version |
|---|---|---|
| **Lean 4**, through **elan** | builds the kernel and checks every proof | picked automatically from `lean-toolchain` |
| **LLVM**: `clang`, `ld.lld`, `llvm-objcopy`, `llvm-strip` | cross-compiles the kernel and programs for the Pi's 64-bit Arm | any recent (tested with 23) |
| **QEMU** with `qemu-system-aarch64` | emulates the Raspberry Pi 4 | **9.0 or later** (the `raspi4b` machine is new in 9.0) |
| **Python 3** | builds fonts, icons and SD card images; runs the tests and the browser console | 3.9 or later, no extra packages |
| **make**, **git**, **curl** | the build | any |

### macOS

Install [Homebrew](https://brew.sh) if you do not have it, then:

```bash
brew install llvm lld qemu python git
```

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Accept the defaults, then open a new terminal window (so `lake` is on your `PATH`). `make`
comes with Apple's Command Line Tools: if it is missing, run `xcode-select --install`.

### Linux (Debian 13, Ubuntu 25.04 or newer)

```bash
sudo apt install clang lld llvm qemu-system-arm python3 make git curl
```

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Then open a new terminal. Check QEMU is new enough:

```bash
qemu-system-aarch64 --version
```

If it says 8.x (Ubuntu 24.04 ships 8.2), it cannot emulate a Pi 4. Build a newer QEMU from
[qemu.org](https://www.qemu.org/download/) (`./configure --target-list=aarch64-softmmu &&
make`), or use a newer distribution.

### Check everything

```bash
lake --version && qemu-system-aarch64 --version && python3 --version
```

`make` looks for LLVM in Homebrew's folder, then the newest `/usr/lib/llvm-*`. If it cannot
find `clang` or `llvm-objcopy`, tell it where LLVM is, for example
`make LLVM=/usr/lib/llvm-19/bin`.

## 2. Get the code and build it

```bash
git clone https://github.com/keithadler/leanos.git
```

```bash
cd leanos
```

```bash
make
```

The first `make` downloads the Lean version the project pins (a few hundred MB, once),
then builds everything and checks every proof: a minute or two on a recent computer. It
ends with `Build completed successfully`. You now have:

- `build/kernel8.img`: the kernel, with the Lean kernel and all built-in programs in it
- `build/sd-desktop.img`: an SD card with the programs, the guide, and `startup.txt`
- `build/sd-template.img`: the same card without `startup.txt`, which the tests use

## 3. Run it in your browser

```bash
python3 tools/serve.py
```

Open **http://127.0.0.1:8796** and click **Boot** if it is not running already. QEMU's
Pi 4 starts with no window of its own; the page shows its screen live and the serial
console below it. The page loads its VNC viewer (noVNC) from a CDN, so the browser needs to
be online the first time.

After a few seconds you see the desktop, with the **Tour** in front and **Apps** behind it.

- **Click the screen** first, then type: keys go to the window in front.
- **Drag** a window by its title bar; the red dot closes it.
- The **dock** at the bottom starts apps: Notes, Files, Terminal, Settings, Security,
  Apps, Clock, Calculator, Tour, and the globe, which is **Web**.
- In **Terminal**, type `help`. Try `ps`, `caps`, `date`, `ls`, `ping 10.0.2.2`,
  `run snake`, or `run edit notes.txt`.
- In **Web**, type `info.cern.ch` and press Enter. It shows plain `http://` pages as text;
  most sites are `https://`, which it cannot open yet.

The emulated Pi has a USB network adapter on QEMU's user network, so it gets an address,
sets its clock from the internet, and reaches the web through your computer.

**Your files stay.** The emulated SD card is `build/sd.img`, and it is kept between boots.
When `make` builds newer programs, the next boot starts from a fresh card and keeps the old
one as `build/sd-old.img`.

**Stop** stops the emulator. Press Ctrl-C in the terminal to stop the server.

### What opens at startup

`startup.txt` on the card lists what opens at boot, one name per line or separated by
spaces: `apps` is the Apps window, anything else is a program on the card, and the last one
ends up in front. To change it, in Terminal:

```
write startup.txt apps web
```

## 4. Other ways to run it

Headless, with the serial console in your terminal (Ctrl-C quits):

```bash
make run
```

The whole test suite (about 2 to 3 minutes on a 10-core Mac; it boots the system many times
and checks what it prints and what is on the screen). It runs up to four tests at once, half
your cores at most; `make test JOBS=1` runs them one after the other (about 9 minutes), and
each test's output stays in `build/test/NAME/output.txt`:

```bash
make test
```

The mutation check: breaks the kernel in 108 ways and checks the proofs reject every one
(about 3 minutes on a 10-core Mac):

```bash
make mutants
```

## 5. Run it on a real Raspberry Pi 4

> leanos has not booted on real hardware yet. Expect to help find what QEMU does not model:
> the SD controller, the screen, timings. The serial console shows where it stops: see
> [First boot on a real Pi 4: what to expect](#first-boot-on-a-real-pi-4-what-to-expect).

### What you need

- A **Raspberry Pi 4 Model B** (any memory size) and its **USB-C power supply**
- A **microSD card** (any size; leanos uses the first 128 MiB, and everything on it is
  erased) and a card reader
- An **HDMI screen** and a **micro-HDMI to HDMI** cable. leanos draws at 1024×600, so a
  7-inch 1024×600 screen matches exactly; others scale it.
- A **3.3 V USB-to-serial cable** (for example Adafruit 954, or FTDI TTL-232R-3V3). Today
  this is how you type into leanos on a Pi and how you see its boot log: the Pi 4's USB-A
  ports need a driver leanos does not have yet. Never use a 5 V cable.

### Build the card image

```bash
tools/fetch-firmware.sh
```

This downloads the Pi's boot firmware (`start4.elf`, `fixup4.dat`) from the Raspberry Pi
Foundation's GitHub, once. leanos does not include it.

```bash
make pi-image
```

This writes `build/leanos-pi4.img`: a FAT boot partition with the firmware, `config.txt`
and the kernel, then leanos's data partition with the programs.

### Write it to the card

The easy way: [Raspberry Pi Imager](https://www.raspberrypi.com/software/), then
**Choose OS**, **Use custom**, pick `build/leanos-pi4.img`, choose your card, and write.

By hand on macOS (be sure of the disk number: `dd` erases whatever it is given):

```bash
diskutil list
```

```bash
diskutil unmountDisk /dev/diskN
```

```bash
sudo dd if=build/leanos-pi4.img of=/dev/rdiskN bs=4m
```

On Linux, find the card with `lsblk` and use `of=/dev/sdX bs=4M conv=fsync`.

### Wire the serial cable

| Serial cable | Pi 4 header |
|---|---|
| GND (black) | pin 6 (ground) |
| RX (white on Adafruit's) | pin 8 (GPIO 14, the Pi's TX) |
| TX (green on Adafruit's) | pin 10 (GPIO 15, the Pi's RX) |

Leave the cable's power wire (red) unconnected: the Pi has its own supply. Then open the
serial port at 115200 baud, for example:

```bash
screen /dev/tty.usbserial-XXXX 115200
```

(`ls /dev/tty.usb*` on macOS or `ls /dev/ttyUSB*` on Linux shows the name.) Put the card in
the Pi, connect the screen to **HDMI 0** (the micro-HDMI port next to the USB-C power port),
and power it on. The firmware's own log comes first, then leanos's, from
`leanos © 2026 Keith Adler`. Keys you type in the serial window go to the window in front.

The card's `config.txt` is written by `tools/mkpiimage.py`, where each line is explained.

### First boot on a real Pi 4: what to expect

leanos has so far run only on QEMU, which is more forgiving than the chip: it has no caches
to keep coherent, accepts any clock divisor, never pads a framebuffer row, and answers every
mailbox request at once. Everything that could differ on a real board is checked at boot
and printed, so the serial console says where it stops and why. Below is each step in
order: what the console prints when it goes well, and what to try if it stops there. The
values in angle brackets depend on your board.

**0. The firmware.** With `uart_2ndstage=1` (set in the card's `config.txt`), the firmware
prints its own log first, on the same pins: it names the files it reads, `config.txt` and
then `kernel8.img`, and where it puts the kernel, which must be `0x80000`.

| If it stops here | Try |
|---|---|
| Nothing on the serial console at all | Check the wiring: the cable's RX goes to pin 8, its TX to pin 10, ground to pin 6; 115200 baud, 8N1, no flow control. Look at the green light: a repeating pattern of flashes is the bootloader's error code (Raspberry Pi's documentation, "LED warning codes"): 4 short flashes mean `start4.elf` was not found (run `tools/fetch-firmware.sh`, then `make pi-image` again), 7 short the kernel image, 2 long then 1 short a boot partition that is not FAT. The Pi 4's bootloader EEPROM may also need updating with Raspberry Pi Imager's "Bootloader" image. |
| The firmware's log, then nothing, and the **green light stays on** | The kernel was loaded somewhere other than `0x80000` and stopped at once (it turns the light on when it finds itself elsewhere, since at the wrong address it cannot drive the UART). Check `kernel_address=0x80000` is still in `config.txt`. |
| The firmware's log, then nothing, light off | The kernel stopped before its first line. Note the firmware's last lines and try another firmware release: `tools/fetch-firmware.sh TAG`, with a release tag from github.com/raspberrypi/firmware, then `make pi-image`. |

**1. The console and the board.**

```
leanos © 2026 Keith Adler
leanos: Raspberry Pi 4, booting on EL1
leanos: board revision <0xc03111>, firmware <0x...>
leanos: serial console: PL011, 115200 baud from a 48000000 Hz clock (the firmware's)
leanos: system counter: 54000000 Hz
leanos: RAM for the ARM: 0x0 to <0x3b400000>
leanos: USB controller powered on
```

| If you see | It means, and what to try |
|---|---|
| Garbage instead of text | The UART's clock is not what the kernel divides: the clock line says which it used. Keep `init_uart_clock=48000000` in `config.txt`. |
| `booting on EL?` | The firmware's boot stub left the core at an exception level leanos does not expect. Report it with the firmware's log. |
| `the firmware does not answer the mailbox` | Nothing that uses the firmware will work (screen, SD clock, USB power); leanos goes on without them. Try another firmware release. |
| `system counter: ... (assumed: CNTFRQ_EL0 was not set)` | The boot stub did not set the counter's rate; leanos assumes 54 MHz, the Pi 4's crystal. Timing may be off if that is wrong. |
| `PANIC: the firmware left the ARM RAM from ...` | Too much memory went to the GPU: remove any `gpu_mem` line you added. leanos needs the first 84 MiB. |
| `the firmware did not power the USB controller on` | USB will not work; everything else goes on. |

**2. The screen.**

```
leanos: the firmware's framebuffer: 1024x600 (screen 1024x600), 32 bits, pitch 4096, BGR, alpha mode 2, 2457600 bytes at bus address <0xfe...>
leanos: framebuffer 1024x600 at <0x3e...>
leanos: MMU on
```

| If you see | It means, and what to try |
|---|---|
| `no framebuffer: ...` | The firmware gave no usable screen; leanos runs without one (the serial console still works). Check the monitor is on HDMI 0 and `hdmi_force_hotplug=1` is in `config.txt`. |
| `PANIC: the firmware's framebuffer has rows of N bytes, not 4096` (also on the screen) | The firmware pads each row; the display server cannot draw on that yet. Please report the line: it needs a kernel change. |
| `PANIC: the firmware gave a WxH framebuffer, not 1024x600`, or one about its size or address | The firmware did not honor the request; report it with the framebuffer line above it. |
| `the firmware kept RGB pixel order: red and blue will look swapped` | leanos runs, with red and blue swapped. Report it. |
| `the firmware kept alpha reversed` | The screen may stay black while everything else works. Report it. |
| The framebuffer lines look right but the screen is black or says "no signal" | The monitor may not like the mode the firmware picked. Try adding `hdmi_safe=1`, or `hdmi_group=2` and `hdmi_mode=16` (1024x768 at 60 Hz), to `config.txt`. |
| Nothing after the framebuffer line (no `MMU on`) | Turning on the MMU and caches failed. Report it. |

**3. The SD card.** Each step of bringing up the Pi 4's SD controller (EMMC2) is printed:

```
leanos: SD: EMMC2: SDHCI 3.0, base clock <100000> kHz (the firmware's)
leanos: SD: EMMC2: I/O lines at 3.3 V
leanos: SD: EMMC2: identification clock <400> kHz
leanos: SD: EMMC2: an SDHC or SDXC card, powered up after <N> ms
leanos: SD: EMMC2: ready, transfer clock 25000 kHz
leanos: SD card ready, data partition of 63 MiB
```

A failed step says which command got no answer (`no answer to CMD0`, `no card answered CMD8
or ACMD41`, `the card did not finish powering up within a second`, and so on), then leanos
tries the older EMMC controller (on a Pi 4 it holds the Wi-Fi chip, not a card, so it fails
too) and goes on with `leanos: no SD card`: files stay in memory, and everything else works.
A block that fails later prints `leanos: SD: read of block N failed, interrupt status 0x...`.
Try another card (a plain SDHC card of 32 GB or less is the simplest case), and report the
lines.

**4. The programs and the cores.**

```
leanos: Lean kernel initialized, 18 tasks
leanos: alice verified, sha256 <0x...>...
...
leanos: core 1 up
leanos: core 2 up
leanos: core 3 up
```

The screen shows the boot checks, then the desktop. If a `core N up` line is missing, that
core did not leave the firmware's spin table; leanos runs on the cores that came up. Report
it.

**5. Input.** Keys typed on the serial console go to the window in front, as in the browser.
`usb: nothing plugged in` is expected: a keyboard on the USB-A ports needs a driver for their
controller (the VL805, over PCIe), which leanos does not have, and the USB-C port is the Pi's
power input, which gives a device plugged into it no power.

When you report a first boot, include the whole serial log, from the firmware's first line.

## 6. Troubleshooting

| What you see | What to do |
|---|---|
| `lake: command not found` | Open a new terminal after installing elan, or run `source ~/.elan/env`. |
| `clang: No such file or directory` or `llvm-objcopy: No such file` | Point `make` at LLVM: `make LLVM=/path/to/llvm/bin` (`brew --prefix llvm` shows it on macOS). |
| `ld.lld: command not found` | Install `lld` (`brew install lld`, or `apt install lld`). |
| QEMU: `unsupported machine type "raspi4b"` | Your QEMU is older than 9.0; see [Linux](#linux-debian-13-ubuntu-2504-or-newer). |
| The browser page stays black | The page loads noVNC from cdn.jsdelivr.net: check the browser is online. Check the terminal running `serve.py` for errors. |
| `Address already in use` from `serve.py` | Another copy is running: stop it, or anything else on port 8796. |
| Keys do nothing in the browser | Click the screen first; keys go to the window in front. |
| `make test` fails on "drawing speed" | The timing check is loose but can trip on a very busy machine: run it again, or with fewer tests at once (`make test JOBS=2`). |

Still stuck? Open an issue with what you ran and what it printed.
