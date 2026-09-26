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
> the SD controller, the screen's colors, timings. The serial console shows where it stops.

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
the Pi, connect the screen, and power it on. The first lines start with
`leanos © 2026 Keith Adler`. Keys you type in the serial window go to the window in front.

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
