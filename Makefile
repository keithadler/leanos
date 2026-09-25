# leanos: a kernel whose decisions are written and proved in Lean 4, for the Raspberry Pi 4.
#
#   make          build build/leanos.elf (and check every proof)
#   make run      boot it in QEMU, headless (serial on the terminal; watch the screen in
#                 the browser console, tools/serve.py)
#   make test     boot it, start the apps, and check the transcripts and the screens
#   make proofs   check the proofs only
#   make mutants  break the kernel on purpose and check the proofs notice

TOOLCHAIN := $(shell cat lean-toolchain | sed 's|/|--|; s|:|---|')
LEAN_HOME := $(HOME)/.elan/toolchains/$(TOOLCHAIN)
LEAN      := $(LEAN_HOME)/bin/lean
# LLVM's bin folder: Homebrew's on macOS, else the system's (override: make LLVM=/path/to/llvm/bin)
LLVM      ?= $(firstword $(wildcard /opt/homebrew/opt/llvm/bin /usr/local/opt/llvm/bin) $(lastword $(sort $(wildcard /usr/lib/llvm-*/bin))) /usr/bin)
CC        := $(LLVM)/clang
LD        := $(firstword $(wildcard $(LLVM)/ld.lld) ld.lld)
OBJCOPY   := $(LLVM)/llvm-objcopy
QEMU      := qemu-system-aarch64

TARGET  := --target=aarch64-none-elf
CFLAGS  := $(TARGET) -ffreestanding -fno-stack-protector -mstrict-align -O2 -g \
           -DNDEBUG -DLEANOS_QEMU -Irt/include -I$(LEAN_HOME)/include -ffunction-sections -fdata-sections
UCFLAGS := $(TARGET) -ffreestanding -fno-stack-protector -mgeneral-regs-only -O2 -fno-pic \
           -Wall -Werror
# Lean's generated C trips warnings that are not ours to fix.
LEANC_FLAGS := $(CFLAGS) -w

# The pieces of Lean's standard library the kernel imports (Init.Core and what it imports).
INIT_MODULES := Prelude Coe Notation SizeOf Tactics Core
INIT_C := $(patsubst %,build/c/Init_%.c,$(INIT_MODULES))
INIT_O := $(INIT_C:.c=.o)

KERNEL_LEAN_C := .lake/build/ir/LeanOS/Kernel.c
USER_PROGS := alice display mallory carol input terminal settings security fs files launcher usb
USER_BINS := $(patsubst %,build/user/%.bin,$(USER_PROGS))

ARCH_O := build/boot.o build/kmain.o build/sd.o build/sha256.o build/runtime.o build/libc.o build/Kernel.o build/Manifest.o

.PHONY: all run test mutants proofs clean pi-image
ASSET_BLOBS := $(patsubst %,build/assets/%.bin,alice display terminal settings security files launcher open)

all: $(ASSET_BLOBS) build/kernel8.img build/sd-template.img build/sd-desktop.img proofs

# The asset blobs are real outputs, not intermediates: a missing one must be rebuilt.
.PRECIOUS: build/assets/%.bin

proofs: LeanOS/Manifest.lean
	lake build

# The boot manifest: what each task must be loaded with (code, then assets), hashed.
MANIFEST_INPUTS := build/user/alice.bin+build/assets/alice.bin build/user/display.bin+build/assets/display.bin \
  build/user/mallory.bin build/user/carol.bin build/user/input.bin \
  build/user/terminal.bin+build/assets/terminal.bin build/user/settings.bin+build/assets/settings.bin \
  build/user/security.bin+build/assets/security.bin build/user/fs.bin \
  build/user/files.bin+build/assets/files.bin \
  "" "" "" "" "" "" build/user/launcher.bin+build/assets/launcher.bin build/user/usb.bin
LeanOS/Manifest.lean: tools/mkmanifest.py $(USER_BINS) $(ASSET_BLOBS)
	python3 tools/mkmanifest.py $@ $(MANIFEST_INPUTS)

$(KERNEL_LEAN_C): LeanOS/Kernel.lean LeanOS/Manifest.lean
	lake build LeanOS.Kernel:c

MANIFEST_LEAN_C := .lake/build/ir/LeanOS/Manifest.c
$(MANIFEST_LEAN_C): LeanOS/Manifest.lean
	lake build LeanOS.Manifest:c

build/Manifest.o: $(MANIFEST_LEAN_C)
	@mkdir -p build
	$(CC) $(LEANC_FLAGS) -c $< -o $@

build/c/Init_%.c: $(LEAN_HOME)/src/lean/Init/%.lean
	@mkdir -p build/c
	$(LEAN) --root=$(LEAN_HOME)/src/lean -c $@ $<

build/c/Init_%.o: build/c/Init_%.c
	$(CC) $(LEANC_FLAGS) -c $< -o $@

build/Kernel.o: $(KERNEL_LEAN_C)
	@mkdir -p build
	$(CC) $(LEANC_FLAGS) -c $< -o $@

build/%.o: arch/%.c arch/arch.h build/user/font.h
	@mkdir -p build
	$(CC) $(CFLAGS) -Ibuild/user -Wall -Werror -c $< -o $@

build/%.o: rt/%.c arch/arch.h
	@mkdir -p build
	$(CC) $(CFLAGS) -Wall -Wno-unused-parameter -c $< -o $@

# Fonts and icons, rasterized and scaled for each task that uses them.
FONTS := assets/fonts
DISPLAY_ASSETS := font:1:$(FONTS)/Inter-Regular.ttf:15 font:2:$(FONTS)/Inter-SemiBold.ttf:15 \
  font:3:$(FONTS)/Inter-Regular.ttf:12 font:4:$(FONTS)/Inter-Bold.ttf:48 font:5:$(FONTS)/Inter-Medium.ttf:17 \
  icon:10:assets/icons/memo_3d.png:52 icon:11:assets/icons/file_folder_3d.png:52 \
  icon:12:assets/icons/laptop_3d.png:52 icon:13:assets/icons/gear_3d.png:52 \
  icon:14:assets/icons/locked_3d.png:52 icon:15:assets/icons/rocket_3d.png:52 \
  icon:16:assets/icons/alarm_clock_3d.png:52 icon:17:assets/icons/abacus_3d.png:52 icon:18:assets/icons/shield_3d.png:52 \
  icon:19:assets/icons/globe_with_meridians_3d.png:52
ALICE_ASSETS := font:5:$(FONTS)/Inter-SemiBold.ttf:20 font:6:$(FONTS)/Inter-Regular.ttf:17 \
  font:3:$(FONTS)/Inter-Regular.ttf:12

build/assets/display.bin: tools/mkassets.py Makefile $(wildcard assets/*/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(DISPLAY_ASSETS)

TERMINAL_ASSETS := font:1:$(FONTS)/JetBrainsMono-Regular.ttf:14
SETTINGS_ASSETS := font:1:$(FONTS)/Inter-Regular.ttf:14 font:2:$(FONTS)/Inter-SemiBold.ttf:16 \
  font:3:$(FONTS)/Inter-Regular.ttf:12
SECURITY_ASSETS := $(SETTINGS_ASSETS)
FILES_ASSETS := $(SETTINGS_ASSETS) font:4:$(FONTS)/JetBrainsMono-Regular.ttf:12
LAUNCHER_ASSETS := font:1:$(FONTS)/Inter-Regular.ttf:13 font:2:$(FONTS)/Inter-SemiBold.ttf:20 \
  font:3:$(FONTS)/Inter-Regular.ttf:12 font:4:$(FONTS)/Inter-SemiBold.ttf:12 \
  icon:10:assets/icons/memo_3d.png:48 icon:11:assets/icons/file_folder_3d.png:48 \
  icon:12:assets/icons/laptop_3d.png:48 icon:13:assets/icons/gear_3d.png:48 \
  icon:14:assets/icons/locked_3d.png:48
# The fonts every program from the SD card gets (user/ui.h names them).
OPEN_ASSETS := font:1:$(FONTS)/Inter-Regular.ttf:15 font:2:$(FONTS)/Inter-SemiBold.ttf:15 \
  font:3:$(FONTS)/Inter-Regular.ttf:12 font:4:$(FONTS)/Inter-Bold.ttf:26 \
  font:5:$(FONTS)/Inter-Medium.ttf:17 font:6:$(FONTS)/JetBrainsMono-Regular.ttf:15 \
  font:7:$(FONTS)/Inter-Bold.ttf:40 font:8:$(FONTS)/Inter-SemiBold.ttf:12

build/assets/alice.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(ALICE_ASSETS)

build/assets/terminal.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(TERMINAL_ASSETS)

build/assets/settings.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(SETTINGS_ASSETS)

build/assets/security.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(SECURITY_ASSETS)

build/assets/files.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(FILES_ASSETS)

build/assets/launcher.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(LAUNCHER_ASSETS)

build/assets/open.bin: tools/mkassets.py Makefile $(wildcard assets/fonts/*)
	@mkdir -p build/assets
	python3 tools/mkassets.py $@ $(OPEN_ASSETS)

build/boot.o: arch/boot.S $(USER_BINS) $(ASSET_BLOBS)
	@mkdir -p build
	$(CC) $(TARGET) -c $< -o $@

build/user/font.h: user/font5x7.txt tools/mkfont.py
	@mkdir -p build/user
	python3 tools/mkfont.py $< $@

build/user/%.elf: user/%.c user/lib.h user/gfx.h user/assets.h user/app.h user/fs.h user/elf.h user/user.ld build/user/font.h
	@mkdir -p build/user
	$(CC) $(UCFLAGS) -Ibuild/user -c $< -o build/user/$*.o
	$(LD) -T user/user.ld --gc-sections build/user/$*.o -o $@

# Programs that live on the SD card, not in the kernel image: stripped ELF files.
DISK_PROGS := hello clock tour calc snake life tiles fuzz edit web
DISK_ELFS := $(patsubst %,build/progs/%.elf,$(DISK_PROGS))
build/progs/%.elf: user/progs/%.c user/lib.h user/gfx.h user/assets.h user/app.h user/user.ld build/user/font.h
	@mkdir -p build/progs
	$(CC) $(UCFLAGS) -Ibuild/user -c $< -o build/progs/$*.o
	$(LD) -T user/user.ld --gc-sections -z max-page-size=16 -z common-page-size=16 build/progs/$*.o -o $@
	$(LLVM)/llvm-strip $@

# A card with welcome.txt and the programs, the way the tests boot (tools/mksd.py).
DISK_DOCS := guide.txt

# Each program's icon, NAME.icon beside it on the card (Fluent Emoji 3D, 56 px).
ICON_SRC_tour := shield_3d
ICON_SRC_calc := abacus_3d
ICON_SRC_snake := snake_3d
ICON_SRC_life := seedling_3d
ICON_SRC_tiles := game_die_3d
ICON_SRC_clock := alarm_clock_3d
ICON_SRC_hello := waving_hand_3d_default
ICON_SRC_fuzz := lady_beetle_3d
ICON_SRC_edit := pencil_3d
ICON_SRC_web := globe_with_meridians_3d
DISK_ICONS := $(patsubst %,build/icons/%.icon,$(DISK_PROGS))
build/icons/%.icon: tools/mkicon.py tools/mkassets.py
	@mkdir -p build/icons
	python3 tools/mkicon.py $@ assets/icons/$(ICON_SRC_$*).png 56
# The card people use: the same, and startup.txt (Apps and the tour open at boot). The tests
# boot the plain card, so they see the system as it starts with nothing asked of it.
build/sd-desktop.img: tools/mksd.py $(DISK_ELFS) $(DISK_ICONS) $(patsubst %,docs/card/%,$(DISK_DOCS)) docs/card/startup.txt
	python3 tools/mksd.py $@ $(foreach p,$(DISK_PROGS),$(p)=build/progs/$(p).elf) \
	  $(foreach p,$(DISK_PROGS),$(p).icon=build/icons/$(p).icon) $(foreach d,$(DISK_DOCS),$(d)=docs/card/$(d)) \
	  startup.txt=docs/card/startup.txt
build/sd-template.img: tools/mksd.py $(DISK_ELFS) $(DISK_ICONS) $(patsubst %,docs/card/%,$(DISK_DOCS))
	python3 tools/mksd.py $@ $(foreach p,$(DISK_PROGS),$(p)=build/progs/$(p).elf) \
	  $(foreach p,$(DISK_PROGS),$(p).icon=build/icons/$(p).icon) $(foreach d,$(DISK_DOCS),$(d)=docs/card/$(d))

# An SD card image a Raspberry Pi 4 boots (tools/mkpiimage.py); the firmware files come from
# tools/fetch-firmware.sh, which you run once.
pi-image: build/pi/kernel8.img $(DISK_ELFS) $(DISK_ICONS) tools/mkpiimage.py tools/mksd.py
	python3 tools/mkpiimage.py build/leanos-pi4.img --kernel build/pi/kernel8.img \
	  $(foreach p,$(DISK_PROGS),$(p)=build/progs/$(p).elf) $(foreach p,$(DISK_PROGS),$(p).icon=build/icons/$(p).icon) \
	  $(foreach d,$(DISK_DOCS),$(d)=docs/card/$(d)) startup.txt=docs/card/startup.txt

# The kernel for a real Pi: the same, except that switching off halts instead of ending the
# emulator through semihosting (a Pi has no debugger to take that call).
build/pi/kmain.o: arch/kmain.c arch/arch.h build/user/font.h
	@mkdir -p build/pi
	$(CC) $(filter-out -DLEANOS_QEMU,$(CFLAGS)) -Ibuild/user -Wall -Werror -c $< -o $@

PI_ARCH_O := $(filter-out build/kmain.o,$(ARCH_O)) build/pi/kmain.o
build/pi/kernel8.img: $(PI_ARCH_O) $(INIT_O) arch/kernel.ld
	$(LD) -T arch/kernel.ld --gc-sections $(PI_ARCH_O) $(INIT_O) -o build/pi/leanos.elf
	$(OBJCOPY) -O binary build/pi/leanos.elf $@

build/user/%.bin: build/user/%.elf
	$(OBJCOPY) -O binary $< $@

build/leanos.elf: $(ARCH_O) $(INIT_O) arch/kernel.ld
	$(LD) -T arch/kernel.ld --gc-sections $(ARCH_O) $(INIT_O) -o $@
	@$(LLVM)/llvm-size $@

# The raw image the Pi firmware (and QEMU's raspi4b) loads at 0x80000.
build/kernel8.img: build/leanos.elf
	$(OBJCOPY) -O binary $< $@

# The SD card: an 8 MiB image, made once and kept, so files survive a reboot.
SD_IMAGE := build/sd.img
$(SD_IMAGE): build/sd-desktop.img
	cp build/sd-desktop.img $@

QEMU_ARGS := -M raspi4b -display none -serial stdio -semihosting -kernel build/kernel8.img \
  -drive if=sd,format=raw,file=$(SD_IMAGE) -device usb-net,netdev=n0 -netdev user,id=n0

run: build/kernel8.img $(SD_IMAGE)
	$(QEMU) $(QEMU_ARGS)

test: all
	./test/boot.sh
	./test/apps.sh
	./test/programs.sh
	./test/power.sh
	./test/piimage.sh
	./test/tamper.sh
	./test/fuzz.sh
	./test/usb.sh
	./test/touch.sh
	./test/crash.sh
	./test/bigprog.sh
	./test/edit.sh
	./test/net.sh
	./test/kill.sh
	./test/web.sh

# Break the kernel in known ways and check the proofs catch every one (slow).
mutants:
	./test/mutants.sh

clean:
	rm -rf build .lake/build
.SECONDARY:
