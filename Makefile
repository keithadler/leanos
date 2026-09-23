# leanos: a kernel whose decisions are written and proved in Lean 4, for the Raspberry Pi 4.
#
#   make          build build/leanos.elf (and check every proof)
#   make run      boot it in QEMU, headless (serial on the terminal; watch the screen in
#                 the browser console, tools/serve.py)
#   make test     boot it and check the transcript
#   make proofs   check the proofs only
#   make mutants  break the kernel on purpose and check the proofs notice

TOOLCHAIN := $(shell cat lean-toolchain | sed 's|/|--|; s|:|---|')
LEAN_HOME := $(HOME)/.elan/toolchains/$(TOOLCHAIN)
LEAN      := $(LEAN_HOME)/bin/lean
LLVM      := /opt/homebrew/opt/llvm/bin
CC        := $(LLVM)/clang
LD        := ld.lld
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
USER_PROGS := alice display mallory carol
USER_BINS := $(patsubst %,build/user/%.bin,$(USER_PROGS))

ARCH_O := build/boot.o build/kmain.o build/runtime.o build/libc.o build/Kernel.o

.PHONY: all run test mutants proofs clean
all: build/kernel8.img proofs

proofs:
	lake build

$(KERNEL_LEAN_C): LeanOS/Kernel.lean
	lake build LeanOS.Kernel:c

build/c/Init_%.c: $(LEAN_HOME)/src/lean/Init/%.lean
	@mkdir -p build/c
	$(LEAN) --root=$(LEAN_HOME)/src/lean -c $@ $<

build/c/Init_%.o: build/c/Init_%.c
	$(CC) $(LEANC_FLAGS) -c $< -o $@

build/Kernel.o: $(KERNEL_LEAN_C)
	@mkdir -p build
	$(CC) $(LEANC_FLAGS) -c $< -o $@

build/%.o: arch/%.c arch/arch.h
	@mkdir -p build
	$(CC) $(CFLAGS) -Wall -Werror -c $< -o $@

build/%.o: rt/%.c arch/arch.h
	@mkdir -p build
	$(CC) $(CFLAGS) -Wall -Wno-unused-parameter -c $< -o $@

build/boot.o: arch/boot.S $(USER_BINS)
	@mkdir -p build
	$(CC) $(TARGET) -c $< -o $@

build/user/font.h: user/font5x7.txt tools/mkfont.py
	@mkdir -p build/user
	python3 tools/mkfont.py $< $@

build/user/%.elf: user/%.c user/lib.h user/gfx.h user/user.ld build/user/font.h
	@mkdir -p build/user
	$(CC) $(UCFLAGS) -Ibuild/user -c $< -o build/user/$*.o
	$(LD) -T user/user.ld --gc-sections build/user/$*.o -o $@

build/user/%.bin: build/user/%.elf
	$(OBJCOPY) -O binary $< $@

build/leanos.elf: $(ARCH_O) $(INIT_O) arch/kernel.ld
	$(LD) -T arch/kernel.ld --gc-sections $(ARCH_O) $(INIT_O) -o $@
	@$(LLVM)/llvm-size $@

# The raw image the Pi firmware (and QEMU's raspi4b) loads at 0x80000.
build/kernel8.img: build/leanos.elf
	$(OBJCOPY) -O binary $< $@

QEMU_ARGS := -M raspi4b -display none -serial stdio -semihosting -kernel build/kernel8.img

run: build/kernel8.img
	$(QEMU) $(QEMU_ARGS)

test: all
	./test/boot.sh

# Break the kernel in known ways and check the proofs catch every one (slow).
mutants:
	./test/mutants.sh

clean:
	rm -rf build .lake/build
.SECONDARY:
