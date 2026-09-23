/* Machine layer shared definitions: Raspberry Pi 4 Model B (BCM2711, Cortex-A72),
   in the default "low peripheral" address map. */
#pragma once
#include <stdint.h>
#include <stddef.h>

/* Physical memory: RAM starts at 0. The kernel image sits at 0x8_0000 (where the Pi
   firmware loads kernel8.img) with its heap after it; user frames start at FRAME_BASE. */
#define FRAME_BASE 0x04000000UL
#define PAGE_SIZE 4096UL
#define MAX_TASKS 8
#define FRAMES_PER_TASK 256
#define SPARE_FIRST 28     /* the spare run starts 28 frames into a task's frames */
#define SPARE_PAGES 228
#define NFRAMES (FRAMES_PER_TASK * MAX_TASKS)

/* Every task sees its 8192 user pages (32 MiB) at the same virtual window (the same
   numbers `userBase` and `userPages` in LeanOS/Kernel.lean), through 16 level-3 tables. */
#define USER_BASE 0x80000000UL
#define USER_PAGES 8192
#define CODE_PAGES 16

#define PERIPHERAL_BASE 0xFE000000UL
#define UART0 (PERIPHERAL_BASE + 0x201000) /* PL011 */
#define GICD 0xFF841000UL                    /* GIC-400 distributor */
#define GICC 0xFF842000UL                    /* GIC-400 CPU interface */
#define TIMER_IRQ 30 /* EL1 physical timer, a private peripheral interrupt */

/* The registers a trap saves: x0-x30, the user stack pointer, return address, and state.
   The layout matches arch/boot.S. */
struct frame {
    uint64_t x[31];
    uint64_t sp, elr, spsr;
    uint64_t pad[2];
};

void kputc(char c);
void kputs(const char *s);
void kputhex(uint64_t v);
void kputdec(uint64_t v);
__attribute__((noreturn)) void kpanic(const char *msg);
__attribute__((noreturn)) void poweroff(void);

__attribute__((noreturn)) void enter_user(struct frame *f);

void *memcpy(void *d, const void *s, size_t n);
void *memset(void *d, int c, size_t n);
void *memmove(void *d, const void *s, size_t n);
int memcmp(const void *a, const void *b, size_t n);

#define SYSREG_READ(name) ({ uint64_t _v; __asm__ volatile("mrs %0, " #name : "=r"(_v)); _v; })
#define SYSREG_WRITE(name, v) __asm__ volatile("msr " #name ", %0" :: "r"((uint64_t)(v)))
#define ISB() __asm__ volatile("isb" ::: "memory")
#define DSB(opt) __asm__ volatile("dsb " #opt ::: "memory")

static inline void mmio_w32(uint64_t a, uint32_t v) { *(volatile uint32_t *)a = v; }
static inline uint32_t mmio_r32(uint64_t a) { return *(volatile uint32_t *)a; }
static inline void mmio_w8(uint64_t a, uint8_t v) { *(volatile uint8_t *)a = v; }
