/* Boot progress (arch/bootcon.c): the steps kmain takes, shown on every output that may
   work on a board that has never booted leanos before. Mechanism only, like the rest of
   the machine layer: it reports, it decides nothing. */
#pragma once
#include <stdint.h>

/* The boot steps, in the order kmain takes them. Each is announced before it runs, so the
   last one shown is where the boot is (or where it stopped). docs/SETUP.md has the table. */
enum {
    STAGE_UART = 1,     /* the serial console */
    STAGE_BOARD,        /* the board, as the firmware's mailbox reports it; USB power */
    STAGE_LEAN,         /* the Lean runtime and the kernel's Lean module */
    STAGE_FB,           /* the framebuffer, from the firmware's mailbox */
    STAGE_MMU,          /* the MMU and the caches */
    STAGE_SD,           /* the SD card and its partition table */
    STAGE_STATE,        /* the Lean kernel's first state */
    STAGE_MEMORY,       /* the task frames cleared, the SHA-256 self-test */
    STAGE_PROGRAMS,     /* the programs loaded and checked against the manifest */
    STAGE_TABLES,       /* every task's page tables */
    STAGE_IRQ,          /* the interrupt controller and the timer */
    STAGE_CORES,        /* cores 1-3 released */
    STAGE_FIRST,        /* the first task: the display server takes the screen */
    BOOT_STAGES = STAGE_FIRST,
    STAGE_RUNNING       /* after boot (a panic's blink code only; never printed) */
};

/* Set while the boot console records what the kernel prints (kputc feeds it). */
extern int bootcon_on;
void bootcon_putc(char c);
void bootcon_uart_stuck(void);              /* kputc gave up on the UART: say so on screen */

void boot_led_on(void);                     /* the first sign of life, before the UART */
void boot_led_code(unsigned stage);         /* a stage's blink code before its line exists */
void boot_stage(unsigned stage);            /* "leanos: [n/13] ..." on serial and screen */
void bootcon_start(uint32_t *fb, uint32_t w, uint32_t h, uint32_t stride);
void bootcon_end(void);                     /* the display server takes the screen */
void boot_board_info(void);                 /* bring-up builds: more of the board */

/* Panics and exceptions. */
void boot_panic_begin(void);
void boot_panic_where(void);
void boot_panic_screen(uint32_t *fb, uint32_t w, uint32_t h, uint32_t stride, uint32_t y);
const char *boot_exception(uint64_t kind, uint64_t esr, uint64_t elr, uint64_t far);
__attribute__((noreturn)) void boot_halt(void);
