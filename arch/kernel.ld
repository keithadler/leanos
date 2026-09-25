ENTRY(_start)
SECTIONS
{
    . = 0x80000;
    .text : { KEEP(*(.text.boot)) *(.text .text.*) }
    .rodata : { *(.rodata .rodata.*) }
    .data : { *(.data .data.*) }
    .bss (NOLOAD) : ALIGN(16) {
        __bss_start = .;
        *(.bss .bss.*) *(COMMON)
        . = ALIGN(8);
        __bss_end = .;
    }
    . = ALIGN(4096);
    __stack_bottom = .;
    . += 0x10000;           /* 64 KiB (kmain.c: STACK_SIZE); the Lean kernel's list walks are loops */
    __stack_top = .;
    __core_stacks = .;      /* cores 1-3: the same again each (kmain.c: start_cores) */
    . += 0x30000;
    __core_stacks_end = .;
    __heap_start = .;
    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
