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
    . += 0x200000;          /* 2 MiB: the Lean kernel recurses once per list element */
    __stack_top = .;
    __heap_start = .;
    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
