/* A user program is one read/execute page at the start of the user window. It may not
   have writable globals: its only writable memory is the data and stack frames. */
ENTRY(_start)
SECTIONS
{
    . = 0x80000000;
    .text : { KEEP(*(.text.start)) *(.text .text.*) *(.rodata .rodata.*) }
    .data : { *(.data .data.*) *(.bss .bss.*) *(COMMON) }
    ASSERT(SIZEOF(.data) == 0, "user programs cannot have writable globals")
    ASSERT(SIZEOF(.text) <= 4096, "user program is larger than one page")
    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
