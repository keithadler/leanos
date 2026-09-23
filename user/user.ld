/* A user program is up to 16 read/execute pages at the start of the user window. It may
   not have writable globals: its only writable memory is the data and stack runs. */
ENTRY(_start)
SECTIONS
{
    . = 0x80000000;
    .text : { KEEP(*(.text.start)) *(.text .text.*) *(.rodata .rodata.*) }
    .data : { *(.data .data.*) *(.bss .bss.*) *(COMMON) }
    ASSERT(SIZEOF(.data) == 0, "user programs cannot have writable globals")
    ASSERT(SIZEOF(.text) <= 65536, "user program is larger than its 16-page code run")
    /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
