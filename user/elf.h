/* Reading a program from an ELF file, in user space: the kernel never parses ELF. The
   loader (Terminal) turns the file into the flat image `exec` takes: the bytes of every
   loadable segment at their place in the code run, which user mode sees at 0x80000000.

   A program runs from its code run, which is read and execute only, and keeps its state in
   its data pages (from 0x80010000), as the programs in the kernel image do. So a segment
   may not be writable, must lie inside the code run, and the program must start at the
   start of it. */
#pragma once
#include "lib.h"

#define IMAGE_BASE 0x80000000UL
#define IMAGE_MAX (16 * 4096UL)

struct elf64_ehdr {
    unsigned char ident[16];
    unsigned short type, machine;
    unsigned version;
    u64 entry, phoff, shoff;
    unsigned flags;
    unsigned short ehsize, phentsize, phnum, shentsize, shnum, shstrndx;
};

struct elf64_phdr {
    unsigned type, flags;
    u64 offset, vaddr, paddr, filesz, memsz, align;
};

enum { PT_LOAD = 1, PF_W = 2, EM_AARCH64 = 183, ET_EXEC = 2 };

/* A program's icon rides in the last four pages of its image, after a marker, with the name
   of the file it came from at the very end, where the program finds them (app_open in
   app.h) and lends them to the display server: the icon for its title bar and the dock, the
   name so that starting it again brings this window forward instead of a second copy. */
#define ICON_IMAGE_PAGE 12
#define ICON_MAGIC 0x43494e4cu          /* "LNIC" */
#define ICON_NAME_AT (4 * 4096UL - 16)  /* the name: 15 bytes and a 0 */
#define ICON_MAX (ICON_NAME_AT - 8)

/* Add an icon file's bytes (tools/mkicon.py, or none: size 0) and the program's name to an
   image; the image grows to the whole code run. Nothing happens if the program itself
   reaches into those pages. */
static inline void image_add_icon(unsigned char *image, u64 *len, const unsigned char *icon, u64 size,
                                  const char *name) {
    if (*len > ICON_IMAGE_PAGE * 4096UL || (size && size < 8) || size > ICON_MAX) return;
    unsigned char *at = image + ICON_IMAGE_PAGE * 4096UL;
    unsigned *head = (unsigned *)at;
    head[0] = ICON_MAGIC;
    head[1] = (unsigned)size;
    for (u64 i = 0; i < size; i++) at[8 + i] = icon[i];
    for (u64 i = 0; i < 16; i++) at[ICON_NAME_AT + i] = 0;
    for (u64 i = 0; i < 15 && name[i]; i++) at[ICON_NAME_AT + i] = (unsigned char)name[i];
    *len = IMAGE_MAX;
}

/* Why a file is not a program we can run, or 0. */
static inline const char *elf_image(const unsigned char *file, u64 size, unsigned char *image, u64 *len) {
    const struct elf64_ehdr *h = (const struct elf64_ehdr *)file;
    if (size < sizeof *h || file[0] != 0x7f || file[1] != 'E' || file[2] != 'L' || file[3] != 'F')
        return "not an ELF file";
    if (file[4] != 2 || file[5] != 1) return "not a 64-bit little-endian ELF file";
    if (h->machine != EM_AARCH64 || h->type != ET_EXEC) return "not an AArch64 program";
    if (h->entry != IMAGE_BASE) return "does not start at 0x80000000";
    if (h->phentsize != sizeof(struct elf64_phdr) || h->phoff > size ||
        (u64)h->phnum * sizeof(struct elf64_phdr) > size - h->phoff)
        return "bad program headers";
    u64 end = 0;
    for (u64 i = 0; i < IMAGE_MAX; i++) image[i] = 0;
    for (unsigned i = 0; i < h->phnum; i++) {
        const struct elf64_phdr *p = (const struct elf64_phdr *)(file + h->phoff) + i;
        if (p->type != PT_LOAD || p->memsz == 0) continue;
        if (p->flags & PF_W) return "has a writable segment (keep state in the data pages)";
        if (p->vaddr < IMAGE_BASE || p->memsz > IMAGE_MAX || p->vaddr - IMAGE_BASE > IMAGE_MAX - p->memsz)
            return "does not fit in the 64 KiB code run";
        if (p->filesz > p->memsz || p->offset > size || p->filesz > size - p->offset)
            return "a segment runs past the end of the file";
        for (u64 k = 0; k < p->filesz; k++) image[p->vaddr - IMAGE_BASE + k] = file[p->offset + k];
        if (p->vaddr - IMAGE_BASE + p->memsz > end) end = p->vaddr - IMAGE_BASE + p->memsz;
    }
    if (end == 0) return "has nothing to load";
    *len = end;
    return 0;
}
