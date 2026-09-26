/* Loading a program straight from the file server into its image, a piece at a time: no
   copy of the whole file is needed, so a program can be as large as its code run (64 KiB)
   whatever the file server moves in one request. The checks are elf.h's: the same rules,
   applied to the headers from the file's first piece and to each segment as it arrives. */
#pragma once
#include "fs.h"
#include "elf.h"

/* Why the file at `path` is not a program we can run, or 0 (and the image made). */
static inline const char *elf_load(struct fs_client *c, const char *path, unsigned char *image, u64 *len) {
    u64 size = 0;
    long n = fs_read_at(c, path, 0, &size);
    if (n < 0) return "no such file";
    const unsigned char *file = (const unsigned char *)fs_data(c);
    const struct elf64_ehdr *h = (const struct elf64_ehdr *)file;
    if ((u64)n < sizeof *h || file[0] != 0x7f || file[1] != 'E' || file[2] != 'L' || file[3] != 'F')
        return "not an ELF file";
    if (file[4] != 2 || file[5] != 1) return "not a 64-bit little-endian ELF file";
    if (h->machine != EM_AARCH64 || h->type != ET_EXEC) return "not an AArch64 program";
    if (h->entry != IMAGE_BASE) return "does not start at 0x80000000";
    if (h->phentsize != sizeof(struct elf64_phdr) || h->phnum > 16 ||
        h->phoff + (u64)h->phnum * sizeof(struct elf64_phdr) > (u64)n)
        return "bad program headers";
    struct elf64_phdr ph[16];
    unsigned nph = h->phnum;
    for (unsigned i = 0; i < nph; i++) ph[i] = ((const struct elf64_phdr *)(file + h->phoff))[i];
    for (u64 i = 0; i < IMAGE_MAX; i++) image[i] = 0;
    u64 end = 0;
    for (unsigned i = 0; i < nph; i++) {
        const struct elf64_phdr *p = &ph[i];
        if (p->type != PT_LOAD || p->memsz == 0) continue;
        if (p->flags & PF_W) return "has a writable segment (keep state in the data pages)";
        if (p->vaddr < IMAGE_BASE || p->memsz > IMAGE_MAX || p->vaddr - IMAGE_BASE > IMAGE_MAX - p->memsz)
            return "does not fit in the 64 KiB code run";
        if (p->filesz > p->memsz || p->offset > size || p->filesz > size - p->offset)
            return "a segment runs past the end of the file";
        for (u64 done = 0; done < p->filesz;) {
            long got = fs_read_at(c, path, p->offset + done, 0);
            if (got <= 0) return "could not read it";
            u64 take = (u64)got < p->filesz - done ? (u64)got : p->filesz - done;
            const unsigned char *d = (const unsigned char *)fs_data(c);
            for (u64 k = 0; k < take; k++) image[p->vaddr - IMAGE_BASE + done + k] = d[k];
            done += take;
        }
        if (p->vaddr - IMAGE_BASE + p->memsz > end) end = p->vaddr - IMAGE_BASE + p->memsz;
    }
    if (end == 0) return "has nothing to load";
    *len = end;
    return image_marked(image);
}
