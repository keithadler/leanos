/* The SD card, through the SDHCI controller, one 512-byte block at a time, by programmed
 * I/O. Never DMA: the controller can be told to write anywhere in physical memory, so it
 * stays here in the machine layer, which only ever asks it to move the bytes the Lean
 * kernel approved (a block in the caller's block capability, 512 bytes in a page the
 * caller has mapped with the right permission) through the data port, word by word.
 *
 * The Pi 4's SD slot is on EMMC2; QEMU's raspi4b puts the card on the older EMMC
 * controller. EMMC2 is tried first, then EMMC. Only QEMU has run this so far. */
#include "arch.h"

void kputs(const char *s);
void kputdec(uint64_t v);

#define EMMC2 0xFE340000UL
#define EMMC  0xFE300000UL

enum {
    ARG2 = 0x00, BLKSIZECNT = 0x04, ARG1 = 0x08, CMDTM = 0x0C, RESP0 = 0x10, RESP1 = 0x14,
    RESP2 = 0x18, RESP3 = 0x1C, DATA = 0x20, STATUS = 0x24, CONTROL0 = 0x28, CONTROL1 = 0x2C,
    INTERRUPT = 0x30, IRPT_MASK = 0x34, IRPT_EN = 0x38, CAPS = 0x40,
};
/* INTERRUPT bits */
#define INT_CMD_DONE (1u << 0)
#define INT_DATA_DONE (1u << 1)
#define INT_WRITE_READY (1u << 4)
#define INT_READ_READY (1u << 5)
#define INT_ERROR (1u << 15)
/* CMDTM: the command half (bits 16-31) and the transfer mode (bits 0-15) */
#define RESP_NONE 0
#define RESP_136 (1u << 16)
#define RESP_48 (2u << 16)
#define RESP_48_BUSY (3u << 16)
#define CRC_CHECK (1u << 19)
#define INDEX_CHECK (1u << 20)
#define HAS_DATA (1u << 21)
#define TM_BLOCK_COUNT (1u << 1)
#define TM_READ (1u << 4)
#define R1 (RESP_48 | CRC_CHECK | INDEX_CHECK)
#define R1B (RESP_48_BUSY | CRC_CHECK | INDEX_CHECK)
#define R2 (RESP_136 | CRC_CHECK)
#define R3 RESP_48
#define R6 R1
#define R7 R1

static uint64_t base;
static int high_capacity;
static uint32_t rca;

static inline uint32_t rd(uint32_t off) { return *(volatile uint32_t *)(base + off); }
static inline void wr(uint32_t off, uint32_t v) { *(volatile uint32_t *)(base + off) = v; }

/* Wait for any of `mask` in INTERRUPT (or an error), with a bound. */
static int wait_int(uint32_t mask) {
    for (uint32_t n = 0; n < 10000000; n++) {
        uint32_t i = rd(INTERRUPT);
        if (i & INT_ERROR) {
            wr(INTERRUPT, i);
            return 0;
        }
        if (i & mask) {
            wr(INTERRUPT, i & mask);
            return 1;
        }
    }
    return 0;
}

static void reset_lines(void) {
    /* reset the command and data lines after an error (CONTROL1 bits 25 and 26) */
    wr(CONTROL1, rd(CONTROL1) | (3u << 25));
    for (uint32_t n = 0; n < 1000000 && (rd(CONTROL1) & (3u << 25)); n++) {}
}

static int cmd(uint32_t index, uint32_t arg, uint32_t flags) {
    for (uint32_t n = 0; n < 1000000 && (rd(STATUS) & 1); n++) {} /* command line busy */
    wr(INTERRUPT, 0xFFFFFFFF);
    wr(ARG1, arg);
    wr(CMDTM, (index << 24) | flags);
    if (!wait_int(INT_CMD_DONE)) {
        reset_lines();
        return 0;
    }
    return 1;
}

static int app_cmd(uint32_t index, uint32_t arg, uint32_t flags) {
    return cmd(55, rca << 16, R1) && cmd(index, arg, flags);
}

static void set_clock(uint32_t divisor) {
    uint32_t c1 = rd(CONTROL1) & ~0xFFFE7u;        /* clear clock enables, divisor and timeout */
    wr(CONTROL1, c1);
    uint32_t d = divisor / 2;                       /* SDHCI v3: 10-bit divided clock */
    c1 |= ((d & 0xFF) << 8) | (((d >> 8) & 3) << 6) | 1u | (0xEu << 16);
    wr(CONTROL1, c1);
    for (uint32_t n = 0; n < 1000000 && !(rd(CONTROL1) & 2); n++) {}
    wr(CONTROL1, rd(CONTROL1) | 4);                 /* the card clock on */
}

/* Bring the card on controller `at` to the transfer state: 1 if it is ready. */
static int init_at(uint64_t at, uint32_t firmware_clock) {
    base = at;
    wr(CONTROL1, rd(CONTROL1) | (1u << 24));        /* reset the whole controller */
    for (uint32_t n = 0; n < 1000000 && (rd(CONTROL1) & (1u << 24)); n++) {}
    wr(CONTROL0, rd(CONTROL0) | (0xFu << 8));       /* bus power on, 3.3 V */
    wr(IRPT_MASK, 0xFFFFFFFF);                      /* report every event in INTERRUPT */
    wr(IRPT_EN, 0);                                 /* but never raise an interrupt: we poll */
    /* The base clock: what the controller says, or else what the firmware says it gave
       it (a Pi 4's EMMC2 may report none). */
    uint32_t base_mhz = (rd(CAPS) >> 8) & 0xFF;
    if (!base_mhz) {
        uint32_t in = firmware_clock, out[2];
        if (mbox_tag(0x00030002, &in, 1, out, 2) && out[1]) base_mhz = out[1] / 1000000;
    }
    set_clock(base_mhz ? base_mhz * 1000 / 400 : 256);   /* 400 kHz to identify the card */

    if (!cmd(0, 0, RESP_NONE)) return 0;
    int v2 = cmd(8, 0x1AA, R7) && (rd(RESP0) & 0xFFF) == 0x1AA;
    uint32_t ocr = 0;
    for (int tries = 0; tries < 1000; tries++) {
        if (!app_cmd(41, 0x00FF8000u | (v2 ? (1u << 30) : 0), R3)) return 0;
        ocr = rd(RESP0);
        if (ocr & (1u << 31)) break;                /* powered up */
    }
    if (!(ocr & (1u << 31))) return 0;
    high_capacity = (ocr >> 30) & 1;
    if (!cmd(2, 0, R2)) return 0;                   /* card identification */
    if (!cmd(3, 0, R6)) return 0;                   /* its address */
    rca = rd(RESP0) >> 16;
    if (!cmd(7, rca << 16, R1B)) return 0;          /* select it */
    if (!high_capacity && !cmd(16, 512, R1)) return 0;
    if (base_mhz) set_clock(base_mhz > 25 ? (base_mhz + 24) / 25 : 1);  /* up to 25 MHz */
    return 1;
}

/* Find the card and bring it to the transfer state. Returns 1 if a card is ready. The Pi
   4's slot is on EMMC2, whose card-detect line reports nothing (Linux marks it broken-cd),
   so EMMC2 is tried whatever it says; the older EMMC (QEMU's card, a Pi's Wi-Fi chip) only
   if it reports a card. A controller with nothing that answers an SD card's commands just
   fails them. */
int sd_init(void) {
    if (init_at(EMMC2, 12)) return 1;               /* firmware clock 12: EMMC2 */
    if ((*(volatile uint32_t *)(EMMC + STATUS) & (1u << 16)) && init_at(EMMC, 1)) return 1;
    base = 0;
    return 0;
}

int sd_present(void) { return base != 0; }

/* Read block `block` into the 512 bytes at `dst`. */
int sd_read(uint64_t block, void *dst) {
    if (!base) return 0;
    wr(BLKSIZECNT, (1u << 16) | 512);
    if (!cmd(17, (uint32_t)(high_capacity ? block : block * 512), R1 | HAS_DATA | TM_READ | TM_BLOCK_COUNT))
        return 0;
    if (!wait_int(INT_READ_READY)) return 0;
    uint32_t *p = dst;
    for (int i = 0; i < 128; i++) p[i] = rd(DATA);
    return wait_int(INT_DATA_DONE);
}

/* Write the 512 bytes at `src` to block `block`. */
int sd_write(uint64_t block, const void *src) {
    if (!base) return 0;
    wr(BLKSIZECNT, (1u << 16) | 512);
    if (!cmd(24, (uint32_t)(high_capacity ? block : block * 512), R1 | HAS_DATA | TM_BLOCK_COUNT))
        return 0;
    if (!wait_int(INT_WRITE_READY)) return 0;
    const uint32_t *p = src;
    for (int i = 0; i < 128; i++) wr(DATA, p[i]);
    return wait_int(INT_DATA_DONE);
}

/* ---- the data partition ----
 * A real card starts with a partition table and the FAT partition the Pi boots from, so
 * the file server's blocks must never be the card's first blocks. At boot the machine layer
 * reads the partition table (block 0) and looks for a partition of type 0xDA ("non-file-
 * system data"); the Lean kernel's block numbers are then numbers inside that partition,
 * and nothing outside it is ever read or written. A card with no such partition has no
 * disk. */
static uint64_t part_start, part_blocks;

/* Find the data partition. Returns its size in blocks, 0 if there is none. */
uint64_t sd_partition(void) {
    static uint8_t mbr[512] __attribute__((aligned(8)));
    part_start = part_blocks = 0;
    if (!base || !sd_read(0, mbr)) return 0;
    if (mbr[510] != 0x55 || mbr[511] != 0xAA) return 0;
    for (int i = 0; i < 4; i++) {
        const uint8_t *e = mbr + 446 + 16 * i;
        uint32_t start = e[8] | e[9] << 8 | e[10] << 16 | (uint32_t)e[11] << 24;
        uint32_t count = e[12] | e[13] << 8 | e[14] << 16 | (uint32_t)e[15] << 24;
        if (e[4] == 0xDA && start != 0 && count != 0) {
            part_start = start;
            part_blocks = count;
            return count;
        }
    }
    return 0;
}

/* Block `block` of the data partition. */
int sd_part_read(uint64_t block, void *dst) {
    return block < part_blocks && sd_read(part_start + block, dst);
}

int sd_part_write(uint64_t block, const void *src) {
    return block < part_blocks && sd_write(part_start + block, src);
}
