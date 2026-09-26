/* The SD card, through the SDHCI controller, a run of 1 to 32 blocks of 512 bytes at a
 * time, by programmed I/O. Never DMA: the controller can be told to write anywhere in
 * physical memory, so it stays here in the machine layer, which only ever asks it to move
 * the bytes the Lean kernel approved (a run of blocks in the caller's block capability,
 * 512 bytes a block in pages the caller has mapped with the right permission) through the
 * data port, word by word. One block is one command (CMD17, CMD24); a longer run is one
 * multi-block command (CMD18, CMD25) with the block count register set, which the
 * controller ends itself with CMD12 after the last block (auto CMD12, in SDHCI since 1.0),
 * so a run costs the card one command and one start-up, not one per block.
 *
 * The Pi 4's SD slot is on EMMC2; QEMU's raspi4b puts the card on the older EMMC
 * controller. EMMC2 is tried first, then EMMC. QEMU accepts almost anything here, so the
 * sequence follows what runs on the chip, with the source for each step:
 *   - registers are read and written 32 bits at a time only (Linux, sdhci-iproc.c: the
 *     BCM2835 EMMC and the BCM2711 EMMC2 both use its 32-bit-only accessors), and while
 *     the card clock is at or below 400 kHz each write is followed by a wait of four card
 *     clocks, since the controller can lose a write that follows another within two
 *     (sdhci_iproc_writel);
 *   - the base clock is the firmware's (mailbox clock 12 for EMMC2, 1 for EMMC, as Linux
 *     and Circle take it), else the capabilities register's, else 100 MHz (Circle's
 *     assumption), and the identification clock is kept at or above 200 kHz, below which
 *     the BCM2711's controller can hang (sdhci_iproc_bcm2711_get_min_clock);
 *   - SDHCI 3.0 divided clock mode: SDCLK = base / 2N, N up to 1023, rounded so the card
 *     never runs faster than asked; an older controller gets its 8-bit power-of-two
 *     divisor;
 *   - on EMMC2, the card's I/O lines at 3.3 V: the firmware's GPIO expander, line 4
 *     (VDD_SD_IO_SEL in the Pi 4's device tree), set low, then 5 ms to settle (Circle does
 *     the same; the device tree's regulator says 5000 us). 1.8 V signaling is never used:
 *     the card runs in default speed, 25 MHz, one data line;
 *   - power, then 10 ms, the clock, then 2 ms (more than the 74 clocks a card needs
 *     before its first command) before CMD0; ACMD41 is repeated every 10 ms for up to a
 *     second while the card powers up (SD Physical Layer spec, 4.2.3);
 *   - EMMC2's card-detect line is not trusted (Linux's device tree marks it broken-cd):
 *     EMMC2 is tried whatever it says; the older EMMC only if it reports a card;
 *   - every wait is bounded in time, from the system counter (arch.h), never in loop turns.
 * Each step's result goes to the serial console, so a card that does not come up says
 * where it stopped. */
#include "arch.h"

#define EMMC2 0xFE340000UL
#define EMMC  0xFE300000UL

enum {
    ARG2 = 0x00, BLKSIZECNT = 0x04, ARG1 = 0x08, CMDTM = 0x0C, RESP0 = 0x10, RESP1 = 0x14,
    RESP2 = 0x18, RESP3 = 0x1C, DATA = 0x20, STATUS = 0x24, CONTROL0 = 0x28, CONTROL1 = 0x2C,
    INTERRUPT = 0x30, IRPT_MASK = 0x34, IRPT_EN = 0x38, CONTROL2 = 0x3C, CAPS = 0x40,
    SLOTISR_VER = 0xFC,
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
#define TM_AUTO_CMD12 (1u << 2)
#define TM_READ (1u << 4)
#define TM_MULTI (1u << 5)
#define R1 (RESP_48 | CRC_CHECK | INDEX_CHECK)
#define R1B (RESP_48_BUSY | CRC_CHECK | INDEX_CHECK)
#define R2 (RESP_136 | CRC_CHECK)
#define R3 RESP_48
#define R6 R1
#define R7 R1

static uint64_t base;
static int high_capacity;
static uint32_t rca;
static uint32_t card_hz;            /* the card clock now, 0 before one is set */
static const char *where;           /* the controller being set up, for the log */

static inline uint32_t rd(uint32_t off) { return *(volatile uint32_t *)(base + off); }
static void wr(uint32_t off, uint32_t v) {
    *(volatile uint32_t *)(base + off) = v;
    if (card_hz <= 400000) delay_us(card_hz ? (4000000 + card_hz - 1) / card_hz : 10);
}

static void say(const char *what) {
    kputs("leanos: SD: ");
    kputs(where);
    kputs(": ");
    kputs(what);
}

/* Wait (at most `us`) until the bits in `mask` of register `off` are all clear. */
static int wait_clear(uint32_t off, uint32_t mask, uint64_t us) {
    for (uint64_t d = deadline_us(us); rd(off) & mask;)
        if (passed(d)) return 0;
    return 1;
}

/* Wait (at most `us`) until any bit in `mask` of register `off` is set. */
static int wait_set(uint32_t off, uint32_t mask, uint64_t us) {
    for (uint64_t d = deadline_us(us); !(rd(off) & mask);)
        if (passed(d)) return 0;
    return 1;
}

/* Wait for any of `mask` in INTERRUPT (or an error), for at most `us`. */
static uint32_t last_int;
static int wait_int(uint32_t mask, uint64_t us) {
    for (uint64_t d = deadline_us(us);;) {
        uint32_t i = rd(INTERRUPT);
        if (i & INT_ERROR) {
            last_int = i;
            wr(INTERRUPT, i);
            return 0;
        }
        if (i & mask) {
            wr(INTERRUPT, i & mask);
            return 1;
        }
        if (passed(d)) {
            last_int = i;
            return 0;
        }
    }
}

static void reset_lines(void) {
    /* reset the command and data lines after an error (CONTROL1 bits 25 and 26) */
    wr(CONTROL1, rd(CONTROL1) | (3u << 25));
    wait_clear(CONTROL1, 3u << 25, 100000);
}

/* What the controller was asked for since boot, for the report at switch-off: commands
   sent (each costs the card a command and response, and a data command its start-up
   time), and blocks moved. */
uint64_t sd_commands, sd_blocks;

static int cmd(uint32_t index, uint32_t arg, uint32_t flags) {
    sd_commands++;
    /* Command inhibit (CMD), and for a command with data or busy, (DAT) too: SDHCI 3.7.1 */
    uint32_t inhibit = (flags & HAS_DATA) || (flags & RESP_48_BUSY) == RESP_48_BUSY ? 3u : 1u;
    if (!wait_clear(STATUS, inhibit, 1000000)) reset_lines();
    wr(INTERRUPT, 0xFFFFFFFF);
    wr(ARG1, arg);
    wr(CMDTM, (index << 24) | flags);
    if (!wait_int(INT_CMD_DONE, 500000)) {
        reset_lines();
        return 0;
    }
    return 1;
}

static int app_cmd(uint32_t index, uint32_t arg, uint32_t flags) {
    return cmd(55, rca << 16, R1) && cmd(index, arg, flags);
}

/* The card clock at most `hz`, from a base clock of `base_hz`; 1 if it is stable. */
static int set_clock(uint32_t base_hz, uint32_t hz, int v3) {
    uint32_t div = (base_hz + hz - 1) / hz, field, actual;
    if (v3) {                                        /* SDCLK = base / 2N, N in 1..1023; 0: base */
        uint32_t n = div <= 1 ? 0 : (div + 1) / 2;
        if (n > 1023) n = 1023;
        field = ((n & 0xFF) << 8) | (((n >> 8) & 3) << 6);
        actual = n ? base_hz / (2 * n) : base_hz;
    } else {                                         /* SDCLK = base / 2N, N a power of two to 128 */
        uint32_t n = 1;
        while (2 * n < div && n < 128) n *= 2;
        if (div <= 1) n = 0;
        field = n << 8;
        actual = n ? base_hz / (2 * n) : base_hz;
    }
    wait_clear(STATUS, 3, 1000000);                  /* no command or data (or busy) under way */
    uint32_t c1 = rd(CONTROL1) & ~0xFFFE7u;          /* clocks off; divisor and timeout cleared */
    wr(CONTROL1, c1);
    card_hz = actual;
    c1 |= field | 1u | (0xEu << 16);                 /* internal clock on; data timeout TMCLK x 2^27 */
    wr(CONTROL1, c1);
    if (!wait_set(CONTROL1, 2, 150000)) return 0;    /* internal clock stable (Linux: 150 ms) */
    wr(CONTROL1, rd(CONTROL1) | 4);                  /* the card clock on */
    delay_us(2000);
    return 1;
}

static void say_khz(const char *what, uint32_t hz) {
    say(what);
    kputdec(hz / 1000);
    kputs(" kHz\n");
}

/* Bring the card on controller `at` to the transfer state: 1 if it is ready. */
static int init_at(uint64_t at, const char *name, uint32_t firmware_clock) {
    base = at;
    where = name;
    card_hz = 0;
    wr(CONTROL1, rd(CONTROL1) | (1u << 24));        /* reset the whole controller */
    if (!wait_clear(CONTROL1, 1u << 24, 100000)) {
        say("the controller did not come out of reset\n");
        return 0;
    }
    uint32_t ver = (rd(SLOTISR_VER) >> 16) & 0xFF;   /* 0: SDHCI 1.0, 1: 2.0, 2: 3.0 */
    int v3 = ver >= 2;
    /* The base clock: the firmware's, else the capabilities register's, else 100 MHz. */
    uint32_t base_hz = 0, in = firmware_clock, out[2] = {0, 0};
    const char *from = "the firmware's";
    if (mbox_tag(0x00030002, &in, 1, out, 2) && out[1] >= 1000000) base_hz = out[1];
    if (!base_hz) {
        base_hz = ((rd(CAPS) >> 8) & (v3 ? 0xFF : 0x3F)) * 1000000;
        from = "the controller's";
    }
    if (!base_hz) {
        base_hz = 100000000;
        from = "assumed";
    }
    say("SDHCI ");
    kputs(ver == 0 ? "1.0" : ver == 1 ? "2.0" : ver == 2 ? "3.0" : "4 or later");
    kputs(", base clock ");
    kputdec(base_hz / 1000);
    kputs(" kHz (");
    kputs(from);
    kputs(")\n");
    if (at == EMMC2) {
        /* 3.3 V I/O: firmware GPIO expander line 4 (128 + 4) low (tag 0x38041). */
        const uint32_t io33[2] = {128 + 4, 0};
        uint32_t o[2];
        int ok = mbox_tag(0x00038041, io33, 2, o, 2);
        say(ok ? "I/O lines at 3.3 V\n" : "could not set the I/O lines to 3.3 V (the firmware did not answer)\n");
        delay_us(5000);
    }
    wr(CONTROL2, 0);                                /* no UHS mode, no 1.8 V, no preset values */
    wr(CONTROL0, (rd(CONTROL0) & ~(0xFu << 8)) | (0x7u << 9));   /* 3.3 V selected */
    wr(CONTROL0, rd(CONTROL0) | (1u << 8));        /* then bus power on */
    delay_us(10000);
    wr(IRPT_MASK, 0xFFFFFFFF);                      /* report every event in INTERRUPT */
    wr(IRPT_EN, 0);                                 /* but never raise an interrupt: we poll */
    uint32_t id_hz = 400000;
    if (base_hz / 2046 > id_hz) id_hz = base_hz / 2046;           /* the slowest the divisor gives */
    if (!set_clock(base_hz, id_hz, v3)) {
        say("the controller's clock did not become stable\n");
        return 0;
    }
    if (card_hz < 200000) {
        say_khz("refusing an identification clock below 200 kHz: ", card_hz);
        return 0;
    }
    say_khz("identification clock ", card_hz);

    if (!cmd(0, 0, RESP_NONE)) {
        say("no answer to CMD0 (go idle)\n");
        return 0;
    }
    int v2 = cmd(8, 0x1AA, R7) && (rd(RESP0) & 0xFFF) == 0x1AA;
    uint32_t ocr = 0;
    uint64_t t0 = timer_now(), d = deadline_us(1000000);
    for (;;) {
        if (!app_cmd(41, 0x00FF8000u | (v2 ? (1u << 30) : 0), R3)) {
            say(v2 ? "a card answered CMD8 (SD 2.0 or later) but not ACMD41\n"
                   : "no card answered CMD8 or ACMD41\n");
            return 0;
        }
        ocr = rd(RESP0);
        if ((ocr & (1u << 31)) || passed(d)) break; /* powered up, or out of time */
        delay_us(10000);
    }
    if (!(ocr & (1u << 31))) {
        say("the card did not finish powering up within a second (ACMD41)\n");
        return 0;
    }
    high_capacity = (ocr >> 30) & 1;
    say(high_capacity ? "an SDHC or SDXC card, powered up after " : "a standard-capacity card, powered up after ");
    kputdec((timer_now() - t0) * 1000 / timer_hz());
    kputs(" ms\n");
    if (!cmd(2, 0, R2)) { say("no answer to CMD2 (identification)\n"); return 0; }
    if (!cmd(3, 0, R6)) { say("no answer to CMD3 (address)\n"); return 0; }
    rca = rd(RESP0) >> 16;
    if (!cmd(7, rca << 16, R1B)) { say("no answer to CMD7 (select)\n"); return 0; }
    if (!high_capacity && !cmd(16, 512, R1)) { say("no answer to CMD16 (block length)\n"); return 0; }
    if (!set_clock(base_hz, 25000000, v3)) {
        say("the controller's clock did not become stable at 25 MHz\n");
        return 0;
    }
    say_khz("ready, transfer clock ", card_hz);
    return 1;
}

/* Find the card and bring it to the transfer state. Returns 1 if a card is ready. A
   controller with nothing that answers an SD card's commands just fails them. */
int sd_init(void) {
    if (init_at(EMMC2, "EMMC2", 12)) return 1;      /* firmware clock 12: EMMC2 */
    base = EMMC;
    if ((rd(STATUS) & (1u << 16)) && init_at(EMMC, "EMMC", 1)) return 1;
    base = 0;
    return 0;
}

int sd_present(void) { return base != 0; }

/* The most blocks one transfer moves: the Lean kernel's `maxRun`. */
#define SD_MAX_RUN 32

/* After a failed transfer of `n` blocks from `block`: say what the controller reported,
   and reset its lines. A multi-block transfer may have left the card sending or taking
   data, so it is told to stop (CMD12); if it had stopped already, it refuses, which does
   no harm. */
static int transfer_failed(const char *what, uint64_t block, uint64_t n) {
    uint32_t status = last_int;
    kputs("leanos: SD: ");
    kputs(what);
    kputs(n > 1 ? " of blocks " : " of block ");
    kputdec(block);
    if (n > 1) {
        kputs(" to ");
        kputdec(block + n - 1);
    }
    kputs(" failed, interrupt status ");
    kputhex(status);
    kputs("\n");
    reset_lines();
    if (n > 1) cmd(12, 0, R1B);
    return 0;
}

/* The command argument for block `block`: its number, or on a standard-capacity card its
   byte address. */
static uint32_t block_arg(uint64_t block) { return (uint32_t)(high_capacity ? block : block * 512); }

/* Read `n` blocks (1 to SD_MAX_RUN) from block `block` into the 512 * n bytes at `dst`. The
   waits: a card may take 100 ms to start sending a block and 250 ms (500 ms for SDXC) to
   finish writing one (SD Physical Layer spec, 4.6.2); these allow a second for each. */
int sd_read(uint64_t block, uint64_t n, void *dst) {
    if (!base || n == 0 || n > SD_MAX_RUN) return 0;
    int multi = n > 1;
    wr(BLKSIZECNT, ((uint32_t)n << 16) | 512);
    if (!cmd(multi ? 18 : 17, block_arg(block),
             R1 | HAS_DATA | TM_READ | TM_BLOCK_COUNT | (multi ? TM_MULTI | TM_AUTO_CMD12 : 0)))
        return transfer_failed(multi ? "read (CMD18)" : "read (CMD17)", block, n);
    uint32_t *p = dst;
    for (uint64_t k = 0; k < n; k++, p += 128) {
        if (!wait_int(INT_READ_READY, 1000000)) return transfer_failed("read", block, n);
        for (int i = 0; i < 128; i++) p[i] = rd(DATA);
        sd_blocks++;
    }
    if (!wait_int(INT_DATA_DONE, 1000000)) return transfer_failed("read (end)", block, n);
    sd_commands += multi;                           /* the controller's CMD12 */
    return 1;
}

/* Write the 512 * n bytes at `src` to `n` blocks (1 to SD_MAX_RUN) from block `block`. The
   transfer is complete once the card is no longer busy (after the CMD12 of a multi-block
   write): it has taken every block, so a later write cannot overtake it. */
int sd_write(uint64_t block, uint64_t n, const void *src) {
    if (!base || n == 0 || n > SD_MAX_RUN) return 0;
    int multi = n > 1;
    wr(BLKSIZECNT, ((uint32_t)n << 16) | 512);
    if (!cmd(multi ? 25 : 24, block_arg(block),
             R1 | HAS_DATA | TM_BLOCK_COUNT | (multi ? TM_MULTI | TM_AUTO_CMD12 : 0)))
        return transfer_failed(multi ? "write (CMD25)" : "write (CMD24)", block, n);
    const uint32_t *p = src;
    for (uint64_t k = 0; k < n; k++, p += 128) {
        if (!wait_int(INT_WRITE_READY, 1000000)) return transfer_failed("write", block, n);
        for (int i = 0; i < 128; i++) wr(DATA, p[i]);
        sd_blocks++;
    }
    if (!wait_int(INT_DATA_DONE, 1000000)) return transfer_failed("write (end)", block, n);
    sd_commands += multi;                           /* the controller's CMD12 */
    return 1;
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
    if (!base || !sd_read(0, 1, mbr)) return 0;
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

/* `n` blocks of the data partition from block `block`: all inside it, or none is moved. */
int sd_part_read(uint64_t block, uint64_t n, void *dst) {
    return block < part_blocks && n <= part_blocks - block && sd_read(part_start + block, n, dst);
}

int sd_part_write(uint64_t block, uint64_t n, const void *src) {
    return block < part_blocks && n <= part_blocks - block && sd_write(part_start + block, n, src);
}
