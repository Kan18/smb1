#include "nes.h"
#include <stdio.h>
#include <string.h>

uint8_t PRG[0x8000], CHR[0x2000];
bool nes_vertical = true;
uint8_t *nes_acc = NULL;  // optional per-byte first-access log: 1 = written first, 2 = read first
uint8_t *nes_wr = NULL;   // optional per-byte write log: set to 1 by every RAM write

static void unsupported(NES *n) {
  if (!n->err) { n->err = 2; n->err_pc = n->pc; }
}

int nes_load_rom(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return -1;
  uint8_t h[16];
  if (fread(h, 1, 16, f) != 16 || memcmp(h, "NES\x1a", 4)) { fclose(f); return -2; }
  int prg = h[4] * 0x4000, chr = h[5] * 0x2000;
  int mapper = (h[6] >> 4) | (h[7] & 0xF0);
  if (mapper != 0 || (h[6] & 0x0c) != 0 || (h[7] & 3) != 0 ||
      ((h[7] & 0x0c) != 0 && ((h[7] & 0x0c) != 8 || h[8] || h[9])) ||
      prg < 0x4000 || prg > 0x8000 || chr != 0x2000) { fclose(f); return -3; }
  if (fread(PRG, 1, prg, f) != (size_t)prg) { fclose(f); return -4; }
  if (prg == 0x4000) memcpy(PRG + 0x4000, PRG, 0x4000);
  if (fread(CHR, 1, chr, f) != (size_t)chr) { fclose(f); return -4; }
  fclose(f);
  nes_vertical = h[6] & 1;
  return 0;
}

// ---------------------------------------------------------------- PPU

// Frame snapshots start at scanline 240. NMI comes from the sampled PPU line,
// not an independently scheduled interrupt. The selected clock phase splits each
// CPU bus cycle into one PPU dot before the access and two after it.
enum { PH_VBL, PH_CLR, PH_PRE, PH_SKIP, PH_LSTART, PH_HIT, PH_LEND, PH_END, PH_COUNT };

static inline int32_t line0(NES *n) { return 22 * 341 - n->skipped; }

static int32_t ph_pos(NES *n, int ph) {
  switch (ph) {
    case PH_VBL: return 342;
    case PH_CLR: return 21 * 341 + 1;
    case PH_PRE: return 21 * 341 + 304;
    case PH_SKIP: return 21 * 341 + 339;
    case PH_LSTART: return line0(n) + n->line * 341;
    case PH_HIT: return -1; // status events are merged independently by sched
    case PH_LEND: return line0(n) + n->line * 341 + 256;
    case PH_END: return n->flen;
  }
  return -1;
}

static void sched(NES *n) {
  n->next_ev = 0x7fffffff;
  while (n->ev_idx < PH_COUNT) {
    int32_t p = ph_pos(n, n->ev_idx);
    if (p >= 0) { n->next_ev = p; break; }
    n->ev_idx++;
  }
  if (n->hit_pos >= 0 && n->hit_pos < n->next_ev) n->next_ev = n->hit_pos;
  if (n->overflow_pos >= 0 && n->overflow_pos < n->next_ev) n->next_ev = n->overflow_pos;
}

static uint16_t inc_y(uint16_t v) {
  if ((v & 0x7000) != 0x7000) return v + 0x1000;
  v &= ~0x7000;
  int y = (v & 0x03E0) >> 5;
  if (y == 29) { y = 0; v ^= 0x0800; }
  else if (y == 31) y = 0;
  else y++;
  return (v & ~0x03E0) | (y << 5);
}

static inline unsigned nt_index(uint16_t a) {
  return nes_vertical ? (a & 0x7ff) : ((a & 0x3ff) | ((a >> 1) & 0x400));
}
static inline uint8_t nt_read(NES *n, uint16_t a) { return n->ntram[nt_index(a)]; }

static int bg_opaque(NES *n, uint16_t v, int px) {
  int fine = n->fx + px;
  int cx = (v & 31) + (fine >> 3);
  uint16_t nt = v & 0x0C00;
  if (cx >= 32) { cx -= 32; nt ^= 0x0400; }
  int cy = (v >> 5) & 31, fy = (v >> 12) & 7;
  uint8_t tile = nt_read(n, 0x2000 | nt | (cy << 5) | cx);
  uint16_t pa = ((n->ctrl & 0x10) ? 0x1000 : 0) + tile * 16 + fy;
  int bit = 7 - (fine & 7);
  return ((CHR[pa] >> bit) | (CHR[pa + 8] >> bit)) & 1;
}

// Sprite-0 pixels for the line after `line`, as fetched at the end of `line`.
static void fetch_sprite0(NES *n) {
  int h = (n->ctrl & 0x20) ? 16 : 8;
  int t = n->line - n->oam[0];
  n->sp0x = 0x100;
  if (t < 0 || t >= h) return;
  uint8_t tile = n->oam[1], attr = n->oam[2];
  int row = (attr & 0x80) ? (h - 1 - t) : t;
  uint16_t pa;
  if (h == 8) pa = ((n->ctrl & 0x08) ? 0x1000 : 0) + tile * 16 + row;
  else pa = ((tile & 1) ? 0x1000 : 0) + (tile & 0xFE) * 16 + (row >= 8 ? 16 : 0) + (row & 7);
  uint8_t d = CHR[pa & 0x1FFF] | CHR[(pa + 8) & 0x1FFF];
  if (attr & 0x40) {  // horizontal flip: reverse bits
    uint8_t r = 0;
    for (int i = 0; i < 8; i++) if (d & (1 << i)) r |= 0x80 >> i;
    d = r;
  }
  n->sp0x = n->oam[3];
  n->sp0data = d;
}

// For the selected CPU/PPU phase, the delayed status output becomes visible
// at X + 4, after the pixel collision and the PPU status pipeline.
static int32_t line_hit(NES *n, int first_x) {
  if (n->sp0x == 0x100 || (n->mask & 0x18) != 0x18 || n->spr0) return -1;
  for (int i = 0; i < 8; i++) {
    int x = n->sp0x + i;
    if (x >= 255) break;
    if (x < first_x) continue;
    if (x < 8 && (n->mask & 6) != 6) continue;
    if ((n->sp0data & (0x80 >> i)) && bg_opaque(n, n->v, x)) return line0(n) + n->line * 341 + x + 4;
  }
  return -1;
}

// Evaluate stable OAM at two dots per byte, including the diagonal scan once
// eight sprites have filled secondary OAM. Rendering-time OAM changes are guarded.
static int32_t sprite_overflow(NES *n) {
  if (n->ovf || !(n->mask & 0x18)) return -1;
  int count = 0, m = 0, dot = 66, h = (n->ctrl & 0x20) ? 16 : 8;
  for (int i = 0; i < 64 && dot <= 256; i++) {
    int row = n->line - n->oam[4 * i + m];
    int in_range = row >= 0 && row < h;
    if (count == 8) {
      if (in_range) return line0(n) + n->line * 341 + dot + 1;
      m = (m + 1) & 3;
    } else if (in_range) { count++; dot += 6; }
    dot += 2;
  }
  return -1;
}

__attribute__((noinline)) static void ppu_events(NES *n) {
  while (n->fpos >= n->next_ev) {
    // CPU-visible sprite flags include the PPU's internal output delay. Keeping
    // these independent permits the rightmost hit to arrive after dot 256.
    if (n->hit_pos == n->next_ev) {
      n->spr0 = 1; n->hit_pos = -1; sched(n); continue;
    }
    if (n->overflow_pos == n->next_ev) {
      n->ovf = 1; n->overflow_pos = -1; sched(n); continue;
    }
    switch (n->ev_idx) {
      case PH_VBL: n->vbl = !n->suppress_vbl; n->suppress_vbl = 0; break;
      case PH_CLR: n->vbl = n->spr0 = n->ovf = 0; n->dead = 0; break;
      case PH_PRE:
        if ((n->mask & 0x18) && n->oamaddr >= 8) unsupported(n);
        if (n->mask & 0x18) { n->v = n->t; n->oamaddr = 0; }
        n->sp0x = 0x100;
        n->line = 0;
        break;
      case PH_SKIP:
        n->skipped = n->odd && (n->mask & 0x18);
        n->flen = 262 * 341 - n->skipped;
        break;
      case PH_LSTART:
        n->hit_pos = line_hit(n, 0);
        n->overflow_pos = sprite_overflow(n);
        break;
      case PH_LEND:
        if (n->mask & 0x18) {
          n->v = inc_y(n->v);
          fetch_sprite0(n);
          n->oamaddr = 0;
          n->v = (n->v & 0xFBE0) | (n->t & 0x041F);
        } else n->sp0x = 0x100;
        if (++n->line < 240) { n->ev_idx = PH_LSTART; sched(n); continue; }
        break;
      case PH_END:
        n->frame_done = 1;
        n->fpos -= n->flen;
        n->odd ^= 1;
        n->skipped = 0;
        n->flen = 262 * 341;
        n->hit_pos = n->overflow_pos = -1;
        n->ev_idx = -1;
        break;
    }
    n->ev_idx++;
    sched(n);
  }
}

// Forced inline: three calls per CPU cycle, almost always only the comparison (the search's hot path).
__attribute__((always_inline)) static inline void advance_ppu(NES *n, int dots) {
  n->fpos += dots;
  if (__builtin_expect(n->fpos >= n->next_ev, 0)) ppu_events(n);
}

__attribute__((always_inline)) static inline void begin_cycle(NES *n) {
  n->cyc++;
  if (!(n->cyc & 1) && n->strobe) { n->sh[0] = n->pad[0]; n->sh[1] = n->pad[1]; }
  advance_ppu(n, 1);
}

__attribute__((always_inline)) static inline void end_cycle(NES *n) {
  advance_ppu(n, 1);
  n->nmi_polled = n->nmi_pending;
  uint8_t line = n->vbl && (n->ctrl & 0x80);
  if (line && !n->nmi_line) n->nmi_pending = 1;
  n->nmi_line = line;
  advance_ppu(n, 1);
}

__attribute__((always_inline)) static inline void tick(NES *n) { begin_cycle(n); end_cycle(n); }

static uint8_t ppu_mem_read(NES *n, uint16_t a) {
  a &= 0x3FFF;
  if (a < 0x2000) return CHR[a];
  if (a < 0x3F00) return nt_read(n, a);
  a &= 0x1F;
  if ((a & 0x13) == 0x10) a &= 0x0F;
  return n->pal[a];
}

static void ppu_mem_write(NES *n, uint16_t a, uint8_t val) {
  a &= 0x3FFF;
  if (a < 0x2000) return;  // CHR ROM
  if (a < 0x3F00) { n->ntram[nt_index(a)] = val; return; }
  a &= 0x1F;
  if ((a & 0x13) == 0x10) a &= 0x0F;
  n->pal[a] = val & 0x3f;
}

static int rendering(NES *n) {
  return !n->dead && (n->mask & 0x18) && n->fpos >= 21 * 341;
}

// Deterministic analogue approximation: each driven group decays after about
// twenty NTSC frames. Undriven bits are not refreshed by an open-bus read.
static void io_decay(NES *n) {
  if (n->cyc - n->io_low >= 600000) n->iolatch &= 0xe0;
  if (n->cyc - n->io_bit5 >= 600000) n->iolatch &= 0xdf;
  if (n->cyc - n->io_high >= 600000) n->iolatch &= 0x3f;
}

static uint8_t ppu_reg_read(NES *n, uint16_t a) {
  io_decay(n);
  uint8_t r = n->iolatch;
  switch (a & 7) {
    case 2:
      r = (n->vbl << 7) | (n->spr0 << 6) | (n->ovf << 5) | (n->iolatch & 0x1F);
      if (n->fpos == 341) n->suppress_vbl = 1;
      n->vbl = 0;
      n->w = 0;
      n->io_bit5 = n->io_high = n->cyc;
      break;
    case 4:
      if (rendering(n)) unsupported(n);
      r = n->oam[n->oamaddr];
      n->io_low = n->io_bit5 = n->io_high = n->cyc;
      break;
    case 7: {
      if (rendering(n)) unsupported(n);
      uint16_t addr = n->v & 0x3FFF;
      if (addr < 0x3F00) { r = n->rbuf; n->rbuf = ppu_mem_read(n, addr); }
      else {
        r = (ppu_mem_read(n, addr) & ((n->mask & 1) ? 0x30 : 0x3f)) | (n->iolatch & 0xc0);
        n->rbuf = nt_read(n, addr);
      }
      n->io_low = n->io_bit5 = n->cyc;
      if (addr < 0x3f00) n->io_high = n->cyc;
      n->v = (n->v + ((n->ctrl & 4) ? 32 : 1)) & 0x7FFF;
      break;
    }
  }
  n->iolatch = r;
  return r;
}

static void ppu_reg_write(NES *n, uint16_t a, uint8_t val) {
  int reg = a & 7;
  n->io_low = n->io_bit5 = n->io_high = n->cyc;
  n->iolatch = val;
  if (n->dead && (reg == 0 || reg == 1 || reg == 5 || reg == 6)) return;
  int old_render = !!(n->mask & 0x18), new_render = !!(val & 0x18);
  int dot = n->fpos - line0(n) - n->line * 341;
  // An early visible-line enable has a complete sprite evaluation/fetch ahead
  // of it. No sprite-zero pixels may remain from the preceding disabled line.
  int early_enable = !old_render && new_render && n->line < 240 &&
    dot >= 0 && dot <= 60 && n->sp0x == 0x100 && n->oamaddr == 0;
  // A later enable, in a long NMI: evaluation on this line is only partial, which can't
  // matter if sprite 0 isn't in range and no overflow is possible. The rest of the line
  // has to stay clear of the Y increment and X copy at dots 256 and 257.
  int late_enable = 0;
  if (!old_render && new_render && n->sp0x == 0x100 && n->oamaddr == 0 && n->fpos >= line0(n)) {
    uint8_t m = n->mask;
    n->mask = val;
    int t = n->line - n->oam[0], h = (n->ctrl & 0x20) ? 16 : 8;
    late_enable = n->line >= 240 || (!(t >= 0 && t < h) && !(dot >= 251 && dot <= 257) && sprite_overflow(n) < 0);
    n->mask = m;
  }
  if (!n->dead && n->fpos >= 21 * 341 + 257 && reg == 1 &&
      old_render != new_render && !early_enable && !late_enable) unsupported(n);
  if (rendering(n) && (reg == 3 || reg == 4 || reg == 7 ||
      (reg == 0 && ((n->ctrl ^ val) & 0x38)))) unsupported(n);
  // Mid-line scroll/address changes before a pending sprite hit require a finer PPU.
  if (rendering(n) && !n->spr0 && n->fpos >= line0(n) &&
      ((reg == 5 && !n->w && (val & 7) != n->fx) ||
       (reg == 6 && n->w && ((n->t & 0xff00) | val) != n->v))) unsupported(n);
  n->iolatch = val;
  switch (a & 7) {
    case 0:
      n->ctrl = val;
      n->t = (n->t & 0xF3FF) | ((val & 3) << 10);
      break;
    case 1:
      n->mask = val;
      if (early_enable) n->overflow_pos = sprite_overflow(n);
      if (n->ev_idx == PH_HIT || n->ev_idx == PH_LEND) {
        // A collision already in the output pipeline cannot be cancelled.
        if (n->hit_pos < 0 || n->hit_pos > n->fpos + 3)
          n->hit_pos = line_hit(n, dot < 0 ? 0 : dot);
        n->ev_idx = PH_HIT;
        sched(n);
      }
      break;
    case 3: n->oamaddr = val; break;
    case 4: n->oam[n->oamaddr] = (n->oamaddr & 3) == 2 ? val & 0xe3 : val; n->oamaddr++; break;
    case 5:
      if (!n->w) { n->t = (n->t & 0xFFE0) | (val >> 3); n->fx = val & 7; n->w = 1; }
      else { n->t = (n->t & 0x8C1F) | ((val & 7) << 12) | ((val & 0xF8) << 2); n->w = 0; }
      break;
    case 6:
      if (!n->w) { n->t = (n->t & 0x00FF) | ((val & 0x3F) << 8); n->w = 1; }
      else { n->t = (n->t & 0xFF00) | val; n->v = n->t; n->w = 0; }
      break;
    case 7:
      ppu_mem_write(n, n->v, val);
      n->v = (n->v + ((n->ctrl & 4) ? 32 : 1)) & 0x7FFF;
      break;
  }
}

// ---------------------------------------------------------------- bus

static uint8_t read_cycle(NES *n, uint16_t a) {
  begin_cycle(n);
  uint8_t r;
  if (a >= 0x8000) r = PRG[a & 0x7FFF];  // most reads: opcodes and operands
  else if (a < 0x2000) {
    uint16_t m = a & 0x7FF;
    if (nes_acc && !nes_acc[m]) nes_acc[m] = 2;
    r = n->ram[m];
  } else if (a < 0x4000) r = ppu_reg_read(n, a);
  else if (a == 0x4016 || a == 0x4017) {
    int i = a & 1;
    uint8_t bit;
    if (n->strobe) bit = n->pad[i] & 1;
    else if (n->pad_read == i + 1) bit = n->pad_bit;
    else { bit = n->sh[i] & 1; n->sh[i] = (n->sh[i] >> 1) | 0x80; }
    n->pad_bit = bit;
    r = (n->bus & 0xE0) | bit;
  } else {
    if (a == 0x4015) unsupported(n);  // APU status is not implemented.
    r = n->bus;
  }
  n->pad_read = (a == 0x4016 || a == 0x4017) ? (a & 1) + 1 : 0;
  n->bus = r;
  end_cycle(n);
  if (a >= 0x2000 && a < 0x4000 && (a & 7) == 2) {
    // Vblank was latched at the start of the read; sprite flags are observed at
    // the end of the read cycle.
    r = (r & 0x9f) | (n->spr0 << 6) | (n->ovf << 5);
    n->bus = n->iolatch = r;
  }
  return r;
}

// DMA can halt only a read cycle. Consecutive writes (including RMW) merely
// replace the pending page. Halt/alignment reads retain their bus side effects.
static uint8_t rd(NES *n, uint16_t a) {
  if (n->dma_pending) {
    n->dma_pending = 0;
    if (rendering(n)) unsupported(n);
    read_cycle(n, a);
    if (n->cyc & 1) read_cycle(n, a);
    for (unsigned i = 0; i < 256; i++) {
      uint8_t b = read_cycle(n, (n->dma_page << 8) | i);
      begin_cycle(n);
      ppu_reg_write(n, 0x2004, b);
      n->pad_read = 0;
      n->bus = b;
      end_cycle(n);
    }
  }
  return read_cycle(n, a);
}

static void wr(NES *n, uint16_t a, uint8_t val) {
  begin_cycle(n);
  n->pad_read = 0;
  n->bus = val;
  if (a < 0x2000) {
    if (nes_acc && !nes_acc[a & 0x7FF]) nes_acc[a & 0x7FF] = 1;
    if (nes_wr) nes_wr[a & 0x7FF] = 1;
    n->ram[a & 0x7FF] = val;
  }
  else if (a < 0x4000) ppu_reg_write(n, a, val);
  else if (a == 0x4014) {
    n->dma_pending = 1;
    n->dma_page = val;
  } else if (a == 0x4016) {
    if (n->strobe && !(val & 1)) n->polls++;
    n->strobe = val & 1;
  } else if (a == 0x4015 && (val & 0x10)) {
    unsupported(n);  // DMC DMA and its bus side effects are not implemented.
  }
  end_cycle(n);
  // Other APU writes do not affect this model while DMC and CPU IRQs are disabled.
}

// ---------------------------------------------------------------- CPU

enum { FC = 1, FZ = 2, FI = 4, FD = 8, FB = 16, FU = 32, FV = 64, FN = 128 };

#define SETNZ(v) (n->p = (n->p & ~(FN | FZ)) | ((v) & FN) | ((v) ? 0 : FZ))

static inline uint8_t fetch(NES *n) { return rd(n, n->pc++); }
static inline uint16_t fetch16(NES *n) { uint8_t lo = fetch(n); return lo | (fetch(n) << 8); }
static inline void push(NES *n, uint8_t v) { wr(n, 0x100 | n->s--, v); }
static inline uint8_t pull(NES *n) { uint8_t v = rd(n, 0x100 | (uint8_t)(n->s + 1)); n->s++; return v; }

// Address computation; `w` = instruction writes (forces the extra indexed cycle).
static uint16_t a_zp(NES *n) { return fetch(n); }
static uint16_t a_zpx(NES *n) { uint8_t b = fetch(n); rd(n, b); return (uint8_t)(b + n->x); }
static uint16_t a_zpy(NES *n) { uint8_t b = fetch(n); rd(n, b); return (uint8_t)(b + n->y); }
static uint16_t a_abs(NES *n) { return fetch16(n); }
static uint16_t a_absi(NES *n, uint8_t i, int w) {
  uint16_t b = fetch16(n), a = b + i;
  if (w || ((a ^ b) & 0xFF00)) rd(n, (b & 0xFF00) | (a & 0xFF));
  return a;
}
static uint16_t a_indx(NES *n) {
  uint8_t z = fetch(n);
  rd(n, z);
  z += n->x;
  uint8_t lo = rd(n, z);
  return lo | (rd(n, (uint8_t)(z + 1)) << 8);
}
static uint16_t a_indy(NES *n, int w) {
  uint8_t z = fetch(n);
  uint8_t lo = rd(n, z);
  uint16_t b = lo | (rd(n, (uint8_t)(z + 1)) << 8), a = b + n->y;
  if (w || ((a ^ b) & 0xFF00)) rd(n, (b & 0xFF00) | (a & 0xFF));
  return a;
}

static void adc(NES *n, uint8_t m) {
  unsigned s = n->a + m + (n->p & FC);
  n->p &= ~(FC | FV);
  if (s > 0xFF) n->p |= FC;
  if (~(n->a ^ m) & (n->a ^ s) & 0x80) n->p |= FV;
  n->a = s;
  SETNZ(n->a);
}
static void cmp(NES *n, uint8_t r, uint8_t m) {
  n->p = (r >= m) ? (n->p | FC) : (n->p & ~FC);
  SETNZ((uint8_t)(r - m));
}
static void branch(NES *n, int cond) {
  int8_t off = fetch(n);
  uint8_t polled = n->nmi_polled;
  if (!cond) return;
  rd(n, n->pc);
  uint16_t a = n->pc + off;
  if ((a ^ n->pc) & 0xFF00) {
    rd(n, (n->pc & 0xFF00) | (a & 0xFF));
    n->nmi_polled |= polled;
  } else n->nmi_polled = polled; // no poll on a taken branch's final dummy read
  n->pc = a;
}

static uint8_t rmw(NES *n, uint16_t a, int op) {
  uint8_t v = rd(n, a);
  wr(n, a, v);  // dummy write of the unmodified value
  uint8_t c;
  switch (op) {
    case 0: c = v >> 7; v <<= 1; n->p = (n->p & ~FC) | c; break;                    // ASL
    case 1: c = v & 1; v >>= 1; n->p = (n->p & ~FC) | c; break;                     // LSR
    case 2: c = v >> 7; v = (v << 1) | (n->p & FC); n->p = (n->p & ~FC) | c; break;  // ROL
    case 3: c = v & 1; v = (v >> 1) | ((n->p & FC) << 7); n->p = (n->p & ~FC) | c; break;  // ROR
    case 4: v++; break;                                                             // INC
    default: v--; break;                                                            // DEC
  }
  SETNZ(v);
  wr(n, a, v);
  return v;
}

static uint8_t acc_op(NES *n, uint8_t v, int op) {
  uint8_t c;
  switch (op) {
    case 0: c = v >> 7; v <<= 1; break;
    case 1: c = v & 1; v >>= 1; break;
    case 2: c = v >> 7; v = (v << 1) | (n->p & FC); break;
    default: c = v & 1; v = (v >> 1) | ((n->p & FC) << 7); break;
  }
  n->p = (n->p & ~FC) | c;
  SETNZ(v);
  return v;
}

static void interrupt(NES *n, uint16_t vec, int brk) {
  push(n, n->pc >> 8);
  push(n, n->pc & 0xFF);
  if (n->nmi_pending) { vec = 0xfffa; n->nmi_pending = 0; }
  push(n, (n->p & ~FB) | FU | (brk ? FB : 0));
  n->p |= FI;
  uint8_t lo = rd(n, vec);
  n->pc = lo | (rd(n, vec + 1) << 8);
}

static void nmi(NES *n) {
  rd(n, n->pc);
  rd(n, n->pc);
  interrupt(n, 0xFFFA, 0);
}

void nes_step(NES *n) {
  uint16_t opc_pc = n->pc;
  uint8_t op = fetch(n);
  switch (op) {
    // ---- loads
    case 0xA9: n->a = fetch(n); SETNZ(n->a); break;
    case 0xA5: n->a = rd(n, a_zp(n)); SETNZ(n->a); break;
    case 0xB5: n->a = rd(n, a_zpx(n)); SETNZ(n->a); break;
    case 0xAD: n->a = rd(n, a_abs(n)); SETNZ(n->a); break;
    case 0xBD: n->a = rd(n, a_absi(n, n->x, 0)); SETNZ(n->a); break;
    case 0xB9: n->a = rd(n, a_absi(n, n->y, 0)); SETNZ(n->a); break;
    case 0xA1: n->a = rd(n, a_indx(n)); SETNZ(n->a); break;
    case 0xB1: n->a = rd(n, a_indy(n, 0)); SETNZ(n->a); break;
    case 0xA2: n->x = fetch(n); SETNZ(n->x); break;
    case 0xA6: n->x = rd(n, a_zp(n)); SETNZ(n->x); break;
    case 0xB6: n->x = rd(n, a_zpy(n)); SETNZ(n->x); break;
    case 0xAE: n->x = rd(n, a_abs(n)); SETNZ(n->x); break;
    case 0xBE: n->x = rd(n, a_absi(n, n->y, 0)); SETNZ(n->x); break;
    case 0xA0: n->y = fetch(n); SETNZ(n->y); break;
    case 0xA4: n->y = rd(n, a_zp(n)); SETNZ(n->y); break;
    case 0xB4: n->y = rd(n, a_zpx(n)); SETNZ(n->y); break;
    case 0xAC: n->y = rd(n, a_abs(n)); SETNZ(n->y); break;
    case 0xBC: n->y = rd(n, a_absi(n, n->x, 0)); SETNZ(n->y); break;
    // ---- stores
    case 0x85: wr(n, a_zp(n), n->a); break;
    case 0x95: wr(n, a_zpx(n), n->a); break;
    case 0x8D: wr(n, a_abs(n), n->a); break;
    case 0x9D: wr(n, a_absi(n, n->x, 1), n->a); break;
    case 0x99: wr(n, a_absi(n, n->y, 1), n->a); break;
    case 0x81: wr(n, a_indx(n), n->a); break;
    case 0x91: wr(n, a_indy(n, 1), n->a); break;
    case 0x86: wr(n, a_zp(n), n->x); break;
    case 0x96: wr(n, a_zpy(n), n->x); break;
    case 0x8E: wr(n, a_abs(n), n->x); break;
    case 0x84: wr(n, a_zp(n), n->y); break;
    case 0x94: wr(n, a_zpx(n), n->y); break;
    case 0x8C: wr(n, a_abs(n), n->y); break;
    // ---- ALU (ORA AND EOR ADC CMP SBC)
#define ALU(base, body)                                   \
    case base + 0x09: { uint8_t m = fetch(n); body; } break;               \
    case base + 0x05: { uint8_t m = rd(n, a_zp(n)); body; } break;         \
    case base + 0x15: { uint8_t m = rd(n, a_zpx(n)); body; } break;        \
    case base + 0x0D: { uint8_t m = rd(n, a_abs(n)); body; } break;        \
    case base + 0x1D: { uint8_t m = rd(n, a_absi(n, n->x, 0)); body; } break; \
    case base + 0x19: { uint8_t m = rd(n, a_absi(n, n->y, 0)); body; } break; \
    case base + 0x01: { uint8_t m = rd(n, a_indx(n)); body; } break;       \
    case base + 0x11: { uint8_t m = rd(n, a_indy(n, 0)); body; } break;
    ALU(0x00, n->a |= m; SETNZ(n->a))
    ALU(0x20, n->a &= m; SETNZ(n->a))
    ALU(0x40, n->a ^= m; SETNZ(n->a))
    ALU(0x60, adc(n, m))
    ALU(0xC0, cmp(n, n->a, m))
    ALU(0xE0, adc(n, ~m))
#undef ALU
    case 0xE0: cmp(n, n->x, fetch(n)); break;
    case 0xE4: cmp(n, n->x, rd(n, a_zp(n))); break;
    case 0xEC: cmp(n, n->x, rd(n, a_abs(n))); break;
    case 0xC0: cmp(n, n->y, fetch(n)); break;
    case 0xC4: cmp(n, n->y, rd(n, a_zp(n))); break;
    case 0xCC: cmp(n, n->y, rd(n, a_abs(n))); break;
    case 0x24: case 0x2C: {
      uint8_t m = rd(n, op == 0x24 ? a_zp(n) : a_abs(n));
      n->p = (n->p & ~(FN | FV | FZ)) | (m & (FN | FV)) | ((n->a & m) ? 0 : FZ);
      break;
    }
    // ---- shifts / inc / dec
#define RMW(base, opn)                                       \
    case base + 0x06: rmw(n, a_zp(n), opn); break;           \
    case base + 0x16: rmw(n, a_zpx(n), opn); break;          \
    case base + 0x0E: rmw(n, a_abs(n), opn); break;          \
    case base + 0x1E: rmw(n, a_absi(n, n->x, 1), opn); break;
    RMW(0x00, 0) RMW(0x40, 1) RMW(0x20, 2) RMW(0x60, 3) RMW(0xE0, 4) RMW(0xC0, 5)
#undef RMW
    case 0x0A: rd(n, n->pc); n->a = acc_op(n, n->a, 0); break;
    case 0x4A: rd(n, n->pc); n->a = acc_op(n, n->a, 1); break;
    case 0x2A: rd(n, n->pc); n->a = acc_op(n, n->a, 2); break;
    case 0x6A: rd(n, n->pc); n->a = acc_op(n, n->a, 3); break;
    case 0xE8: rd(n, n->pc); n->x++; SETNZ(n->x); break;
    case 0xCA: rd(n, n->pc); n->x--; SETNZ(n->x); break;
    case 0xC8: rd(n, n->pc); n->y++; SETNZ(n->y); break;
    case 0x88: rd(n, n->pc); n->y--; SETNZ(n->y); break;
    // ---- transfers / flags
    case 0xAA: rd(n, n->pc); n->x = n->a; SETNZ(n->x); break;
    case 0x8A: rd(n, n->pc); n->a = n->x; SETNZ(n->a); break;
    case 0xA8: rd(n, n->pc); n->y = n->a; SETNZ(n->y); break;
    case 0x98: rd(n, n->pc); n->a = n->y; SETNZ(n->a); break;
    case 0xBA: rd(n, n->pc); n->x = n->s; SETNZ(n->x); break;
    case 0x9A: rd(n, n->pc); n->s = n->x; break;
    case 0x18: rd(n, n->pc); n->p &= ~FC; break;
    case 0x38: rd(n, n->pc); n->p |= FC; break;
    case 0x58: rd(n, n->pc); n->p &= ~FI; break;
    case 0x78: rd(n, n->pc); n->p |= FI; break;
    case 0xB8: rd(n, n->pc); n->p &= ~FV; break;
    case 0xD8: rd(n, n->pc); n->p &= ~FD; break;
    case 0xF8: rd(n, n->pc); n->p |= FD; break;
    case 0xEA: case 0x1A: case 0x3A: case 0x5A: case 0x7A: case 0xDA: case 0xFA:
      rd(n, n->pc); break;
    case 0x80: case 0x82: case 0x89: case 0xC2: case 0xE2: fetch(n); break;
    case 0x04: case 0x44: case 0x64: rd(n, a_zp(n)); break;
    case 0x14: case 0x34: case 0x54: case 0x74: case 0xD4: case 0xF4: rd(n, a_zpx(n)); break;
    case 0x0C: rd(n, a_abs(n)); break;
    case 0x1C: case 0x3C: case 0x5C: case 0x7C: case 0xDC: case 0xFC: rd(n, a_absi(n, n->x, 0)); break;
    // ---- stack
    case 0x48: rd(n, n->pc); push(n, n->a); break;
    case 0x08: rd(n, n->pc); push(n, n->p | FB | FU); break;
    case 0x68: rd(n, n->pc); rd(n, 0x100 | n->s); n->a = pull(n); SETNZ(n->a); break;
    case 0x28: rd(n, n->pc); rd(n, 0x100 | n->s); n->p = (pull(n) & ~FB) | FU; break;
    // ---- control flow
    case 0x4C: n->pc = fetch16(n); break;
    case 0x6C: {
      uint16_t ptr = fetch16(n);
      uint8_t lo = rd(n, ptr);
      n->pc = lo | (rd(n, (ptr & 0xFF00) | ((ptr + 1) & 0xFF)) << 8);
      break;
    }
    case 0x20: {
      uint8_t lo = fetch(n);
      rd(n, 0x100 | n->s);
      push(n, n->pc >> 8);
      push(n, n->pc & 0xFF);
      n->pc = lo | (fetch(n) << 8);
      break;
    }
    case 0x60: {
      rd(n, n->pc); rd(n, 0x100 | n->s);
      uint8_t lo = pull(n);
      n->pc = lo | (pull(n) << 8);
      rd(n, n->pc);
      n->pc++;
      break;
    }
    case 0x40: {
      rd(n, n->pc); rd(n, 0x100 | n->s);
      n->p = (pull(n) & ~FB) | FU;
      uint8_t lo = pull(n);
      n->pc = lo | (pull(n) << 8);
      break;
    }
    case 0x00: fetch(n); interrupt(n, 0xFFFE, 1); n->nmi_polled = 0; break;
    case 0x10: branch(n, !(n->p & FN)); break;
    case 0x30: branch(n, n->p & FN); break;
    case 0x50: branch(n, !(n->p & FV)); break;
    case 0x70: branch(n, n->p & FV); break;
    case 0x90: branch(n, !(n->p & FC)); break;
    case 0xB0: branch(n, n->p & FC); break;
    case 0xD0: branch(n, !(n->p & FZ)); break;
    case 0xF0: branch(n, n->p & FZ); break;
    default:
      if (!n->err) { n->err = 1; n->err_pc = opc_pc; }
      tick(n);
      break;
  }
  if (!(n->p & FI)) unsupported(n);  // Maskable IRQ delivery is not implemented.
  if (n->nmi_polled) nmi(n);
}

// ---------------------------------------------------------------- power / frames

void nes_power(NES *n) {
  memset(n, 0, sizeof *n);
  for (int i = 0; i < 0x800; i++) n->ram[i] = (i & 4) ? 0xFF : 0x00;
  n->s = 0xFD;
  n->p = FI | FU | FB;
  n->flen = 262 * 341;
  n->hit_pos = n->overflow_pos = -1;
  n->dead = 1;
  n->pc = PRG[0x7FFC] | (PRG[0x7FFD] << 8);
  n->fpos = 22 * 341;
  n->ev_idx = PH_LSTART;
  sched(n);
  for (int i = 0; i < 7; i++) tick(n);
}

void nes_reset(NES *n) {
  n->s -= 3;
  n->p |= FI;
  n->ctrl = n->mask = n->w = n->vbl = 0;
  n->nmi_pending = n->nmi_line = n->nmi_polled = n->dma_pending = 0;
  n->dead = 1;
  n->pc = PRG[0x7FFC] | (PRG[0x7FFD] << 8);
  for (int i = 0; i < 7; i++) tick(n);
}

void nes_frame(NES *n, uint8_t pad1, uint8_t pad2) {
  n->pad[0] = pad1;
  n->pad[1] = pad2;
  n->polls = 0;
  n->frame_done = 0;
  unsigned fuel = 100000;
  while (!n->frame_done && fuel) { nes_step(n); fuel--; }
  if (!n->frame_done && !n->err) { n->err = 3; n->err_pc = n->pc; }
  n->frame++;
}
