#pragma once
#include "nes.h"
#include <stdio.h>

// Stable validation format: 52 little-endian 64-bit fields, then RAM, nametables,
// palette, and OAM. Kept in the same order as stateBytes in lean/Main.lean.
static inline void dump_state(FILE *out, const NES *n) {
  const uint64_t fields[] = {
    n->pc, n->a, n->x, n->y, n->s,
    n->p, n->ctrl, n->mask, n->oamaddr, n->w,
    n->fx, n->rbuf, n->vbl, n->spr0, n->ovf,
    n->iolatch, n->v, n->t, n->fpos, n->flen,
    (uint32_t)n->hit_pos, n->line, n->sp0x, n->sp0data, n->next_ev,
    n->ev_idx, n->odd, n->dead, n->nmi_pending, n->frame_done,
    n->pad[0], n->pad[1], n->sh[0], n->sh[1], n->strobe,
    n->bus, n->polls, n->err != 0, n->cyc,
    nes_vertical, n->skipped, n->suppress_vbl, n->nmi_line, n->nmi_polled,
    n->dma_pending, n->dma_page, (uint32_t)n->overflow_pos, n->pad_read,
    n->pad_bit, n->io_low, n->io_bit5, n->io_high};
  for (size_t i = 0; i < sizeof fields / sizeof *fields; i++)
    for (int j = 0; j < 8; j++) fputc((fields[i] >> (8 * j)) & 0xff, out);
  fwrite(n->ram, 1, sizeof n->ram, out);
  fwrite(n->ntram, 1, sizeof n->ntram, out);
  fwrite(n->pal, 1, sizeof n->pal, out);
  fwrite(n->oam, 1, sizeof n->oam, out);
}
