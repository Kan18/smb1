// Minimal NROM NES model for Super Mario Bros. analysis.
// CPU: cycle-counted 6502 (official opcodes and NOP variants; other opcodes are flagged).
// PPU: event-driven timing model (vblank/NMI, sprite-0 hit, odd-frame skip) plus
//      register/VRAM behaviour; no pixel output.
#pragma once
#include <stdint.h>
#include <stdbool.h>

extern uint8_t PRG[0x8000], CHR[0x2000];
extern bool nes_vertical;
extern uint8_t *nes_acc;
extern uint8_t *nes_wr;

typedef struct {
  // CPU
  uint16_t pc;
  uint8_t a, x, y, s, p;
  uint8_t ram[0x800];
  // PPU
  uint8_t ctrl, mask, oamaddr, w, fx, rbuf, vbl, spr0, ovf, iolatch;
  uint16_t v, t;
  uint8_t ntram[0x800], pal[32], oam[256];
  int32_t fpos;     // dot position in current frame; frame starts at scanline 240 dot 0
  int32_t flen;     // dots in current frame
  int32_t overflow_pos;
  int32_t hit_pos;  // pending sprite-0 hit position on the current line, -1 if none
  int16_t line, sp0x;  // current render line; sprite-0 x on it (0x100 = none)
  uint8_t sp0data;
  int32_t next_ev;
  int8_t ev_idx;
  uint8_t odd, dead, nmi_pending, frame_done;
  uint8_t skipped, suppress_vbl, nmi_line, nmi_polled;
  uint8_t dma_pending, dma_page;
  // controllers
  uint8_t pad[2], sh[2], strobe;
  // CPU open-bus latch (part of the machine state)
  uint8_t bus, pad_read, pad_bit;
  uint64_t io_low, io_bit5, io_high;
  // validation bookkeeping
  uint32_t polls;   // controller strobe falling edges this frame
  uint8_t err;      // sticky: 1 = opcode, 2 = unsupported feature, 3 = step budget
  uint16_t err_pc;
  uint64_t cyc;
  uint32_t frame;
} NES;

static inline bool nes_final_victory(const NES *n) {
  return n->ram[0x770] == 2 && n->ram[0x75f] == 7 && n->ram[0x75c] == 3;
}

int nes_load_rom(const char *path);
void nes_power(NES *n);
void nes_reset(NES *n);
void nes_step(NES *n);                         // one instruction (+ pending NMI)
void nes_frame(NES *n, uint8_t pad1, uint8_t pad2);  // run until end of frame
