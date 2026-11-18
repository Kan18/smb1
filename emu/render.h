// A picture of the model's PPU state, written as a PNG, so a run can be looked at.
//
// What it draws is what the frame that just ended showed, rebuilt from the state the model keeps:
// the name tables, palette and sprite table, and the scroll the game wrote after the sprite-0 split
// (the `t` register and fine X at the frame's end). Above the split (the status bar, taken as the
// top 32 lines) the scroll is 0 on name table 0, as SMB's NMI sets it. Nothing mid-frame is modelled
// beyond that split, and the sprite-per-line limit isn't applied.
//
// With `grid` set, a strip on the left numbers the block rows and a strip below numbers the level's
// columns (from ScreenLeft, `$071A`/`$071C`, lined up with the displayed scroll), and lines mark the
// 16-px blocks under the status bar, with page boundaries in red.
#ifndef RENDER_H
#define RENDER_H
#include "nes.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t render_rgb[64][3] = {
  {84,84,84},{0,30,116},{8,16,144},{48,0,136},{68,0,100},{92,0,48},{84,4,0},{60,24,0},
  {32,42,0},{8,58,0},{0,64,0},{0,60,0},{0,50,60},{0,0,0},{0,0,0},{0,0,0},
  {152,150,152},{8,76,196},{48,50,236},{92,30,228},{136,20,176},{160,20,100},{152,34,32},{120,60,0},
  {84,90,0},{40,114,0},{8,124,0},{0,118,40},{0,102,120},{0,0,0},{0,0,0},{0,0,0},
  {236,238,236},{76,154,236},{120,124,236},{176,98,236},{228,84,236},{236,88,180},{236,106,100},{212,136,32},
  {160,170,0},{116,196,0},{76,208,32},{56,204,108},{56,180,204},{60,60,60},{0,0,0},{0,0,0},
  {236,238,236},{168,204,236},{188,188,236},{212,178,236},{236,174,236},{236,174,212},{236,180,176},{228,196,144},
  {204,210,120},{180,222,120},{168,226,144},{152,226,180},{160,214,228},{160,162,160},{0,0,0},{0,0,0},
};

#define RENDER_SPLIT 32

static inline uint8_t render_nt(const NES *n, unsigned a) {  // a: $2000-$2FFF
  unsigned i = nes_vertical ? (a & 0x7ff) : ((a & 0x3ff) | ((a >> 1) & 0x400));
  return n->ntram[i];
}

// The displayed scroll below the split, 0-511.
static inline int render_scroll(const NES *n) {
  return ((n->t >> 10) & 1) * 256 + (n->t & 31) * 8 + (n->fx & 7);
}

// Palette indices (0-63) of the 256x240 picture.
static inline void render_indices(const NES *n, uint8_t *out) {
  static uint8_t bgc[256 * 240];  // background colour number 0-3, for sprite priority
  unsigned bgpt = (n->ctrl & 0x10) ? 0x1000 : 0, sppt = (n->ctrl & 0x08) ? 0x1000 : 0;
  int sx = render_scroll(n), showbg = n->mask & 0x08, showsp = n->mask & 0x10;
  for (int y = 0; y < 240; y++)
    for (int x = 0; x < 256; x++) {
      int c = 0, p = 0;
      if (showbg) {
        int wx = y < RENDER_SPLIT ? x : (sx + x) & 511, wy = y;
        unsigned nt = 0x2000 + (wx >= 256 ? 0x400 : 0);
        int tx = (wx & 255) >> 3, ty = wy >> 3;
        uint8_t tile = render_nt(n, nt + ty * 32 + tx);
        uint8_t at = render_nt(n, nt + 0x3c0 + (ty >> 2) * 8 + (tx >> 2));
        p = (at >> (((ty & 2) << 1) | (tx & 2))) & 3;
        unsigned a = bgpt + tile * 16 + (wy & 7);
        int b = 7 - (wx & 7);
        c = ((CHR[a] >> b) & 1) | (((CHR[a + 8] >> b) & 1) << 1);
      }
      bgc[y * 256 + x] = c;
      out[y * 256 + x] = c ? n->pal[p * 4 + c] : n->pal[0];
    }
  if (!showsp) return;
  for (int s = 63; s >= 0; s--) {  // lower numbers drawn last, so on top
    const uint8_t *o = n->oam + s * 4;
    int top = o[0] + 1, flipv = o[2] & 0x80, fliph = o[2] & 0x40, behind = o[2] & 0x20;
    for (int r = 0; r < 8; r++) {
      int y = top + r;
      if (y >= 240) break;
      unsigned a = sppt + o[1] * 16 + (flipv ? 7 - r : r);
      for (int k = 0; k < 8; k++) {
        int x = o[3] + k;
        if (x > 255) break;
        int b = fliph ? k : 7 - k;
        int c = ((CHR[a] >> b) & 1) | (((CHR[a + 8] >> b) & 1) << 1);
        if (!c || (behind && bgc[y * 256 + x])) continue;
        out[y * 256 + x] = n->pal[16 + (o[2] & 3) * 4 + c];
      }
    }
  }
}

static inline uint32_t render_crc(const uint8_t *p, size_t len, uint32_t c) {
  static uint32_t t[256];
  if (!t[1]) for (uint32_t i = 0; i < 256; i++) { uint32_t v = i; for (int k = 0; k < 8; k++) v = v & 1 ? 0xedb88320 ^ (v >> 1) : v >> 1; t[i] = v; }
  c = ~c;
  for (size_t i = 0; i < len; i++) c = t[(c ^ p[i]) & 255] ^ (c >> 8);
  return ~c;
}

static inline void render_be32(uint8_t *p, uint32_t v) { p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v; }

static inline void render_chunk(FILE *f, const char *type, const uint8_t *data, uint32_t len) {
  uint8_t h[8]; render_be32(h, len); memcpy(h + 4, type, 4);
  fwrite(h, 1, 8, f); if (len) fwrite(data, 1, len, f);
  uint32_t c = render_crc((const uint8_t *)type, 4, 0); c = render_crc(data, len, c);
  render_be32(h, c); fwrite(h, 1, 4, f);
}

// An RGB image as a PNG, with zlib's stored (uncompressed) blocks.
static inline int render_write_png(const char *path, const uint8_t *rgb, int w, int h) {
  size_t raw = (size_t)h * (w * 3 + 1), nblk = raw / 65535 + 1;
  uint8_t *z = (uint8_t *)malloc(2 + raw + nblk * 5 + 4), *q = z;
  uint8_t *row = (uint8_t *)malloc(raw);
  for (int y = 0; y < h; y++) { row[(size_t)y * (w * 3 + 1)] = 0; memcpy(row + (size_t)y * (w * 3 + 1) + 1, rgb + (size_t)y * w * 3, w * 3); }
  *q++ = 0x78; *q++ = 0x01;
  uint32_t s1 = 1, s2 = 0;
  for (size_t i = 0; i < raw; i++) { s1 = (s1 + row[i]) % 65521; s2 = (s2 + s1) % 65521; }
  for (size_t off = 0; off < raw;) {
    size_t k = raw - off > 65535 ? 65535 : raw - off;
    *q++ = off + k == raw; *q++ = k & 255; *q++ = k >> 8; *q++ = ~k & 255; *q++ = (~k >> 8) & 255;
    memcpy(q, row + off, k); q += k; off += k;
  }
  render_be32(q, (s2 << 16) | s1); q += 4;
  FILE *f = fopen(path, "wb");
  if (!f) { free(z); free(row); return -1; }
  static const uint8_t sig[8] = {0x89, 'P', 'N', 'G', 13, 10, 26, 10};
  fwrite(sig, 1, 8, f);
  uint8_t ih[13]; render_be32(ih, w); render_be32(ih + 4, h); ih[8] = 8; ih[9] = 2; ih[10] = ih[11] = ih[12] = 0;
  render_chunk(f, "IHDR", ih, 13);
  render_chunk(f, "IDAT", z, (uint32_t)(q - z));
  render_chunk(f, "IEND", NULL, 0);
  fclose(f); free(z); free(row);
  return 0;
}

// A number in the game's own digit tiles (background tiles 0-9), white on the strip, 1 px per pixel.
static inline void render_number(uint8_t *rgb, int w, int h, int x0, int y0, int v, const NES *n) {
  char s[8]; int len = snprintf(s, sizeof s, "%d", v);
  unsigned bgpt = (n->ctrl & 0x10) ? 0x1000 : 0;
  for (int i = 0; i < len; i++)
    for (int r = 0; r < 8; r++)
      for (int k = 0; k < 8; k++) {
        unsigned a = bgpt + (s[i] - '0') * 16 + r;
        if (!(((CHR[a] | CHR[a + 8]) >> (7 - k)) & 1)) continue;
        int x = x0 + i * 8 + k, y = y0 + r;
        if (x < 0 || x >= w || y < 0 || y >= h) continue;
        memset(rgb + ((size_t)y * w + x) * 3, 255, 3);
      }
}

// The picture at `scale`, with the grid and number strips if `grid` is set.
static inline int render_png(const NES *n, const char *path, int scale, int grid) {
  static uint8_t idx[256 * 240];
  render_indices(n, idx);
  int lw = grid ? 24 : 0, bh = grid ? 12 : 0, w = 256 * scale + lw, h = 240 * scale + bh;
  uint8_t *rgb = (uint8_t *)calloc((size_t)w * h, 3);
  for (int y = 0; y < 240 * scale; y++)
    for (int x = 0; x < 256 * scale; x++)
      memcpy(rgb + ((size_t)y * w + lw + x) * 3, render_rgb[idx[(y / scale) * 256 + x / scale] & 63], 3);
  if (grid) {
    int full = n->ram[0x71a] * 256 + n->ram[0x71c];
    int left = full - (((full - render_scroll(n)) % 512 + 512) % 512);  // world X at screen X 0, as displayed
    for (int x = 0; x < 256; x++) {
      int wx = left + x;
      if (wx % 16) continue;
      int page = wx % 256 == 0;
      for (int y = RENDER_SPLIT * scale; y < 240 * scale; y++) {
        uint8_t *p = rgb + ((size_t)y * w + lw + x * scale) * 3;
        if (page) { p[0] = 255; p[1] = p[2] = 40; }
        else for (int c = 0; c < 3; c++) p[c] = (p[c] + 160) / 2;
      }
      int col = wx / 16;
      if (scale >= 2 || col % 2 == 0) render_number(rgb, w, h, lw + x * scale + 1, 240 * scale + 2, col, n);
    }
    for (int r = 0; r <= 12; r++) {
      int y = (RENDER_SPLIT + 16 * r) * scale;
      for (int x = 0; x < 256 * scale; x++) {
        uint8_t *p = rgb + ((size_t)y * w + lw + x) * 3;
        for (int c = 0; c < 3; c++) p[c] = (p[c] + 160) / 2;
      }
      render_number(rgb, w, h, 2, y + (16 * scale - 8) / 2, r, n);
    }
  }
  int rc = render_write_png(path, rgb, w, h);
  free(rgb);
  return rc;
}
#endif
