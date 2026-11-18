// Which RAM cells stay the same through the launch, at frames' ends, on a movie's frames and on random inputs from its frame START? They're candidates for launch_regions.py's bounds.
// usage: launch_cells ROM MOVIE START LEN RUNS: prints each constant cell and value
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint8_t u8; typedef uint32_t u32;
static u32 rs = 88172645; static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
int main(int c, char **v) { if (c < 6 || nes_load_rom(v[1])) return 2; Movie m; char e[128]; if (movie_load(v[2], &m, e) || movie_align(&m, e)) return 2;
  int start = atoi(v[3]), len = atoi(v[4]), runs = atoi(v[5]); static NES n, base; nes_power(&n); nes_reset(&n); for (int f = 0; f <= start; f++) nes_frame(&n, m.p1[f], m.p2[f]); base = n;
  static u8 first[0x800], same[0x800]; memcpy(first, n.ram, 0x800); memset(same, 1, 0x800);
  for (int f = 1; f <= len; f++) { nes_frame(&n, m.p1[start + f], m.p2[start + f]); for (int i = 0; i < 0x800; i++) if (n.ram[i] != first[i]) same[i] = 0; }
  for (int r = 0; r < runs; r++) { n = base; int held = 0, left = 0; for (int f = 0; f < len; f++) { if (left-- <= 0) { held = rnd() & 0xFF; if (rnd() & 3) held &= 0xF7; if (rnd() & 1) held |= 0x80; if (rnd() & 1) held &= 0xBF; if (rnd() & 3) held &= 0xDF; left = rnd() % 12; } nes_frame(&n, held, 0); for (int i = 0; i < 0x800; i++) if (n.ram[i] != first[i]) same[i] = 0; } }
  for (int i = 0; i < 0x800; i++) if (same[i]) printf("%03x %02x\n", i, first[i]);
  return 0; }
