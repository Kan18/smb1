// What values each RAM cell takes at frames' ends while Mario's on 1-1's surface before X reaches LIMIT: on the movie's frames from START, and on runs that follow the movie for a random
// stretch and then press random inputs. They're candidates for play_regions.py's bounds, nothing rests on them.
// usage: play_cells ROM MOVIE START LIMIT RUNS: prints each cell and its values, when there are at most 16
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef uint8_t u8; typedef uint32_t u32;
static u32 rs = 88172645; static u32 rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }
static u8 seen[0x800][32];
static void note(NES *n) { for (int i = 0; i < 0x800; i++) seen[i][n->ram[i] >> 3] |= 1 << (n->ram[i] & 7); }
static int xpos(NES *n) { return n->ram[0x6D] * 256 + n->ram[0x86]; }
static int inplay(NES *n, int limit) { return n->ram[0x770] == 1 && n->ram[0x772] == 3 && n->ram[0x74E] == 1 && n->ram[0x0E] == 8 && xpos(n) < limit; }
int main(int c, char **v) { if (c < 6 || nes_load_rom(v[1])) return 2; Movie m; char e[128]; if (movie_load(v[2], &m, e) || movie_align(&m, e)) return 2;
  int start = atoi(v[3]), limit = atoi(v[4]), runs = atoi(v[5]); static NES n, base, tas[800]; nes_power(&n); nes_reset(&n);
  for (int f = 0; f <= start; f++) nes_frame(&n, m.p1[f], m.p2[f]);
  base = n; int nt = 0;
  for (int f = 1; f < 800 && inplay(&n, limit); f++) { tas[nt++] = n; note(&n); nes_frame(&n, m.p1[start + f], m.p2[start + f]); }
  for (int r = 0; r < runs; r++) { n = tas[rnd() % nt]; int held = 0, left = 0;
    for (int f = 0; f < 600 && inplay(&n, limit); f++) { if (left-- <= 0) { held = rnd() & 0xCF; if (rnd() & 1) held = (held & ~2) | 1 | 0x40; left = rnd() % 24; } note(&n); nes_frame(&n, held & 0xFF, 0); } }
  for (int i = 0; i < 0x800; i++) { int k = 0; for (int b = 0; b < 256; b++) if (seen[i][b >> 3] >> (b & 7) & 1) k++;
    printf("%03x", i); if (k > 16) printf(" many%d", k); else for (int b = 0; b < 256; b++) if (seen[i][b >> 3] >> (b & 7) & 1) printf(" %02x", b); printf("\n"); }
  return 0; }
