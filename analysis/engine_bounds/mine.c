// Seed RAM bounds for smbabs: the values a movie shows at chosen PCs, as `global` config lines.
// Only a starting point: smbabs widens them and the Lean checker decides. usage:
//   mine ROM MOVIE FIRST_FRAME END_FRAME MAX_VALUES PC...   (PCs in hex, frames in the TAS startup convention)
// A byte with more than MAX_VALUES values gets no line (unconstrained). The stack page is skipped.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>

#include "input.h"

static unsigned char seen[0x800][256];

int main(int argc, char **argv) {
  if (argc < 7 || nes_load_rom(argv[1])) { fprintf(stderr, "usage: mine ROM MOVIE FIRST END MAXV PC...\n"); return 2; }
  Movie m; char err[128];
  if (movie_load(argv[2], &m, err) || movie_align(&m, err)) { fprintf(stderr, "%s\n", err); return 2; }
  int first = number(argv[3], 10, INT_MAX), end = number(argv[4], 10, INT_MAX);
  unsigned maxv = number(argv[5], 10, 256);
  if (!maxv) { fprintf(stderr, "MAXV must be positive\n"); return 2; }
  window(&m, argv[1], first, end);
  int npc = argc - 6; unsigned pcs[16];
  if (npc > 16) { fprintf(stderr, "too many PCs\n"); return 2; }
  for (int i = 0; i < npc; i++) pcs[i] = number(argv[6 + i], 16, 0xffff);
  unsigned hits[16] = {0};
  static NES n; nes_power(&n); nes_reset(&n);
  for (int f = 0; f < m.n && f < end; f++) {
    if (m.cmd[f] & 1) nes_reset(&n);
    if (m.cmd[f] & 2) nes_power(&n);
    n.pad[0] = m.p1[f]; n.pad[1] = m.p2[f]; n.polls = 0; n.frame_done = 0;
    unsigned fuel = 100000;
    while (!n.frame_done && fuel--) {
      if (f >= first)
        for (int k = 0; k < npc; k++)
          if (n.pc == pcs[k]) {
            hits[k]++;
            for (int i = 0; i < 0x800; i++) seen[i][n.ram[i]] = 1;
          }
      nes_step(&n);
    }
    if (n.err || !n.frame_done) { fprintf(stderr, "unsupported or out of fuel at frame %d\n", f); return 1; }
    n.frame++;
  }
  for (int k = 0; k < npc; k++) if (!hits[k]) {
    fprintf(stderr, "no observations at PC %04x\n", pcs[k]); return 2;
  }
  for (int i = 0; i < 0x800; i++) {
    if (i >= 0x100 && i < 0x200) continue;
    unsigned k = 0;
    for (int j = 0; j < 256; j++) k += seen[i][j];
    if (k == 0 || k > maxv) continue;
    printf("global %x", i);
    for (int j = 0; j < 256; j++) if (seen[i][j]) printf(" %x", j);
    printf("\n");
  }
  return 0;
}
