// Replays an .fm2 movie in the model and lists every instruction (by PC) after which one of the
// watched RAM bytes changed, with how often. Default: Mario's vertical state ($9F speed, $433
// force, $416 sub-pixel, $CE Y, $B5 Y high).
// usage: writers rom movie [hex-address...]
// Startup as in the Lean model (`emu/movie.h`: power-on and reset, idle first frame dropped).
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXW 16
static uint16_t watch[MAXW] = {0x9F, 0x433, 0x416, 0xCE, 0xB5};
static int nwatch = 5;
static unsigned count[0x10000][MAXW];

int main(int argc, char **argv) {
  if (argc < 3 || nes_load_rom(argv[1])) { fprintf(stderr, "usage: %s rom movie [hex-address...]\n", argv[0]); return 2; }
  Movie mv;
  char err[128];
  if (movie_load(argv[2], &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
  if (argc > 3) {
    nwatch = 0;
    for (int i = 3; i < argc && nwatch < MAXW; i++) watch[nwatch++] = (uint16_t)strtol(argv[i], NULL, 16) & 0x7FF;
  }
  static NES n;
  nes_power(&n);
  nes_reset(&n);
  for (int frame = 0; frame < mv.n; frame++) {
    if (mv.cmd[frame] & 1) nes_reset(&n);
    if (mv.cmd[frame] & 2) nes_power(&n);
    n.pad[0] = mv.p1[frame];
    n.pad[1] = mv.p2[frame];
    n.polls = 0; n.frame_done = 0;
    unsigned fuel = 100000;
    while (!n.frame_done && fuel--) {
      uint8_t before[MAXW];
      for (int i = 0; i < nwatch; i++) before[i] = n.ram[watch[i]];
      uint16_t pc = n.pc;
      nes_step(&n);
      for (int i = 0; i < nwatch; i++) if (n.ram[watch[i]] != before[i]) count[pc][i]++;
    }
    n.frame++;
    if (n.err || !n.frame_done) { fprintf(stderr, "unsupported execution near %04X on frame %d\n", n.err_pc, frame); return 1; }
  }
  for (int pc = 0; pc < 0x10000; pc++)
    for (int i = 0; i < nwatch; i++) if (count[pc][i]) printf("%04X $%03X %u\n", pc, watch[i], count[pc][i]);
  return 0;
}
