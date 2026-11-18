// Replays an FM2 controller movie in the model and reports game progress.
// usage: replay rom.nes movie.fm2 [--tas-startup] [-v]
// --tas-startup: the model's startup convention (power-on and reset, idle first frame dropped;
// see movie.h). Without it every frame is played from power-on, commands included.
#include "nes.h"
#include "state.h"
#include "movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define OperMode 0x770
#define OperMode_Task 0x772
#define WorldNumber 0x75f
#define LevelNumber 0x75c
#define AreaNumber 0x760
#define Player_PageLoc 0x6d
#define Player_X_Position 0x86

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s rom movie [--tas-startup] [-v]\n", argv[0]); return 2; }
  int verbose = 0, tas_startup = 0;
  for (int i = 3; i < argc; i++) {
    if (!strcmp(argv[i], "-v")) verbose = 1;
    else if (!strcmp(argv[i], "--tas-startup")) tas_startup = 1;
    else { fprintf(stderr, "unknown option: %s\n", argv[i]); return 2; }
  }
  if (nes_load_rom(argv[1])) { fprintf(stderr, "rom load failed\n"); return 2; }
  Movie mv;
  char err[128];
  if (movie_load(argv[2], &mv, err) || (tas_startup && movie_align(&mv, err))) { fprintf(stderr, "%s\n", err); return 2; }
  if (movie_rom_matches(&mv, argv[1]) == 0) fprintf(stderr, "warning: the movie was recorded on another ROM (romChecksum)\n");
  static NES n;
  nes_power(&n);
  if (tas_startup) nes_reset(&n);
  int lag = 0, victory = -1;
  FILE *dump = getenv("DUMP") ? fopen(getenv("DUMP"), "wb") : NULL;
  FILE *states = getenv("STATE_DUMP") ? fopen(getenv("STATE_DUMP"), "wb") : NULL;
  if ((getenv("DUMP") && !dump) ||
      (getenv("STATE_DUMP") && !states)) { perror("output"); return 2; }
  uint8_t last_area = 0xff, last_mode = 0xff;
  int frame;
  for (frame = 0; frame < mv.n; frame++) {
    uint8_t b1 = mv.p1[frame], b2 = mv.p2[frame];
    if (mv.cmd[frame] & 1) nes_reset(&n);
    if (mv.cmd[frame] & 2) nes_power(&n);
    nes_frame(&n, b1, b2);
    if (!n.polls) { lag++; if (verbose) printf("  lag frame %d\n", frame); }
    if (getenv("TRACE") && frame >= atoi(getenv("TRACE")) && frame < atoi(getenv("TRACE")) + 400)
      printf("  f%d in=%02x x=%d.%02x y=%d spd=%d st=%d sub=%d\n", frame, b1, n.ram[Player_PageLoc]*256+n.ram[Player_X_Position], n.ram[0x400], n.ram[0xce], (int8_t)n.ram[0x57], n.ram[0x1d], n.ram[0x0e]);
    if (dump) fwrite(n.ram, 1, 2048, dump);
    if (states) dump_state(states, &n);
    uint8_t mode = n.ram[OperMode], area = n.ram[AreaNumber];
    if (verbose && (mode != last_mode || area != last_area))
      printf("frame %6d: mode=%d task=%d world=%d-%d area=%02x x=%d lag=%d\n", frame, mode, n.ram[OperMode_Task],
             n.ram[WorldNumber] + 1, n.ram[LevelNumber] + 1, area, n.ram[Player_PageLoc] * 256 + n.ram[Player_X_Position], lag);
    last_mode = mode; last_area = area;
    if (victory < 0 && nes_final_victory(&n)) victory = frame;
    if (n.err) { fprintf(stderr, "unsupported execution (error %d) near %04X on frame %d\n", n.err, n.err_pc, frame); return 1; }
  }
  printf("frames=%d lag=%d world=%d-%d mode=%d victory_frame=%d\n", frame, lag, n.ram[WorldNumber] + 1,
         n.ram[LevelNumber] + 1, n.ram[OperMode], victory);
  if (states && (ferror(states) || fclose(states))) return 2;
  if (dump && (ferror(dump) || fclose(dump))) return 2;
  return 0;  // Successful replay need not win (e.g. random-input experiments).
}
