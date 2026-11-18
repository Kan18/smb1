// Checks that an .fm2 movie plays as intended in the model before it is analysed: ROM
// checksum, startup convention, levels entered, deaths, game overs, victory, and whether
// controller 2 matters (a second replay with it idle; the first frame whose RAM differs).
// usage: movieinfo rom.nes movie.fm2 [--raw]   (--raw: no startup conversion)
#include "nes.h"
#include "movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Replays the movie; with `report`, prints progress. Returns the RAM after every frame, or NULL
// if execution became unsupported (the rest of the buffer would be meaningless).
static uint8_t *play(const Movie *mv, int aligned, int pad2, int report) {
  static NES n;
  memset(&n, 0, sizeof n);
  nes_power(&n);
  if (aligned) nes_reset(&n);
  uint8_t *ram = malloc((size_t)mv->n * 0x800);
  int last_level = -1, last_mode = -1, deaths = 0, victory = -1;
  for (int f = 0; f < mv->n; f++) {
    if (mv->cmd[f] & 1) nes_reset(&n);
    if (mv->cmd[f] & 2) nes_power(&n);
    uint8_t lives = n.ram[0x75A], mode0 = n.ram[0x770];
    nes_frame(&n, mv->p1[f], pad2 ? mv->p2[f] : 0);
    memcpy(ram + (size_t)f * 0x800, n.ram, 0x800);
    if (n.err) {
      printf("UNSUPPORTED execution near %04X on frame %d%s\n", n.err_pc, f, pad2 ? "" : " (controller 2 idle)");
      free(ram);
      return NULL;
    }
    if (!report) continue;
    int mode = n.ram[0x770], level = n.ram[0x75F] << 16 | n.ram[0x75C] << 8 | n.ram[0x760];
    if (mode == 1 && (level != last_level || last_mode != 1))
      printf("frame %6d: %d-%d area %02X\n", f, n.ram[0x75F] + 1, n.ram[0x75C] + 1, n.ram[0x760]);
    if (mode0 == 1 && n.ram[0x75A] == (uint8_t)(lives - 1)) { deaths++; printf("frame %6d: DEATH (lives left %d)\n", f, n.ram[0x75A]); }
    if (mode == 3 && last_mode != 3) printf("frame %6d: GAME OVER\n", f);
    if (victory < 0 && nes_final_victory(&n)) { victory = f; printf("frame %6d: final victory\n", f); }
    last_level = level; last_mode = mode;
  }
  if (report) printf("end: %d frames, %d deaths, victory frame %d\n", mv->n, deaths, victory);
  return ram;
}

int main(int argc, char **argv) {
  if (argc < 3 || nes_load_rom(argv[1])) { fprintf(stderr, "usage: %s rom movie [--raw]\n", argv[0]); return 2; }
  int raw = argc > 3 && !strcmp(argv[3], "--raw");
  Movie mv;
  char err[128];
  if (movie_load(argv[2], &mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
  int rom = movie_rom_matches(&mv, argv[1]);
  printf("rom: %s\n", rom == 1 ? "matches" : rom == 0 ? "MISMATCH (recorded on another ROM; expect a desync)" : "unknown (no romChecksum)");
  printf("first frame: %s, %s\n", mv.cmd[0] & 2 ? "power" : mv.cmd[0] & 1 ? "reset" : "no command",
         mv.p1[0] || mv.p2[0] ? "buttons pressed" : "idle");
  int later = 0;
  for (int f = 1; f < mv.n; f++) if (mv.cmd[f]) later++;
  if (later) printf("commands after frame 0: %d frames (resets/power cycles)\n", later);
  if (!raw && movie_align(&mv, err)) { fprintf(stderr, "%s (try --raw)\n", err); return 2; }
  printf("startup: %s\n", raw ? "raw (every frame from power-on)" : "power-on + reset, first frame dropped (as the Lean model)");
  uint8_t *with = play(&mv, !raw, 1, 1);
  if (!with) return 1;
  if (mv.uses_p2) {
    uint8_t *without = play(&mv, !raw, 0, 0);
    if (!without) { printf("controller 2: MATTERS (execution differs with it idle)\n"); return 0; }
    int f = 0;
    while (f < mv.n && !memcmp(with + (size_t)f * 0x800, without + (size_t)f * 0x800, 0x800)) f++;
    if (f < mv.n) printf("controller 2: used, and MATTERS (RAM differs from frame %d with it idle)\n", f);
    else printf("controller 2: used, but ignorable (same RAM with it idle)\n");
  } else printf("controller 2: idle\n");
  return 0;
}
