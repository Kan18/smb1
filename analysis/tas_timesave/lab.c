// Inspect a controller movie in the NES model. usage: lab rom movie COMMAND
//   events        frames where the game engine state, area or level changes
//   trace f0 f1   Mario, camera and enemy slots after each aligned frame in f0..f1
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static Movie mv;
#define R(a) (n->ram[a])

static void checked_frame(NES *n, uint8_t p1) {
  nes_frame(n, p1, 0);
  if (n->err || !n->frame_done) {
    fprintf(stderr, "unsupported execution at frame %u, PC=%04X\n", n->frame, n->pc);
    exit(1);
  }
}

static void boot(NES *n) {
  memset(n, 0, sizeof *n);
  nes_power(n);
  nes_reset(n);
}

static int xpos(const NES *n) { return R(0x6d) * 256 + R(0x86); }

static void show(const NES *n, int f, int pad) {
  printf("f%6d pad=%02X ges=%d task=%d/%d ptr=%02X itc=%2d tmr=%d%d%d x=%5d.%02X y=%3d.%02X vx=%4d vy=%3d st=%d scr=%d",
         f, pad, R(0x0e), R(0x770), R(0x772), R(0x750), R(0x77f), R(0x7f8), R(0x7f9), R(0x7fa),
         xpos(n), R(0x400), R(0xce), R(0x416), (int8_t)R(0x57), (int8_t)R(0x9f), R(0x1d), R(0x71c) + 256 * R(0x71a));
  for (int s = 0; s < 6; s++)
    if (R(0x0f + s)) printf(" [%d:%02X %d,%d]", s, R(0x16 + s), R(0x6e + s) * 256 + R(0x87 + s), R(0xcf + s));
  printf("\n");
}

static void cmd_events(void) {
  static NES nn; NES *n = &nn;
  boot(n);
  int last[6] = {-1, -1, -1, -1, -1, -1};
  for (int f = 0; f < mv.n; f++) {
    checked_frame(n, mv.p1[f]);
    int cur[6] = {R(0x770), R(0x0e), R(0x750), R(0x75f) * 16 + R(0x75c), R(0x760), R(0x1d) == 3};
    if (memcmp(cur, last, sizeof cur)) {
      printf("f%6d mode=%d ges=%2d ptr=%02X level=%d-%d area=%d x=%5d y=%3d itc=%2d tmr=%d%d%d\n", f, cur[0], cur[1],
             cur[2], R(0x75f) + 1, R(0x75c) + 1, cur[4], xpos(n), R(0xce), R(0x77f), R(0x7f8), R(0x7f9), R(0x7fa));
      memcpy(last, cur, sizeof cur);
    }
  }
}

static void cmd_trace(int f0, int f1) {
  static NES nn; NES *n = &nn;
  boot(n);
  for (int f = 0; f <= f1 && f < mv.n; f++) {
    checked_frame(n, mv.p1[f]);
    if (f >= f0) show(n, f, mv.p1[f]);
  }
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s rom movie CMD [args]\n", argv[0]); return 2; }
  if (nes_load_rom(argv[1])) { fprintf(stderr, "rom load failed\n"); return 2; }
  char err[128];
  if (movie_load(argv[2], &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
  if (movie_rom_matches(&mv, argv[1]) != 1) {
    fprintf(stderr, "movie ROM checksum must match\n"); return 2;
  }
  for (int f = 0; f < mv.n; f++) {
    if (mv.p2[f] || mv.cmd[f]) {
      fprintf(stderr, "unsupported input at frame %d\n", f); return 2;
    }
  }
  const char *c = argv[3];
  if (!strcmp(c, "events")) cmd_events();
  else if (!strcmp(c, "trace") && argc == 6) cmd_trace(atoi(argv[4]), atoi(argv[5]));
  else { fprintf(stderr, "bad command\n"); return 2; }
  return 0;
}
