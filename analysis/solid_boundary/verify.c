// Replays a movie prefix and a list of pad bytes from power-on, nothing else, and prints each
// PlayerBGCollision entry from a given frame with the table's leaves.
// usage: verify rom movie inputs-file [print-from]
#include "bgc.h"
#include <errno.h>
#include <limits.h>
static NES n;
int main(int argc, char **argv) {
  if (argc < 4 || nes_load_rom(argv[1])) return 2;
  Movie mv; char err[128];
  if (movie_load(argv[2], &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
  if (movie_rom_matches(&mv, argv[1]) != 1) { fprintf(stderr, "movie/ROM mismatch or missing identity\n"); return 2; }
  FILE *f = fopen(argv[3], "r");
  if (!f) { perror(argv[3]); return 2; }
  char line[128]; int start = -1, cap = 0; static uint8_t in[8192];
  while (fgets(line, sizeof line, f)) {
    if (!strchr(line, '\n') && !feof(f)) {
      fprintf(stderr, "input line is too long\n"); fclose(f); return 2;
    }
    if (line[0] == '#' || line[0] == '\n') continue;
    int is_start = !strncmp(line, "start ", 6);
    char *end;
    errno = 0;
    long value = strtol(line + (is_start ? 6 : 0), &end, is_start ? 10 : 16);
    if (errno || end == line + (is_start ? 6 : 0) || (*end && *end != '\n') ||
        value < 0 || value > (is_start ? mv.n : 255)) {
      fprintf(stderr, "invalid input line: %s", line); fclose(f); return 2;
    }
    if (is_start) {
      if (start >= 0 || cap) { fclose(f); return 2; }
      start = (int)value;
    } else {
      if (start < 0 || cap == (int)sizeof in) { fclose(f); return 2; }
      in[cap++] = (uint8_t)value;
    }
  }
  int read_error = ferror(f);
  fclose(f);
  if (read_error || start < 0 || !cap || start > INT_MAX - cap) return 2;
  int from = argc > 4 ? atoi(argv[4]) : start;
  nes_power(&n); nes_reset(&n);
  printf("frame pad  X    Y  lo ysp.fr sub xsp st dir sz | H lf rf | lu ll ru rl | leaves | after X Y ysp xsp st | world\n");
  int total = start + cap;
  for (int fr = 0; fr < total; fr++) {
    if (fr < start) { if (mv.cmd[fr] & 1) nes_reset(&n); if (mv.cmd[fr] & 2) nes_power(&n); }
    uint8_t pad = fr < start ? mv.p1[fr] : in[fr - start];
    if (fr < start) { n.pad[0] = pad; n.pad[1] = mv.p2[fr]; }
    else { n.pad[n.ram[0x753] ? 1 : 0] = pad; n.pad[n.ram[0x753] ? 0 : 1] = 0; }  // $753: current player
    n.polls = 0; n.frame_done = 0;
    unsigned fuel = 100000;
    while (!n.frame_done && fuel--) {
      if (n.pc == pcBG && fr >= from) {
        uint8_t *r = n.ram; int eb = bgc_eb(r); Out o = bgc_predict(r, NULL);
        printf("%5d %02x %03x %02x %2x %02x.%02x %02x  %02x  %d  %d  %d | %02x %02x %02x | %02x %02x %02x %02x | %05x | %03x %02x %02x %02x %d | %d-%d\n", fr, pad,
               r[rPage] << 8 | r[rX], r[rY], r[rY] & 15, r[rYSp], r[rYForce], r[rYSub], r[rXSp], r[rState], r[rMovDir], r[rSize],
               r[rY] >= 0x10 ? bb_tile(r, eb) : 0, bb_tile(r, eb + 1), bb_tile(r, eb + 2), r[rY] >= 0x20 ? bb_tile(r, eb + 3) : 0, r[rY] >= 8 ? bb_tile(r, eb + 4) : 0,
               r[rY] >= 0x20 ? bb_tile(r, eb + 5) : 0, r[rY] >= 8 ? bb_tile(r, eb + 6) : 0, o.leaf, o.page << 8 | o.x, o.y, o.ysp, o.xsp, o.state, r[rWorld] + 1, r[rLevel] + 1);
      }
      nes_step(&n);
    }
    n.frame++;
    if (n.err || !n.frame_done) {
      fprintf(stderr, "unsupported execution or exhausted fuel at frame %d, PC=%04X\n", fr, n.pc);
      return 1;
    }
  }
  printf("end: X=%03X Y=%02X state %d GE %X size %d\n", n.ram[rPage] << 8 | n.ram[rX], n.ram[rY], n.ram[rState], n.ram[rGE], n.ram[rSize]);
  return 0;
}
