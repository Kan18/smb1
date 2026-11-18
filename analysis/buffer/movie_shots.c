// Pictures of a movie's frames, for looking at a run: movie_shots ROM MOVIE FIRST LAST PREFIX
// Replays the movie (emu/movie.h's startup convention, so frame numbers are the aligned ones the notes use) and writes
// PREFIX<frame>.png (emu/render.h, 2x with the block grid) for FIRST..LAST. For each of those frames it also prints
// buffer 1's offset ($0300) at the frame's end and the largest value it reached during the frame, and $0340.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include "../../emu/render.h"
int main(int argc, char **argv) {
  if (argc < 6 || nes_load_rom(argv[1])) return 2;
  Movie m; char err[128];
  if (movie_load(argv[2], &m, err) || movie_align(&m, err)) { fprintf(stderr, "%s\n", err); return 2; }
  int first = atoi(argv[3]), last = atoi(argv[4]);
  static NES n; nes_power(&n); nes_reset(&n);
  for (int f = 0; f <= last && f < m.n; f++) {
    if (m.cmd[f] & 1) nes_reset(&n);
    if (m.cmd[f] & 2) nes_power(&n);
    n.pad[0] = m.p1[f]; n.pad[1] = m.p2[f]; n.polls = 0; n.frame_done = 0;
    unsigned fuel = 1000000; int peak = n.ram[0x300];
    while (!n.frame_done && fuel--) { nes_step(&n); if (n.ram[0x300] > peak) peak = n.ram[0x300]; }
    n.frame++;
    if (n.err) { fprintf(stderr, "model stopped at frame %d\n", f); return 1; }
    if (f >= first) {
      char path[512]; snprintf(path, sizeof path, "%s%d.png", argv[5], f);
      render_png(&n, path, 2, 1);
      printf("%d $0300=%02X peak=%02X $0340=%02X polls=%u\n", f, n.ram[0x300], peak, n.ram[0x340], n.polls);
    }
  }
  return 0;
}
