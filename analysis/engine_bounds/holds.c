// Checks global RAM bounds only, not registers, stack, Quiet, or the complete theorem premises. usage: holds ROM MOVIE BOUNDS PC_ENTRY PC_EXIT FIRST_FRAME END_FRAME
// Prints hit and failure counts, then `cell:count@first_frame` for each byte out of bounds. Exit status 1 on any failure.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "input.h"

static unsigned char ok[0x800][256], top[0x800];

int main(int argc, char **argv) {
  if (argc != 8 || nes_load_rom(argv[1])) { fprintf(stderr, "usage: holds ROM MOVIE BOUNDS ENTRY EXIT FIRST END\n"); return 2; }
  Movie m; char err[128];
  if (movie_load(argv[2], &m, err) || movie_align(&m, err)) { fprintf(stderr, "%s\n", err); return 2; }
  FILE *bf = fopen(argv[3], "r");
  if (!bf) { fprintf(stderr, "cannot open %s\n", argv[3]); return 2; }
  char line[4096];
  memset(top, 1, sizeof top);
  unsigned char present[0x800] = {0};
  unsigned row = 0;
  while (fgets(line, sizeof line, bf)) {
    row++;
    if (!strchr(line, '\n') && !feof(bf)) {
      fprintf(stderr, "bounds line %u too long\n", row); return 2;
    }
    line[strcspn(line, "#")] = 0;
    char *t = strtok(line, " \t\r\n");
    if (!t) continue;
    // Tracking hints do not constrain the observed RAM values.
    int track = !strcmp(t, "track");
    if (!track && strcmp(t, "global")) {
      fprintf(stderr, "bounds line %u: expected global or track\n", row); return 2;
    }
    t = strtok(NULL, " \t\r\n");
    if (!t) { fprintf(stderr, "missing bounds address\n"); return 2; }
    unsigned a = number(t, 16, 0x7ff);
    t = strtok(NULL, " \t\r\n");
    if (track) {
      if (t && number(t, 16, 0x7ff) < a) { fprintf(stderr, "reversed track range\n"); return 2; }
      if (strtok(NULL, " \t\r\n")) { fprintf(stderr, "extra track argument\n"); return 2; }
      continue;
    }
    if (present[a]++ || !t) { fprintf(stderr, "duplicate or empty bounds row\n"); return 2; }
    if (!strcmp(t, "top")) {
      if (strtok(NULL, " \t\r\n")) { fprintf(stderr, "extra top argument\n"); return 2; }
      continue;
    }
    top[a] = 0;
    while (t) {
      char *dash = strchr(t, '-');
      if (dash) *dash++ = 0;
      unsigned lo = number(t, 16, 255), hi = dash ? number(dash, 16, 255) : lo;
      if (hi < lo) { fprintf(stderr, "reversed byte range\n"); return 2; }
      for (unsigned v = lo; v <= hi; v++) ok[a][v] = 1;
      t = strtok(NULL, " \t\r\n");
    }
  }
  int read_error = ferror(bf);
  fclose(bf);
  if (read_error) { fprintf(stderr, "bounds read error\n"); return 2; }
  unsigned pc0 = number(argv[4], 16, 0xffff), pc1 = number(argv[5], 16, 0xffff);
  if (pc0 == pc1) { fprintf(stderr, "entry and exit PCs must differ\n"); return 2; }
  int first = number(argv[6], 10, INT_MAX), end = number(argv[7], 10, INT_MAX);
  window(&m, argv[1], first, end);
  static NES n; nes_power(&n); nes_reset(&n);
  long hits[2] = {0, 0}, bad[2] = {0, 0}, cell[0x800] = {0};
  int at[0x800];
  memset(at, -1, sizeof at);
  for (int f = 0; f < m.n && f < end; f++) {
    if (m.cmd[f] & 1) nes_reset(&n);
    if (m.cmd[f] & 2) nes_power(&n);
    n.pad[0] = m.p1[f]; n.pad[1] = m.p2[f]; n.polls = 0; n.frame_done = 0;
    unsigned fuel = 100000;
    while (!n.frame_done && fuel--) {
      int w = n.pc == pc0 ? 0 : n.pc == pc1 ? 1 : -1;
      if (w >= 0 && f >= first) {
        hits[w]++;
        int b = 0;
        for (int i = 0; i < 0x800; i++)
          if (!top[i] && !ok[i][n.ram[i]]) { b = 1; cell[i]++; if (at[i] < 0) at[i] = f; }
        bad[w] += b;
      }
      nes_step(&n);
    }
    if (n.err || !n.frame_done) { fprintf(stderr, "unsupported or out of fuel at frame %d\n", f); return 2; }
    n.frame++;
  }
  printf("entry hits %ld bad %ld; exit hits %ld bad %ld\n", hits[0], bad[0], hits[1], bad[1]);
  for (int i = 0; i < 0x800; i++) if (cell[i]) printf(" %03x:%ld@%d", i, cell[i], at[i]);
  printf("\n");
  if (!hits[0] || !hits[1]) { fprintf(stderr, "missing entry or exit observations\n"); return 2; }
  return bad[0] || bad[1] ? 1 : 0;
}
