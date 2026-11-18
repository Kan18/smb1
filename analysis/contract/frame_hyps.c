#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// usage: frame_hyps ROM MOVIE F0 F1 [RUNS LEN SEED]
// What `PlayerJoin.cycle_frame` and `FrameChain.next_entry` still assume, measured at every visit to
// `PlayerCtrlRoutine` (`$B0E9`) in normal play (`$0E` = 8, overworld): no swimming, size change or jumpspring, the
// Y speed in -$40..$3F, the tail's copy of last frame's on-screen X in `$0755` (against the RAM at that frame's
// return into the engine, `$AF01`) and the side-collision timer still running where the impede set it.
// It also counts the frames `FramesBound.Odd` excludes: ending inside a player call, or with two calls.
// With RUNS: from each TAS frame F0..F1 in steps of 10, RUNS random runs of LEN frames, as `entry_check` does.
typedef struct { long visits, swim, size, spring, yspd, copy, copyInj, timer, noAf01, frames, lag, twice; } Count;
static unsigned char last[0x800]; static int haveLast;
static void visit(const NES *t, Count *c, int show, int fr) {
  const unsigned char *r = t->ram; c->visits++;
  if (r[0x704]) c->swim++;
  if (r[0x70b]) c->size++;
  if (r[0x70e]) c->spring++;
  if ((unsigned char)(r[0x9f] + 0x40) >= 0x80) c->yspd++;
  if (!haveLast) { c->noAf01++; return; }
  unsigned char d = (unsigned char)(last[0x86] - last[0x71c]);
  if (r[0x755] != d) { if (r[0x79e]) c->copyInj++; else { c->copy++; if (show && c->copy <= 10) printf("frame %d: $0755 = %02X, last frame's on-screen X %02X\n", fr, r[0x755], d); } }
  if (last[0x785] == 0x10 && r[0x785] == 0) c->timer++; }
static int inCall;
static void step_frame(NES *t, Count *c, int count, int fr) {
  t->polls = 0; t->frame_done = 0; unsigned g = 100000; int calls = 0, normal = 0;
  while (!t->frame_done && g--) {
    if (count && t->ram[0xe] == 8 && t->ram[0x74e] == 1) { normal = 1;
      if (t->pc == 0x8175) { calls++; inCall = 1; }
      if (t->pc == 0xB0E9) visit(t, c, 1, fr);
      if (t->pc == 0xAF01) { memcpy(last, t->ram, 0x800); haveLast = 1; inCall = 0; } }
    nes_step(t); }
  if (count && normal) { c->frames++; if (inCall) { c->lag++; if (c->lag <= 10) printf("frame %d ends inside a player call ($0E = %02X, PC %04X)\n", fr, t->ram[0xe], t->pc); } if (calls > 1) c->twice++; }
  t->frame++; }
static void report(const char *what, Count *c) {
  printf("%s: %ld visits to $B0E9; swimming %ld, size change %ld, jumpspring %ld, Y speed out of range %ld, "
         "$0755 not last frame's on-screen X %ld (and %ld more while InjuryTimer runs), timer run out %ld, no $AF01 before %ld; "
         "%ld frames, %ld ending inside a player call, %ld with two calls\n",
         what, c->visits, c->swim, c->size, c->spring, c->yspd, c->copy, c->copyInj, c->timer, c->noAf01, c->frames, c->lag, c->twice); }
int main(int argc, char **argv) {
  nes_load_rom(argv[1]); Movie m; char err[128]; if (movie_load(argv[2], &m, err) || movie_align(&m, err)) { puts(err); return 1; }
  int F0 = atoi(argv[3]), F1 = atoi(argv[4]); int runs = argc > 5 ? atoi(argv[5]) : 0, len = argc > 6 ? atoi(argv[6]) : 0;
  unsigned seed = argc > 7 ? atoi(argv[7]) : 1;
  static NES s; nes_power(&s); nes_reset(&s); Count c = {0};
  if (!runs) {
    for (int fr = 0; fr <= F1 && fr < m.n; fr++) { s.pad[0] = m.p1[fr]; s.pad[1] = 0; step_frame(&s, &c, fr >= F0, fr); }
    report("TAS", &c); return 0; }
  for (int fr = 0; fr < F0; fr++) { s.pad[0] = m.p1[fr]; s.pad[1] = 0; step_frame(&s, &c, 0, fr); }
  for (int f0 = F0; f0 <= F1; f0 += 10) {
    for (int r = 0; r < runs; r++) { static NES t; t = s; haveLast = 0; inCall = 0;
      for (int k = 0; k < len; k++) { seed = seed * 1103515245 + 12345; unsigned q = seed >> 8;
        uint8_t pad = ((q & 7) ? 0x80 : 0) | ((q >> 3 & 1) ? 1 : 0) | ((q >> 4 & 3) ? 2 : 0) | ((q >> 6 & 7) == 0 ? 0x40 : 0) | ((q >> 9 & 15) == 0 ? 0x20 : 0);
        t.pad[0] = pad; t.pad[1] = 0; step_frame(&t, &c, 1, f0 + k);
        if (t.err || t.ram[0xe] != 8) break; } }
    for (int k = 0; k < 10; k++) { s.pad[0] = m.p1[f0 + k]; s.pad[1] = 0; step_frame(&s, &c, 0, f0 + k); } }
  report("random runs", &c);
}
