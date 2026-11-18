#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
// usage: blink_check ROM MOVIE F0 F1 RUNS LEN
// Random runs with InjuryTimer forced on: at each $B0E9 in normal play, XInv's last clause
// (0x50 <= $0755, $0785 = 0 -> on-screen X in 1..$7FFF) and how stale $0755 is.
int main(int c, char **v) { nes_load_rom(v[1]); Movie m; char err[128]; movie_load(v[2], &m, err); movie_align(&m, err);
  int F0 = atoi(v[3]), F1 = atoi(v[4]), runs = atoi(v[5]), len = atoi(v[6]); unsigned seed = 7;
  static NES s; nes_power(&s); nes_reset(&s); long visits = 0, stale = 0, bad = 0; int maxgap = 0;
  for (int fr = 0; fr < F0; fr++) { s.pad[0] = m.p1[fr]; s.pad[1] = 0; s.polls = 0; s.frame_done = 0; unsigned g = 100000; while (!s.frame_done && g--) nes_step(&s); s.frame++; }
  for (int f0 = F0; f0 <= F1; f0 += 10) {
    for (int r = 0; r < runs; r++) { static NES t; t = s;
      for (int k = 0; k < len; k++) { seed = seed * 1103515245 + 12345; unsigned q = seed >> 8;
        uint8_t pad = ((q & 7) ? 0x80 : 0) | ((q >> 3 & 1) ? 1 : 0) | ((q >> 4 & 3) ? 2 : 0) | ((q >> 6 & 7) == 0 ? 0x40 : 0) | ((q >> 9 & 15) == 0 ? 0x20 : 0);
        if (t.ram[0x79e] < 2) t.ram[0x79e] = 0x40;
        t.pad[0] = pad; t.pad[1] = 0; t.polls = 0; t.frame_done = 0; unsigned g = 100000;
        while (!t.frame_done && g--) {
          if (t.pc == 0xB0E9 && t.ram[0xe] == 8 && t.ram[0x74e] == 1) { visits++;
            int P = t.ram[0x6d] * 256 + t.ram[0x86], L = t.ram[0x71a] * 256 + t.ram[0x71c], d = (P - L) & 0xffff;
            if (t.ram[0x755] != (d & 0xff)) { stale++; int gap = abs((int)t.ram[0x755] - (d & 0xff)); if (gap > maxgap) maxgap = gap; }
            if (t.ram[0x755] >= 0x50 && t.ram[0x785] == 0 && (d == 0 || d >= 0x8000)) { bad++; if (bad < 10) printf("run from %d +%d: $0755 %02X, on-screen X %04X\n", f0, k, t.ram[0x755], d); } }
          nes_step(&t); }
        t.frame++; if (t.err || t.ram[0xe] != 8) break; } }
    for (int k = 0; k < 10; k++) { s.pad[0] = m.p1[f0 + k]; s.pad[1] = 0; s.polls = 0; s.frame_done = 0; unsigned g = 100000; while (!s.frame_done && g--) nes_step(&s); s.frame++; } }
  printf("%ld visits with InjuryTimer forced; $0755 stale at %ld (largest gap %d); XInv's last clause fails at %ld\n", visits, stale, maxgap, bad); }
