// A search with a chosen set of inputs and parent pointers, so a hit comes with its inputs, which it replays on the game.
// Not complete like range_dp: it's for finding runs. Inputs are every combination of the buttons in FREE, with the buttons in HELD always down.
// usage: line_search ROM MOVIE START T EVENT MINY FREE HELD   (buttons as a string of R L B A D)
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include "model.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { M m; int parent; u8 in; } N;
static u8 MAP[4096 * 13]; static u8 SEEN[4096];
static u8 bufcell(const uint8_t *r, int col, int row) { int base = (col & 16) ? 0x5D0 : 0x500; return r[base + (col & 15) + row * 16]; }
static void see(const uint8_t *r) { int left = (r[0x71A] * 256 + r[0x71C]) >> 4; for (int c = left; c < left + 17; c++) { if (c >= 4096 || SEEN[c]) continue; SEEN[c] = 1; for (int row = 0; row < 13; row++) MAP[c * 13 + row] = bufcell(r, c, row); } }
static u32 hsh(const M *t) { const u8 *p = (const u8 *)t; u32 h = 2166136261u; for (size_t i = 0; i < sizeof(M); i++) h = (h ^ p[i]) * 16777619u; return h; }
static int bits(const char *s) { int b = 0; for (; *s; s++) b |= *s == 'R' ? B_R : *s == 'L' ? B_L : *s == 'B' ? B_B : *s == 'A' ? B_A : *s == 'D' ? B_D : 0; return b; }
enum { TAB = 1 << 24 };
static NES stk[9]; static uint8_t seq[9];
static int tail(const NES *r, int d, int max, int fr) {
  static const uint8_t TAIL[8] = {0x00, 0x01, 0x80, 0x81, 0xC0, 0xC1, 0x40, 0x41};
  for (int i = 0; i < 8; i++) { stk[d] = *r; seq[d] = TAIL[i]; nes_frame(&stk[d], seq[d], 0); const uint8_t *q = stk[d].ram;
    if ((q[0xE] == 4 || q[0xE] == 5)) { if (q[0xCE] >= 162) { printf("grab on the game at frame %d, y %d, x %d, tail:", fr + d + 1, q[0xCE], q[0x6D] * 256 + q[0x86]); for (int w = 0; w <= d; w++) printf(" %02x", seq[w]); puts(""); return 1; } continue; }
    if (q[0xE] != 8 || d + 1 >= max) continue;
    if (tail(&stk[d], d + 1, max, fr)) return 1; }
  return 0; }
int main(int c, char **v) {
  setvbuf(stdout, NULL, _IOLBF, 0);
  if (c < 9 || nes_load_rom(v[1])) return 2; Movie mv; char err[128]; if (movie_load(v[2], &mv, err) || movie_align(&mv, err)) { puts(err); return 2; }
  int start = atoi(v[3]), T = atoi(v[4]), event = atoi(v[5]), miny = atoi(v[6]), freeb = bits(v[7]), held = bits(v[8]);
  static NES n, base; nes_power(&n); nes_reset(&n); M s; int area0 = -1;
  for (int f = 0; f <= start + T + 2 && f < mv.n; f++) { nes_frame(&n, mv.p1[f], mv.p2[f]); const uint8_t *r = n.ram; if (f == start) { base = n; area0 = r[0xE7]; see(r); memset(&s, 0, sizeof s); s.pos = (r[0x6D] << 16) | (r[0x86] << 8) | r[0x400]; s.v = r[0x57]; s.f = r[0x705]; s.abs_ = r[0x700]; s.face = r[0x33]; s.move = r[0x45]; s.st = r[0x1D]; s.t783 = r[0x783]; s.r703 = r[0x703]; s.y = r[0xCE]; s.ysub = r[0x416]; s.vy = r[0x9F]; s.vf = r[0x433]; s.g = r[0x709]; s.gfall = r[0x70A]; s.y0 = r[0x708]; s.rise = r[0x706]; s.area = r[0x74E]; s.yh = r[0xB5]; s.coll = r[0x490]; s.t784 = r[0x784]; s.prevA = (mv.p1[f] & 1) ? 0x80 : 0; s.ground = 176; } else if (f > start && r[0xE7] == area0) see(r); }
  m_tiles = MAP; m_cols = 4096;
  N **lay = calloc(T + 2, sizeof(N *)); int *cnt = calloc(T + 2, sizeof(int)); int *tab = malloc(TAB * sizeof(int));
  lay[0] = malloc(sizeof(N)); lay[0][0] = (N){s, -1, 0}; cnt[0] = 1;
  int ins[64], ni = 0; for (int in = 0; in < 64; in++) if ((in & ~freeb) == 0) ins[ni++] = in | held;
  for (int f = 1; f <= T; f++) {
    int cap = cnt[f - 1] * ni + 1; if (cap > 1 << 24) cap = 1 << 24; N *nx = malloc(cap * sizeof(N)); int k = 0; memset(tab, 0xFF, TAB * sizeof(int));
    for (int i = 0; i < cnt[f - 1]; i++) for (int q = 0; q < ni; q++) {
      M a = lay[f - 1][i].m; m_step(&a, ins[q]);
      if (a.evt == event && a.y >= miny) {
        printf("hit after %d frames (frame %d), y %d x %u.%02x\n", f, start + f, a.y, a.pos >> 8, a.pos & 255);
        u8 path[4096]; path[f - 1] = ins[q]; int p = i; for (int g = f - 1; g > 0; g--) { path[g - 1] = lay[g][p].in; p = lay[g][p].parent; }
        static const u8 MK[6] = {0x80, 0x40, 0x02, 0x01, 0x10, 0x20};
        NES r = base; for (int g = 0; g < f + 8; g++) { int in = g < f ? path[g] : 0; uint8_t b = 0; for (int w = 0; w < 6; w++) if (in & (1 << w)) b |= MK[w]; nes_frame(&r, b, 0); const uint8_t *q2 = r.ram; printf("%d in %02x x %d.%02x v %d y %d st %d eng %d\n", start + g + 1, b, q2[0x6D] * 256 + q2[0x86], q2[0x400], (int8_t)q2[0x57], q2[0xCE], q2[0x1D], q2[0xE]); }
        return 0; }
      if (a.evt) continue;
      u32 h = hsh(&a) & (TAB - 1);
      for (;;) { int e = tab[h]; if (e < 0) { if (k >= cap) { puts("too many states"); return 1; } tab[h] = k; nx[k++] = (N){a, i, (u8)ins[q]}; break; } if (!memcmp(&nx[e].m, &a, sizeof(M))) break; h = (h + 1) & (TAB - 1); }
    }
    if (f == T) { int hist[256] = {0}; u32 lo = (u32)-1, hi = 0; for (int i = 0; i < k; i++) { u32 x = nx[i].m.pos >> 8; if (x < lo) lo = x; if (x > hi) hi = x; if (nx[i].m.vy < 0x80 && x == (u32)atoi(getenv("XAT") ? getenv("XAT") : "0")) hist[nx[i].m.y]++; } printf("x %u..%u; falling at XAT, by y:", lo, hi); for (int y = 140; y < 180; y++) if (hist[y]) printf(" %d:%d", y, hist[y]); puts(""); }
    if (f == T && getenv("TARGETY")) {
      int ty = atoi(getenv("TARGETY")), xat = atoi(getenv("XAT")), shown = 0, grabs = 0;
      static const u8 MK[6] = {0x80, 0x40, 0x02, 0x01, 0x10, 0x20};
      for (int i = 0; i < k && shown < 400; i++) if (nx[i].m.y == ty && (int)(nx[i].m.pos >> 8) == xat && nx[i].m.vy < 0x80) {
        shown++; u8 path[4096]; path[f - 1] = nx[i].in; int p = nx[i].parent; for (int g = f - 1; g > 0; g--) { path[g - 1] = lay[g][p].in; p = lay[g][p].parent; }
        NES r = base; for (int g = 0; g < f; g++) { uint8_t b = 0; for (int w = 0; w < 6; w++) if (path[g] & (1 << w)) b |= MK[w]; nes_frame(&r, b, 0); }
        if (r.ram[0xCE] != ty || r.ram[0xE] != 8) { printf("candidate %d: the game has y %d engine %d x %d\n", shown, r.ram[0xCE], r.ram[0xE], r.ram[0x6D] * 256 + r.ram[0x86]); continue; }
        if (getenv("SHOWTAIL")) { printf("path:"); for (int g = 0; g < f; g++) { uint8_t b = 0; for (int w = 0; w < 6; w++) if (path[g] & (1 << w)) b |= MK[w]; printf(" %02x", b); } puts(""); static NES q; q = r; char *t = strdup(getenv("SHOWTAIL")), *tok; int fr = start + f; while ((tok = strsep(&t, " "))) { uint8_t b = strtol(tok, 0, 16); nes_frame(&q, b, 0); fr++; printf("%d in %02x x %d.%02x v %d y %d st %d eng %d move %d face %d\n", fr, b, q.ram[0x6D] * 256 + q.ram[0x86], q.ram[0x400], (int8_t)q.ram[0x57], q.ram[0xCE], q.ram[0x1D], q.ram[0xE], q.ram[0x45], q.ram[0x33]); } return 0; }
        // the last frames, on the game: every choice of right, left and A
        int found = tail(&r, 0, atoi(getenv("TAILN") ? getenv("TAILN") : "6"), start + f);
        if (found) { grabs++; printf("  candidate %d, from %d:", shown, start + 1); for (int g = 0; g < f; g++) { uint8_t b = 0; for (int w = 0; w < 6; w++) if (path[g] & (1 << w)) b |= MK[w]; printf(" %02x", b); } puts(""); }
        if (!found) { printf("candidate %d: x %d.%02x y %d, no low grab within 7 frames\n", shown, r.ram[0x6D] * 256 + r.ram[0x86], r.ram[0x400], r.ram[0xCE]); }
        if (grabs >= 3) break;
      }
      printf("%d candidates, %d grabs\n", shown, grabs); return 0;
    }
    lay[f] = nx; cnt[f] = k; if (f % 16 == 0 || f == T) { printf("%3d: %d states\n", f, k); fflush(stdout); }
  }
  printf("event %d at y >= %d not found in %d frames\n", event, miny, T); return 0;
}
