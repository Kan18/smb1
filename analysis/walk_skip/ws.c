// Walk-skip experiments from movie states. usage: ws rom movie CMD [args]
//   trace f0 f1                 Mario's variables after each movie frame
//   bfs f0 depth lo hi xneed [maxfront [prefix]]   breadth-first search over inputs from the state after f0, merging by key()
// States merged by key() are not byte-identical; a hit is only evidence until replayed from power-on.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static NES *snap; static Movie mv;

// Stop instead of counting an unsupported branch as evidence.
static void checked_frame(NES *n, uint8_t p1, uint8_t p2) {
  nes_frame(n, p1, p2);
  if (n->err || !n->frame_done) {
    fprintf(stderr, "unsupported execution at frame %u, PC=%04X\n", n->frame, n->pc);
    exit(1);
  }
}

#define R(a) (n->ram[a])

static void show(const NES *n, int f, int pad) {
  printf("f%6d pad=%02X st=%d y=%3d.%02X vy=%3d.%02X x=%2d:%3d.%02X vx=%4d abs=%3d mdir=%d fdir=%d vf=%02X vd=%02X org=%3d side=%2d bits=%02X run=%2d/%d ges=%d size=%d cr=%d\n",
    f, pad, R(0x1d), R(0xce), R(0x416), (int8_t)R(0x9f), R(0x433), R(0x6d), R(0x86), R(0x400), (int8_t)R(0x57), R(0x700), R(0x45), R(0x33),
    R(0x709), R(0x70a), R(0x708), R(0x785), R(0x490), R(0x783), R(0x703), R(0x0e), R(0x754), R(0x714));
}

static const uint16_t KEY[] = {0x1d,0xce,0xb5,0x416,0x9f,0x433,0x6d,0x86,0x400,0x57,0x700,0x45,0x33,0x709,0x70a,0x708,0x706,0x785,0x490,0x783,0x703,0x754,0x714,0x74a,0x0e,0x702,0x701};
#define NKEY (sizeof KEY / sizeof *KEY)
typedef struct { uint8_t k[NKEY]; } Key;
typedef struct { int parent; uint8_t pad; } Back;

static uint64_t hkey(const uint8_t *k) { uint64_t h = 0xcbf29ce484222325ULL; for (unsigned i = 0; i < NKEY; i++) { h ^= k[i]; h *= 0x100000001b3ULL; } return h; }

// open-addressed set of 64-bit hashes (collisions lose a state; negligible at this size, and only for search)
static uint64_t *seen; static size_t seen_cap, seen_n;
static int seen_add(uint64_t h) {
  if (!h) h = 1;
  size_t m = seen_cap - 1, i = h & m;
  while (seen[i]) { if (seen[i] == h) return 0; i = (i + 1) & m; }
  seen[i] = h; seen_n++;
  return 1;
}

static const uint8_t PADS[] = {0x00,0x80,0x40,0xC0,0x01,0x81,0x41,0xC1,0x02,0x82,0x42,0xC2,0x03,0x83,0x43,0xC3};

static Back *backs; static size_t nback;
static void print_path(int b) {
  static uint8_t st[4096]; int k = 0;
  for (; b > 0 && k < 4096; b = backs[b].parent) st[k++] = backs[b].pad;
  while (k) printf(" %02X", st[--k]);
}

// target X: pole column left edge is col; grab needs X nibble 6..9, X + 13 in col.
static long best_band = -(1L << 30), best_gnd = -(1L << 30); static int best_band_b, best_gnd_b;
static void cmd_bfs(int f0, int depth, int lo, int hi, int xneed, size_t maxfront, int prefix) {
  if (depth < 1 || depth > 64 || maxfront < 1 || maxfront > 10000 || prefix < 0 || prefix > 10000) {
    fprintf(stderr, "bfs limits: depth 1..64, frontier 1..10000, prefix 0..10000\n"); exit(2);
  }
  size_t backcap = maxfront * (size_t)depth + 21;
  seen_cap = 1;
  while (seen_cap < backcap * 32) seen_cap *= 2;
  typedef struct { NES s; int b; } E;
  size_t bytes = seen_cap * sizeof(uint64_t) + backcap * sizeof(Back) + 2 * sizeof(E) * maxfront;
  if (bytes > 256u * 1024u * 1024u) { fprintf(stderr, "bfs exceeds 256 MiB budget; reduce frontier/depth\n"); exit(2); }
  seen = calloc(seen_cap, sizeof *seen);
  backs = malloc(backcap * sizeof *backs); nback = 1;
  E *cur = malloc(sizeof(E) * maxfront), *nxt = malloc(sizeof(E) * maxfront);
  if (!seen || !backs || !cur || !nxt) { fprintf(stderr, "bfs allocation failed\n"); exit(2); }
  backs[0].parent = -1;
  size_t ncur = 1, nnxt; cur[0].s = snap[f0]; cur[0].b = 0;
  for (int i = 0; i < prefix; i++) checked_frame(&cur[0].s, 0x82, 0);
  if (prefix) { NES *n = &cur[0].s; printf("after %d frames R+B: ", prefix); show(n, f0 + prefix, 0x82); }
  int page0 = snap[f0].ram[0x6d];
  long hist[256] = {0}, hits = 0, frames = 0, trunc = 0;
  for (int d = 1; d <= depth && ncur; d++) {
    nnxt = 0;
    for (size_t i = 0; i < ncur; i++) {
      for (unsigned p = 0; p < sizeof PADS; p++) {
        static NES m; m = cur[i].s; NES *n = &m;
        checked_frame(n, PADS[p], 0); frames++;
        if (n->err) continue;
        if (R(0x0e) != 8) {
          if (R(0x0e) == 4 || R(0x0e) == 5) {
            int y = R(0xce); hist[y]++;
            if (y >= lo && y <= hi) {
              hits++;
              if (nback >= backcap) { trunc++; continue; }
              backs[nback].parent = cur[i].b; backs[nback].pad = PADS[p]; nback++;
              if (hits <= 20) { printf("HIT d=%d f=%d y=%d ges=%d inputs:", d, f0 + d, y, R(0x0e)); print_path(nback - 1); printf("\n"); show(n, f0 + d, PADS[p]); fflush(stdout); }
            }
          }
          continue;
        }
        if (R(0x1d) > 2 && R(0x1d) != 1) continue;
        if (R(0xb5) != 1) continue;
        int xabs = R(0x6d) * 256 + R(0x86);
        if (xabs + (depth - d) * 3 < xneed) continue;     // cannot reach the pole in time
        if (xabs > xneed + 3 + 256) continue;
        (void)page0;
        uint8_t k[NKEY]; for (unsigned j = 0; j < NKEY; j++) k[j] = R(KEY[j]);
        if (!seen_add(hkey(k))) continue;
        if (nnxt >= maxfront || nback >= backcap) { trunc++; continue; }
        backs[nback].parent = cur[i].b; backs[nback].pad = PADS[p];
        nxt[nnxt].s = m; nxt[nnxt].b = nback++; nnxt++;
        { static const char *ge; static int gx, init; if (!init) { init = 1; ge = getenv("WS_GX"); gx = ge ? atoi(ge) : 0; }
          static long bestg = -1; static long ng;
          if (gx && R(0x1d) == 0 && R(0xce) >= 181) { ng++; long xg = xabs * 256L + R(0x400); if (xg > bestg) { bestg = xg; printf("  on ground below the surface: y=%d x=%d (left point in wall needs %d) vx=%d d=%d n=%ld inputs:", R(0xce), xabs, gx, (int8_t)R(0x57), d, ng); print_path(nback - 1); printf("\n"); fflush(stdout); } } }
        long xf = (long)(xabs - xneed) * 256 + R(0x400);   // X relative to the first grabbing X, in 1/256 px
        if (R(0xce) >= 165 && R(0xce) <= 167 && (int8_t)R(0x9f) < 0 && xf > best_band) { best_band = xf; best_band_b = nback - 1; printf("  rising in band, best X-need %.3f y=%d vy=%d d=%d inputs:", xf / 256.0, R(0xce), (int8_t)R(0x9f), d); print_path(best_band_b); printf("\n"); }
        if (R(0x1d) == 0 && R(0xce) == 176 && R(0x700) >= 0x19 && xf > best_gnd) { best_gnd = xf; best_gnd_b = nback - 1; printf("  ground with abs>=$19, best X-need %.3f abs=%d vx=%d d=%d\n", xf / 256.0, R(0x700), (int8_t)R(0x57), d); }
      }
    }
    E *t = cur; cur = nxt; nxt = t; ncur = nnxt;
    printf("depth %d: frontier %zu seen %zu frames %ld trunc %ld hits %ld\n", d, ncur, seen_n, frames, trunc, hits); fflush(stdout);
  }
  printf("grab Y histogram:"); for (int y = 0; y < 256; y++) if (hist[y]) printf(" %d:%ld", y, hist[y]); printf("\n");
}

// Necessary condition for a fast-jump grab [edit]: from the state after f (Mario on the ground), set X and speeds;
// frame 1 presses A with any L/R, frame 2 any L/R. Reports the grabs at Y 165..167 by X and vx.
static void cmd_jumpgrid(int f, int need) {
  static const int8_t VX[] = {-40,-30,-25,-8,-1,0,1,8,25,30,40};
  static const uint8_t LR[] = {0x00,0x80,0x40,0xC0};
  long runs = 0, hits = 0;
  for (unsigned v = 0; v < sizeof VX; v++) {
    int minx = 1 << 30, maxx = -(1 << 30);
    for (int x16 = (need - 8) * 16; x16 <= (need + 8) * 16; x16++) {
      int hit = 0;
      for (int a = 0; a < 4 && !hit; a++) for (int b = 0; b < 4 && !hit; b++) {
        static NES m; m = snap[f]; NES *n = &m;
        R(0x6d) = (x16 >> 4) >> 8; R(0x86) = (x16 >> 4) & 255; R(0x400) = (x16 & 15) << 4; R(0x57) = (uint8_t)VX[v]; R(0x700) = 40;
        R(0x45) = VX[v] < 0 ? 2 : 1; R(0x1d) = 0; R(0xce) = 176; R(0x416) = 0; R(0x9f) = 0; R(0x433) = 0; R(0x74a) = 0; R(0x785) = 0;
        checked_frame(n, LR[a] | 3, 0); runs++;
        if (R(0x0e) == 8) { checked_frame(n, LR[b] | 2, 0); runs++; }
        if ((R(0x0e) == 5 || R(0x0e) == 4) && R(0xce) >= 165 && R(0xce) <= 167) hit = 1;
      }
      if (hit) { hits++; if (x16 < minx) minx = x16; if (x16 > maxx) maxx = x16; }
    }
    if (minx < (1 << 30)) printf("vx=%4d: grab in band from X0-need in [%+.3f, %+.3f]\n", VX[v], minx / 16.0 - need, maxx / 16.0 - need);
    else printf("vx=%4d: no grab in band for X0-need in [-8,+8]\n", VX[v]);
  }
  printf("jumpgrid: %ld frames, %ld X values with a hit\n", runs, hits);
}

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint32_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs >> 32; }

// Random play from movie states f0, f0+step, ... f1: how far right do enemies get? Near = within 48 px of pole X.
static void cmd_foefuzz(int f0, int f1, int step, int trials, int len, int polex, unsigned seed) {
  rs ^= (uint64_t)seed * 0x100000001B3ULL; for (int i = 0; i < 8; i++) rnd();
  int maxx[256]; for (int i = 0; i < 256; i++) maxx[i] = -1;
  long frames = 0, near[256] = {0}, stomps = 0; int moves[] = {0x82,0x82,0x83,0x81,0x80,0x42,0x40,0x00,0x01,0x43};
  for (int f = f0; f <= f1; f += step) for (int t = 0; t < trials; t++) {
    static NES m; m = snap[f]; NES *n = &m; uint8_t b = 0x82;
    int stay = rnd() % 3 == 0;
    for (int i = 0; i < len; i++) {
      if (!(rnd() & 7)) { b = moves[rnd() % 10]; if (stay && (rnd() & 1)) b = 0x42; }
      int vy0 = R(0x9f);
      checked_frame(n, b, 0); frames++;
      if (n->err || R(0x0e) != 8 || R(0x770) != 1 || R(0x772) != 3) break;
      if ((int8_t)R(0x9f) < -2 && (int8_t)vy0 >= 0 && R(0x1d) != 0 && (R(0x9f) == 0xFC || R(0x9f) == 0xFD)) stomps++;
      for (int e = 0; e < 6; e++) if (R(0x0f + e)) {
        int id = R(0x16 + e), x = R(0x6e + e) * 256 + R(0x87 + e);
        if (id == 0x30 || id == 0x31 || R(0xb6 + e) != 1) continue;
        if (x > maxx[id]) maxx[id] = x;
        if (x >= polex - 48 && x <= polex + 48 && R(0xcf + e) >= 140) near[id]++;
      }
    }
  }
  printf("foefuzz f=%d..%d step %d trials %d len %d: %ld frames, stomps seen %ld; pole X %d\n", f0, f1, step, trials, len, frames, stomps, polex);
  for (int i = 0; i < 256; i++) if (maxx[i] >= 0) printf("  id %02X: max X %d (pole%+d), frames near pole at Y>=140: %ld\n", i, maxx[i], maxx[i] - polex, near[i]);
}

// [edit] a moving shell placed at each X in [x0,x1] moving right from the state after f: furthest X and fate.
static void cmd_shell(int f, int x0, int x1, int st) {
  int best = -1, bestfrom = 0, n_ret = 0, n_pit = 0, n_gone = 0;
  for (int x = x0; x <= x1; x += 4) {
    static NES m; m = snap[f]; NES *n = &m; int e = 0;
    R(0x0f + e) = 1; R(0x16 + e) = 0; R(0x6e + e) = x >> 8; R(0x87 + e) = x & 255; R(0xcf + e) = 184; R(0xb6 + e) = 1;
    R(0x1e + e) = st; R(0x58 + e) = 48; R(0x46 + e) = 1; R(0xa0 + e) = 0; R(0x434 + e) = 0;
    int mx = x, fate = 0;
    for (int i = 0; i < 300; i++) {
      checked_frame(n, 0, 0);
      if (!R(0x0f + e)) { fate = 2; break; }
      int nx = R(0x6e + e) * 256 + R(0x87 + e);
      if (nx > mx) mx = nx;
      if (R(0xb6 + e) != 1 || R(0xcf + e) > 208) { fate = 1; break; }
      if ((int8_t)R(0x58 + e) < 0) { fate = 3; break; }
    }
    if (fate == 1) n_pit++; else if (fate == 3) n_ret++; else n_gone++;
    if (mx > best) { best = mx; bestfrom = x; }
  }
  printf("shell st=%02X from X in [%d,%d]: furthest X %d (from %d); fell %d, turned back %d, other %d\n", st, x0, x1, best, bestfrom, n_pit, n_ret, n_gone);
}

int main(int argc, char **argv) {
  if (argc < 4 || nes_load_rom(argv[1])) { fprintf(stderr, "usage: ws rom movie CMD\n"); return 2; }
  char err[128];
  if (movie_load(argv[2], &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
  if (movie_rom_matches(&mv, argv[1]) != 1) { fprintf(stderr, "movie/ROM mismatch or missing identity\n"); return 2; }
  const char *command = argv[3];
  int need = !strcmp(command,"trace") || !strcmp(command,"jumpgrid") || !strcmp(command,"cannon") ? 6 :
    !strcmp(command,"map") ? 5 : !strcmp(command,"foes") || !strcmp(command,"cantab") || !strcmp(command,"fastjump") ? 7 :
    !strcmp(command,"shell") || !strcmp(command,"inshow") ? 8 : !strcmp(command,"foefuzz") ? 11 :
    !strcmp(command,"inground") ? 10 : !strcmp(command,"pitfuzz") || !strcmp(command,"bfs") ? 9 :
    !strcmp(command,"ingrid") ? 6 : 0;
  if (!need || argc < need) { fprintf(stderr, "unknown command or missing arguments\n"); return 2; }
  int first = atoi(argv[4]);
  if (first < 0 || first >= mv.n) return 2;
  if (!strcmp(command,"trace") || !strcmp(command,"foes") || !strcmp(command,"cannon") || !strcmp(command,"cantab") || !strcmp(command,"foefuzz")) {
    int last = atoi(argv[5]);
    if (last < first || last >= mv.n) return 2;
  }
  if ((!strcmp(command,"foes") || !strcmp(command,"cantab") || !strcmp(command,"foefuzz")) && atoi(argv[6]) <= 0) return 2;
  if (!strcmp(command,"pitfuzz") && (atoi(argv[5]) < 1 || atoi(argv[5]) > 512)) return 2;
  snap = malloc(sizeof(NES) * (size_t)mv.n);
  if (!snap) { fprintf(stderr, "snapshot allocation failed\n"); return 2; }
  static NES n0; nes_power(&n0); nes_reset(&n0);
  for (int f = 0; f < mv.n; f++) {
    if (mv.cmd[f] & 1) nes_reset(&n0);
    if (mv.cmd[f] & 2) nes_power(&n0);
    checked_frame(&n0, mv.p1[f], mv.p2[f]); snap[f] = n0;
  }
  const char *c = argv[3];
  if (!strcmp(c, "trace")) { for (int f = atoi(argv[4]); f <= atoi(argv[5]); f++) show(&snap[f], f, mv.p1[f]); }
  else if (!strcmp(c, "map")) { // block buffer around a column at state f: 2 pages, 13 rows from Y=$20
    NES *n = &snap[atoi(argv[4])]; int cols = R(0x6d) * 16 + R(0x86) / 16;
    printf("mario page %d x %d y %d; screenleft page %d x %d; buffer pages: columns 0..31 map to $500+\n", R(0x6d), R(0x86), R(0xce), R(0x71a), R(0x71c));
    for (int r = 0; r < 13; r++) { printf("y=%3d:", 0x20 + r * 16); for (int c2 = 0; c2 < 32; c2++) printf(" %02X", R(0x500 + (c2 < 16 ? 0 : 0xd0) + (c2 % 16) + r * 16)); printf("\n"); }
    (void)cols;
  }
  else if (!strcmp(c, "foes")) { // enemy slots every `step` frames over f0..f1
    int step = atoi(argv[6]);
    for (int f = atoi(argv[4]); f <= atoi(argv[5]); f += step) { NES *n = &snap[f]; printf("f%6d m=%2d:%3d y=%3d |", f, R(0x6d), R(0x86), R(0xce));
      for (int i = 0; i < 6; i++) if (R(0x0f + i)) printf(" [%d id=%02X %2d:%3d y=%3d st=%02X vx=%3d]", i, R(0x16 + i), R(0x6e + i), R(0x87 + i), R(0xcf + i), R(0x1e + i), (int8_t)R(0x58 + i));
      printf("\n"); } }
  else if (!strcmp(c, "jumpgrid")) cmd_jumpgrid(atoi(argv[4]), atoi(argv[5]));
  else if (!strcmp(c, "foefuzz")) cmd_foefuzz(atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]), atoi(argv[8]), atoi(argv[9]), atoi(argv[10]));
  else if (!strcmp(c, "shell")) cmd_shell(atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), strtol(argv[7], 0, 16));
  else if (!strcmp(c, "inground")) { // [edit] state after f with Mario on the ground at Y=192 inside the floor at X, moving at vx: search for a grab
    int f = atoi(argv[4]), x = atoi(argv[5]), y = atoi(argv[6]), vx = atoi(argv[7]);
    NES *n = &snap[f]; R(0x6d) = x >> 8; R(0x86) = x & 255; R(0xce) = y; R(0x1d) = 0; R(0x9f) = 0; R(0x433) = 0; R(0x416) = 0; R(0x57) = (uint8_t)vx; R(0x700) = vx < 0 ? -vx : vx; R(0x45) = 1; R(0x33) = 1;
    cmd_bfs(f, atoi(argv[8]), 165, 167, atoi(argv[9]), 2000, 0);
  }
  else if (!strcmp(c, "inshow")) { // [edit] one such run, printed
    int f = atoi(argv[4]), x = atoi(argv[5]), t = atoi(argv[6]), h = atoi(argv[7]);
    static NES m; m = snap[f]; NES *n = &m;
    R(0x6d) = x >> 8; R(0x86) = x & 255; R(0xce) = 192; R(0x1d) = 0; R(0x9f) = 0; R(0x433) = 0; R(0x416) = 0; R(0x57) = 40; R(0x700) = 40; R(0x45) = 1; R(0x33) = 1;
    for (int i = 0; i < 26; i++) { checked_frame(n, 0x82 | (i >= t && i < t + h ? 1 : 0), 0); show(n, i, 0x82 | (i >= t && i < t + h ? 1 : 0)); if (R(0x0e) != 8) break; }
  }
  else if (!strcmp(c, "fastjump")) { // legal inputs from the state after f + prefix frames of R+B: R+B for n frames with one tap, then A; best X at Y 165..167 rising
    int f = atoi(argv[4]), pre = atoi(argv[5]), need = atoi(argv[6]); static const uint8_t TAP[] = {0x82,0x00,0x80,0x40,0xC0,0xC2,0x02};
    static const uint8_t LR[] = {0x00,0x80,0x40,0xC0}; long runs = 0, grabs = 0, band = 0; long best = -(1L << 40); int hist[256] = {0}; static NES s0; s0 = snap[f];
    for (int i = 0; i < pre; i++) checked_frame(&s0, 0x82, 0);
    for (int nn = 0; nn <= 16; nn++) for (int p = 0; p <= nn; p++) for (unsigned tp = 0; tp < (p == nn ? 1 : sizeof TAP); tp++) for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) for (int hA = 0; hA < 2; hA++) {
      static NES m; m = s0; NES *n = &m; int dead = 0; runs++;
      for (int i = 0; i < nn && !dead; i++) { checked_frame(n, i == p ? TAP[tp] : 0x82, 0); if (R(0x0e) != 8) dead = 1; }
      if (dead) continue;
      checked_frame(n, LR[a] | 3, 0);
      if (R(0x0e) == 8) checked_frame(n, LR[b] | 2 | hA, 0);
      if (R(0x0e) == 4 || R(0x0e) == 5) { grabs++; hist[R(0xce)]++; continue; }
      if (R(0x1d) == 1 && R(0xce) >= 165 && R(0xce) <= 167 && (int8_t)R(0x9f) < 0) { band++; long xf = (R(0x6d) * 256L + R(0x86) - need) * 256 + R(0x400); if (xf > best) { best = xf; printf("  best at band frame: X-need %.4f y=%d vy=%d n=%d p=%d tap=%02X a=%02X b=%02X\n", xf / 256.0, R(0xce), (int8_t)R(0x9f), nn, p, TAP[tp], LR[a], LR[b]); } }
    }
    printf("fastjump f=%d pre=%d: %ld runs, band frames %ld, best X-need %.4f, grabs %ld by Y:", f, pre, runs, band, best / 256.0, grabs); for (int y = 0; y < 256; y++) if (hist[y]) printf(" %d:%d", y, hist[y]); printf("\n");
  }
  else if (!strcmp(c, "pitfuzz")) { // random legal inputs from the state after f: can Mario get into the floor at the pit's right wall (left point in wall)?
    int f = atoi(argv[4]), len = atoi(argv[5]); long trials = atol(argv[6]); int wall = atoi(argv[7]); rs ^= (uint64_t)atoi(argv[8]) * 0x100000001B3ULL; for (int i = 0; i < 8; i++) rnd();
    static const uint8_t MV[] = {0x80,0x80,0x82,0x40,0x42,0xC0,0x00,0x81,0x41,0x01,0xC1,0x00};
    long frames = 0, low = 0, in = 0, under = 0; int bestx = -1, besty = 0, bestin = -1, maxanyx = -1;
    static uint8_t in_path[512], best_path[512]; int best_len = 0;
    for (long t = 0; t < trials; t++) {
      static NES m; m = snap[f]; NES *n = &m; uint8_t b = 0x80; int period = 1 + rnd() % 6;
      for (int i = 0; i < len; i++) {
        if (rnd() % period == 0) b = MV[rnd() % 12];
        in_path[i] = b;
        checked_frame(n, b, 0); frames++;
        if (n->err || R(0x0e) != 8 || R(0xb5) != 1) break;
        int x = R(0x6d) * 256 + R(0x86), y = R(0xce);
        if (y >= 181 && x > maxanyx) maxanyx = x;
        if (y >= 181 && x >= wall + 16) under++;
        if (R(0x1d) == 0 && y >= 181) {
          low++;
          if (x > bestx) { bestx = x; besty = y; best_len = i + 1; memcpy(best_path, in_path, i + 1); printf("  on the ground below the surface: y=%d x=%d (wall-2 is %d, short by %d) vx=%d t=%ld\n", y, x, wall - 2, wall - 2 - x, (int8_t)R(0x57), t); fflush(stdout); }
          if (x >= wall - 2) { in++; if (x > bestin) bestin = x; }
        }
      }
    }
    printf("pitfuzz f=%d len=%d trials=%ld: %ld frames; on-ground frames below surface %ld, best X %d (y=%d), with left point in wall %ld; frames at Y>=181 past wall+16 %ld; max X at Y>=181 %d\n  inputs to best:", f, len, trials, frames, low, bestx, besty, in, under, maxanyx);
    for (int i = 0; i < best_len; i++) printf(" %02X", best_path[i]); printf("\n");
  }
  else if (!strcmp(c, "cannon")) { // any cannon Y set over a movie range?
    int ct = 0, f0 = atoi(argv[4]), f1 = atoi(argv[5]); for (int f = f0; f <= f1; f++) { NES *n = &snap[f]; for (int i = 0; i < 6; i++) if (R(0x477 + i)) ct++; }
    printf("frames %d..%d: cannon slots with Y set, slot-frames %d; world %d-%d\n", f0, f1, ct, snap[f1].ram[0x75f] + 1, snap[f1].ram[0x75c] + 1);
  }
  else if (!strcmp(c, "cantab")) { // cannon table and any Bullet Bills over a range, sampled
    int f0 = atoi(argv[4]), f1 = atoi(argv[5]), st = atoi(argv[6]);
    for (int f = f0; f <= f1; f += st) { NES *n = &snap[f]; printf("f%6d m=%2d:%3d cannons:", f, R(0x6d), R(0x86));
      for (int i = 0; i < 6; i++) if (R(0x477 + i)) printf(" [%d %d:%d y=%d t=%d]", i, R(0x46b + i), R(0x471 + i), R(0x477 + i), R(0x47d + i));
      printf(" | bills:"); for (int e = 0; e < 6; e++) if (R(0x0f + e) && (R(0x16 + e) == 0x33 || R(0x16 + e) == 8)) printf(" [%d %02X %d:%d y=%d vx=%d]", e, R(0x16 + e), R(0x6e + e), R(0x87 + e), R(0xcf + e), (int8_t)R(0x58 + e));
      printf("\n"); }
  }
  else if (!strcmp(c, "ingrid")) { // [edit] on the floor's second row at Y=192 inside the ground: A at frame t for h frames, holding R+B
    int f = atoi(argv[4]), x0 = atoi(argv[5]); int found = 0, runs = 0; static int ghist[256]; int vx = argc > 6 ? atoi(argv[6]) : 40, hold = argc > 7 ? strtol(argv[7], 0, 16) : 0x82;
    for (int x = x0; x < x0 + 16; x += 1) for (int t = 0; t < 16; t++) for (int h = 1; h <= 24; h++) {
      static NES m; m = snap[f]; NES *n = &m;
      R(0x6d) = x >> 8; R(0x86) = x & 255; R(0xce) = 192; R(0x1d) = 0; R(0x9f) = 0; R(0x433) = 0; R(0x416) = 0; R(0x57) = vx; R(0x700) = vx; R(0x45) = 1; R(0x33) = 1;
      int ys[40], k = 0, grabbed = 0; runs++;
      for (int i = 0; i < 40; i++) {
        checked_frame(n, hold | (i >= t && i < t + h ? 1 : 0), 0); ys[k++] = R(0xce);
        if (R(0x0e) != 8) { grabbed = R(0x0e) == 4 || R(0x0e) == 5; break; }
      }
      if (grabbed) ghist[R(0xce)]++;
      if (grabbed && R(0xce) >= 165 && R(0xce) <= 167 && found < 12) { found++; printf("x0=%d t=%d h=%d grab y=%d x=%d ges=%d vy=%d; last Ys:", x, t, h, R(0xce), R(0x86), R(0x0e), (int8_t)R(0x9f)); for (int i = k > 8 ? k - 8 : 0; i < k; i++) printf(" %d", ys[i]); printf("\n"); }
    }
    printf("ingrid: %d runs, %d shown; grab Y:", runs, found); for (int y = 0; y < 256; y++) if (ghist[y]) printf(" %d:%d", y, ghist[y]); printf("\n");
  }
  else if (!strcmp(c, "bfs")) cmd_bfs(atoi(argv[4]), atoi(argv[5]), atoi(argv[6]), atoi(argv[7]), atoi(argv[8]), argc > 9 ? atol(argv[9]) : 2000, argc > 10 ? atoi(argv[10]) : 0);
  return 0;
}
