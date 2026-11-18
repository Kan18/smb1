// Can an event happen within T frames, from a movie's frame, over every input, with real terrain?
// One frame per layer. A state keeps every cell exact but two fractions, the low bytes of position and speed, which are ranges: states differing only there merge.
// Branches only look at exact cells, and a range splits where a carry would change one, so a merged state covers all it replaces: "unreachable" here is sound.
// usage: range_dp ROM MOVIE START T EVENT [MINY]: MINY counts the event only at that Y or lower on the screen
// env: NEEDBY N, the event's threshold must be reached N frames before the end. BOUNCE "XLO XHI", allow a stomp's bounce there.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include "model.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { M m; u8 plo, phi, flo, fhi; } R;
static inline u32 hsh(const M *t) { u32 h = 2166136261u; h = (h ^ (t->pos >> 8)) * 16777619u; u8 fs[] = {t->v, t->abs_, t->face, t->move, t->st, t->t783, t->r703, t->y, t->ysub, t->vy, t->vf, t->g, t->gfall, t->y0, t->rise, t->prevA, t->yh, t->coll, t->t784}; for (unsigned i = 0; i < sizeof fs; i++) h = (h ^ fs[i]) * 16777619u; return h; }
static inline int same(const M *a, const M *b) { return (a->pos >> 8) == (b->pos >> 8) && a->v == b->v && a->abs_ == b->abs_ && a->face == b->face && a->move == b->move && a->st == b->st && a->t783 == b->t783 && a->r703 == b->r703 && a->y == b->y && a->ysub == b->ysub && a->vy == b->vy && a->vf == b->vf && a->g == b->g && a->gfall == b->gfall && a->y0 == b->y0 && a->rise == b->rise && a->prevA == b->prevA && a->yh == b->yh && a->coll == b->coll && a->t784 == b->t784; }
static u8 MAP[4096 * 13]; static u8 SEEN[4096];
static u8 bufcell(const uint8_t *r, int col, int row) { int base = (col & 16) ? 0x5D0 : 0x500; return r[base + (col & 15) + row * 16]; }
static void see(const uint8_t *r) { int left = (r[0x71A] * 256 + r[0x71C]) >> 4; for (int c = left; c < left + 17; c++) { if (c >= 4096 || SEEN[c]) continue; SEEN[c] = 1; for (int row = 0; row < 13; row++) MAP[c * 13 + row] = bufcell(r, c, row); } }
enum { MAXN = 1 << 23, TAB = 1 << 25 };
static R *nxt; static int k; static int *tab, *stamp; static int layer; static int hit; static int needby; static int miny; static int event; static u32 need; static int T; static int fl;
// Cells nothing can read any more. A held A only matters on the way up: on the way down it's free to let go, so a landing needn't be counted as held.
static inline void norm(M *m) {
  int rising = m->st == 1 && m->vy >= 0x80;
  if (!rising) { m->y0 = 0; m->rise = 0; m->g = 0; m->prevA = 0; }
}
// A lower bound on the frames left to reach `Y` 176, for an event that has to be on the floor. It falls from the
// current height at a speed no real continuation can beat on any frame: rising, a head bump sets the speed's whole
// byte to 1 but keeps its fraction, so at most 1.FF at once; each frame adds the strongest gravity; and the game's
// clamp (4.80 and up becomes 4.00) never leaves a speed above 4.7F, so capping there bounds every clamped speed too.
static inline int to_floor(const M *m) {
  if (m->yh != 1) return 0;
  if (m->st == 0 && m->y >= 176) return 0;
  u32 yy = (u32)m->y << 8 | m->ysub; u32 v = m->vy >= 0x80 ? 0x1FF : (u32)m->vy << 8 | m->vf; u32 g = m->g > m->gfall ? m->g : m->gfall; int k = 0;
  if (v > 0x47F) v = 0x47F;
  while ((yy >> 8) < 176 && k < 200) { yy += v; v += g; if (v > 0x47F) v = 0x47F; k++; }
  return k;
}
static u32 ramp[256][512];   // the most a speed can cover in n frames
static u32 bxlo, bxhi;   // BOUNCE: while falling at these X, near a floor enemy's height, a stomp may set the speed ($D9B0, $D9F3)
static void add(const M *m0, int f) {
  if (event && m0->evt == event && m0->y >= miny) { hit = 1; return; }
  if (m0->evt) return;
  if (bxhi && m0->st != 0 && m0->vy < 0x80 && m0->y >= 140 && m0->y < 184 && (m0->pos >> 8) >= bxlo && (m0->pos >> 8) <= bxhi) {
    for (int w = 0; w < 2; w++) { M b = *m0; b.vy = w ? 0xFC : 0xFD; b.g = b.gfall; add(&b, f); }
  }
  M mm = *m0; const M *m = &mm; norm(&mm);
  if ((m->pos | 0xFF) + ramp[m->v][T - f] < need) return;
  // NEEDBY: the threshold has to be reached that many frames before the end.
  if (needby && (m->pos | 0xFF) < need && (T - f < needby || (m->pos | 0xFF) + ramp[m->v][T - f - needby] < need)) return;
  if (event == 1 && to_floor(m) > T - f) return;
  u32 h = hsh(m) & (TAB - 1); u8 p = m->pos & 255, q = m->f;
  for (;;) {
    if (stamp[h] != layer) { stamp[h] = layer; tab[h] = k; if (k >= MAXN) { puts("too many states"); exit(1); } nxt[k] = (R){*m, p, p, q, q}; k++; return; }
    R *e = &nxt[tab[h]];
    if (same(&e->m, m)) { if (p < e->plo) e->plo = p; if (p > e->phi) e->phi = p; if (q < e->flo) e->flo = q; if (q > e->fhi) e->fhi = q; return; }
    h = (h + 1) & (TAB - 1);
  }
}
// Step one point.
static inline M at(const M *base, int p, int q, int in) { M a = *base; a.pos = (a.pos & ~255u) | p; a.f = q; m_step(&a, in); return a; }
static inline int agree(const M *x, const M *y) { return same(x, y) && x->evt == y->evt; }
// A rectangle of fractions, split until its four corners agree. Then the whole of it agrees: within a branch each fraction moves by a constant, the speed's carry is monotonic in its fraction, and given the speed the position's is monotonic in its own. A wrap of a fraction is a carry a clamp might hide, so it splits too.
static void rect(const M *base, int p0, int p1, int q0, int q1, int in, int f) {
  M a = at(base, p0, q0, in);
  if (p0 == p1 && q0 == q1) { add(&a, f); return; }
  M b = at(base, p1, q1, in), c = at(base, p0, q1, in), d = at(base, p1, q0, in);
  if (agree(&a, &b) && agree(&a, &c) && agree(&a, &d) && c.f >= a.f && b.f >= d.f && (d.pos & 255) >= (a.pos & 255) && (b.pos & 255) >= (c.pos & 255)) { add(&a, f); add(&b, f); add(&c, f); add(&d, f); return; }
  // Only some fractions occur: a position moves in 16ths, a speed's fraction by friction steps, all multiples of 4.
  if (p1 - p0 >= (q1 - q0) * 4 && p1 > p0) { int m = p0 + (((p1 - p0) / 2) & ~15); rect(base, p0, m, q0, q1, in, f); rect(base, m + 16, p1, q0, q1, in, f); }
  else { int m = q0 + (((q1 - q0) / 2) & ~3); rect(base, p0, p1, q0, m, in, f); rect(base, p0, p1, m + 4, q1, in, f); }
}
int main(int c, char **v) {
  if (c < 6 || nes_load_rom(v[1])) return 2; Movie mv; char err[128]; if (movie_load(v[2], &mv, err) || movie_align(&mv, err)) { puts(err); return 2; }
  int start = atoi(v[3]); T = atoi(v[4]); event = atoi(v[5]); if (c > 6) miny = atoi(v[6]); if (getenv("NEEDBY")) needby = atoi(getenv("NEEDBY")); if (getenv("BOUNCE")) sscanf(getenv("BOUNCE"), "%u %u", &bxlo, &bxhi); static NES n; nes_power(&n); nes_reset(&n); M s; int area0 = -1;
  for (int f = 0; f <= start + T + 2 && f < mv.n; f++) { nes_frame(&n, mv.p1[f], mv.p2[f]); const uint8_t *r = n.ram; if (f == start) { area0 = r[0xE7]; see(r); memset(&s, 0, sizeof s); s.pos = (r[0x6D] << 16) | (r[0x86] << 8) | r[0x400]; s.v = r[0x57]; s.f = r[0x705]; s.abs_ = r[0x700]; s.face = r[0x33]; s.move = r[0x45]; s.st = r[0x1D]; s.t783 = r[0x783]; s.r703 = r[0x703]; s.y = r[0xCE]; s.ysub = r[0x416]; s.vy = r[0x9F]; s.vf = r[0x433]; s.g = r[0x709]; s.gfall = r[0x70A]; s.y0 = r[0x708]; s.rise = r[0x706]; s.area = r[0x74E]; s.yh = r[0xB5]; s.coll = r[0x490]; s.t784 = r[0x784]; s.prevA = (mv.p1[f] & 1) ? 0x80 : 0; s.ground = 176; } else if (f > start && r[0xE7] == area0) see(r); }
  m_tiles = MAP; m_cols = 4096;
  int col0 = (s.pos >> 8) >> 4, found = -1; for (int cc = col0; cc < 4096 && found < 0; cc++) for (int row = 0; row < 13; row++) { u8 t = MAP[cc * 13 + row]; if (event == 1 ? (t == 0x6C || t == 0x1F) : (t == 0x24 || t == 0x25)) { found = cc; break; } }
  if (found < 0) { puts("no such tile on the map"); return 2; } need = (u32)(found * 16 - 0x0D) << 8;
  if (getenv("FSET")) s.f = atoi(getenv("FSET"));   // try another speed fraction
  printf("start: x %u y %u st %u; event %d needs x >= %u\n", s.pos >> 8, s.y, s.st, event, need >> 8);
  // A frame's gain: the speed rises at most 2, but the skid check can zero a small negative speed first, so a negative speed counts as 0; and a wall can push Mario a pixel at speed 0 or less.
  for (int w = 0; w < 256; w++) for (int n = 0; n <= T; n++) { int sv = (int8_t)w; u32 tot = 0; int c = sv > 0 ? sv : 0; for (int q = 0; q < n; q++) { c += 2; if (c > 40) c = 40; u32 g = (u32)c * 16; tot += g > 256 ? g : 256; } ramp[w][n] = tot; }
  R *cur = malloc(MAXN * sizeof(R)); nxt = malloc(MAXN * sizeof(R)); tab = calloc(TAB, sizeof(int)); stamp = calloc(TAB, sizeof(int));
  cur[0] = (R){s, s.pos & 255, s.pos & 255, s.f, s.f}; int cnt = 1; M ts = s;
  // POLE: start from every state in which Mario has just entered the pole's column, X having reached 3155 on this frame, however he got there. What constrains it:
  // at Y >= 165 the base is a wall, so he's been stopped (v = 0) and may have been pushed; falling into Y 160-164 with a foot over the base has landed; on the floor or the base he's stopped;
  // rising can only be from a jump off the floor, since nothing else is near, so its (Y, speed) come from simulating those jumps.
  if (getenv("POLE")) {
    cnt = 0;
    static struct { u8 y, ysub, vy, vf, g, gfall; } UP[4096]; int nup = 0;
    { const u8 *t0 = m_tiles; m_tiles = 0; for (int c = 0; c < 5; c++) for (int h = 0; h < 24; h++) { M m; memset(&m, 0, sizeof m); static const u8 AB[5] = {0, 9, 16, 25, 28}; m.abs_ = AB[c]; m.v = AB[c]; m.face = m.move = 1; m.y = 176; m.ground = 176; m.area = 1; m.yh = 1;
        for (int k = 0; k < 40; k++) { m_step(&m, (k <= h ? B_A : 0)); if (m.st == 0 || m.vy < 0x80) break; int dup = 0; for (int q = 0; q < nup; q++) if (UP[q].y == m.y && UP[q].ysub == m.ysub && UP[q].vy == m.vy && UP[q].vf == m.vf && UP[q].g == m.g && UP[q].gfall == m.gfall) dup = 1; if (!dup && nup < 4096) { UP[nup].y = m.y; UP[nup].ysub = m.ysub; UP[nup].vy = m.vy; UP[nup].vf = m.vf; UP[nup].g = m.g; UP[nup].gfall = m.gfall; nup++; } } }
      m_tiles = t0; }
    printf("%d rising states off the floor\n", nup);
    static const u8 GF[] = {0x28, 0x60, 0x70, 0x90};
    for (int v = 0; v <= 40; v++) for (int px = 0; px < 3; px++) {
      // POLE=2: arriving on the earliest frame, X is limited by exit_crossing: at most 3156.5625 moving, or a pixel less pushed back
      int lim = v ? v : 24; if (atoi(getenv("POLE")) == 2) { int top = v ? 26 : 10; if (lim > top) lim = top; }
      int lo = px * 16; if (lo >= lim) continue; int hi = lim - 1 < lo + 15 ? lim - 1 : lo + 15;
      u32 pos = (3155u + px) << 8;
#define START(Y, YSUB, VY, VF, G, GFALL, ST, F, MV, CL, R7) for (int ia = 0; ia < (v ? 1 : 7); ia++) do { static const u8 ABS0[7] = {0, 10, 16, 25, 28, 33, 40}; M m = s; m.pos = pos; m.v = v; m.abs_ = v ? v : ABS0[ia]; m.y = (Y); m.ysub = (YSUB); m.vy = (VY); m.vf = (VF); m.st = (ST); m.face = (F); m.move = (MV); m.gfall = (GFALL); m.g = (G); m.r703 = (R7); m.t783 = 0; m.y0 = 176; m.rise = 1; m.prevA = 0; m.coll = (CL); m.yh = 1; m.t784 = 0; m.evt = 0; if (cnt >= MAXN) { puts("too many starts"); return 1; } cur[cnt++] = (R){m, (u8)((lo - px * 16) * 16), (u8)((hi - px * 16) * 16), 0, 0xFC}; } while (0)
      static const u8 CL[3] = {0xFF, 0xFE, 0xFD};
      for (int face = 1; face <= 3; face++) for (int r7 = 0; r7 < 2; r7++) for (int icl = 0; icl < (v ? 1 : 3); icl++) for (int mv = 1; mv <= (v ? 1 : 2); mv++) {
        for (int q = 0; q < nup; q++) if (UP[q].y <= 164 || v == 0) START(UP[q].y, UP[q].ysub, UP[q].vy, UP[q].vf, UP[q].g, UP[q].gfall, 1, face, mv, CL[icl], r7 ? 1 : 0);
        for (int y = 150; y <= 176; y++) { if (y >= 165 && v) continue; if (y >= 160 && y <= 164 && px > 0) continue;
          for (int vy = 0; vy <= 4; vy++) for (int vf = 0; vf < 256; vf += 128) for (unsigned ig = 0; ig < sizeof GF; ig++) for (int st = 1; st <= 2; st++) START(y, 0, vy, vf, GF[ig], GF[ig], st, face, mv, CL[icl], r7 ? 1 : 0); }
        if (v == 0) { START(176, 0, 0, 0, 0x90, 0x90, 0, face, mv, CL[icl], r7 ? 1 : 0); }
      }
    }
    printf("%d starts\n", cnt);
  }
  for (int f = 1; f <= T; f++) {
    k = 0; layer = f; hit = 0;
    for (int i = 0; i < cnt; i++) for (int in = 0; in < 64; in++) {
      if ((in & B_O) && (in & B_D)) continue;
      if (cur[i].m.st != 0 && (in & (B_B | B_O | B_D))) continue;   // in the air only left, right and A do anything
      rect(&cur[i].m, cur[i].plo, cur[i].phi, cur[i].flo, cur[i].fhi, in, f);
    }
    { u8 p = mv.p1[start + f]; int in = ((p & 0x80) ? B_R : 0) | ((p & 0x40) ? B_L : 0) | ((p & 2) ? B_B : 0) | ((p & 1) ? B_A : 0) | ((p & 0x20) ? B_D : 0) | ((p & 0x10) ? B_O : 0); m_step(&ts, in); }
    { M tn = ts; norm(&tn); int found2 = ts.evt != 0; for (int i = 0; i < k && !found2; i++) if (same(&nxt[i].m, &tn) && (ts.pos & 255) >= nxt[i].plo && (ts.pos & 255) <= nxt[i].phi && ts.f >= nxt[i].flo && ts.f <= nxt[i].fhi) found2 = 1; if (!found2) { static int told = 0; if (told++ < 1) { printf("  the movie's own state isn't covered at layer %d: x %u.%02x v %d.%02x abs %u face %u move %u st %u y %u.%02x vy %02x.%02x g %02x/%02x y0 %u rise %u prevA %02x yh %u coll %02x t783 %u r703 %u t784 %u\n", f, ts.pos >> 8, ts.pos & 255, (int8_t)ts.v, ts.f, ts.abs_, ts.face, ts.move, ts.st, ts.y, ts.ysub, ts.vy, ts.vf, ts.g, ts.gfall, ts.y0, ts.rise, ts.prevA, ts.yh, ts.coll, ts.t783, ts.r703, ts.t784); for (int i = 0, nn = 0; i < k && nn < 3; i++) if (same(&nxt[i].m, &tn)) { printf("    same key: frac %02x-%02x, f %02x-%02x\n", nxt[i].plo, nxt[i].phi, nxt[i].flo, nxt[i].fhi); nn++; } } } }
    R *t = cur; cur = nxt; nxt = t; cnt = k; u32 best = 0; for (int i = 0; i < cnt; i++) { u32 x = (cur[i].m.pos & ~255u) | cur[i].phi; if (x > best) best = x; }
    if (f % 8 == 0 || hit || !cnt || f == T) { printf("%3d: %8d states, best x %4u.%02x\n", f, cnt, best >> 8, best & 255); fflush(stdout); }
    if (hit) { printf("event %d reachable after %d frames\n", event, f); return 0; }
    if (!cnt) break;
  }
  printf("event %d NOT reachable within %d frames\n", event, T); return 0;
}
