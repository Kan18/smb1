// Can anything beat a movie's position? From the state at frame START, over every input on open ground, is any position after T frames past the movie's?
// One frame per layer, best position per state. The state is everything in M but the position, so nothing's lost but states with the same future and less progress,
// and states that can't beat the target even at 640 per frame. usage: launch_dp ROM MOVIE START T [EVENT]: EVENT 1 side pipe, 2 pole: can it happen within T frames, rather than beat the movie's position
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include "model.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// With terrain a state's future depends on its position, so that's in the key, and only exact duplicates merge. On open ground (OPEN) more progress in the same state dominates.
static int open_ground = 0;
static inline void canon(M *t) { if (open_ground) t->pos = 0; t->ground = 0; }
static u32 hsh(const M *m) { M t; memset(&t, 0, sizeof t); t = *m; canon(&t); u32 h = 2166136261u; h = (h ^ t.pos) * 16777619u; u8 fs[] = {t.v, t.f, t.abs_, t.face, t.move, t.st, t.t783, t.r703, t.y, t.ysub, t.vy, t.vf, t.g, t.gfall, t.y0, t.rise, t.prevA, t.yh, t.coll, t.t784, t.evt}; for (unsigned i = 0; i < sizeof fs; i++) h = (h ^ fs[i]) * 16777619u; return h; }
static int same(const M *a, const M *b) { if (!open_ground && a->pos != b->pos) return 0; return a->v == b->v && a->f == b->f && a->abs_ == b->abs_ && a->face == b->face && a->move == b->move && a->st == b->st && a->t783 == b->t783 && a->r703 == b->r703 && a->y == b->y && a->ysub == b->ysub && a->vy == b->vy && a->vf == b->vf && a->g == b->g && a->gfall == b->gfall && a->y0 == b->y0 && a->rise == b->rise && a->prevA == b->prevA && a->yh == b->yh && a->coll == b->coll && a->t784 == b->t784 && a->evt == b->evt; }
typedef struct { int parent; u8 in; } Back; static Back *backs[8192];
static void load(M *m, const uint8_t *r) { memset(m, 0, sizeof *m); m->pos = (r[0x6D] << 16) | (r[0x86] << 8) | r[0x400]; m->v = r[0x57]; m->f = r[0x705]; m->abs_ = r[0x700]; m->face = r[0x33]; m->move = r[0x45]; m->st = r[0x1D]; m->t783 = r[0x783]; m->r703 = r[0x703]; m->y = r[0xCE]; m->ysub = r[0x416]; m->vy = r[0x9F]; m->vf = r[0x433]; m->g = r[0x709]; m->gfall = r[0x70A]; m->y0 = r[0x708]; m->rise = r[0x706]; m->area = r[0x74E]; }
enum { MAXN = 1 << 24, TAB = 1 << 26 };
static u8 MAP[4096 * 13]; static u8 SEEN[4096];
static u8 bufcell(const uint8_t *r, int col, int row) { int base = (col & 16) ? 0x5D0 : 0x500; return r[base + (col & 15) + row * 16]; }
static void see(const uint8_t *r) { int left = (r[0x71A] * 256 + r[0x71C]) >> 4; for (int c = left; c < left + 17; c++) { if (c >= 4096 || SEEN[c]) continue; SEEN[c] = 1; for (int row = 0; row < 13; row++) MAP[c * 13 + row] = bufcell(r, c, row); } }
int main(int c, char **v) {
  if (c < 5 || nes_load_rom(v[1])) return 2; Movie mv; char err[128]; if (movie_load(v[2], &mv, err) || movie_align(&mv, err)) { puts(err); return 2; }
  int start = atoi(v[3]), T = atoi(v[4]); int event = c > 5 ? atoi(v[5]) : 0; int ground = 176;
  static NES n; nes_power(&n); nes_reset(&n); M s; static u32 tp[4096]; static u8 tsp[4096]; int area0 = -1;
  for (int f = 0; f <= start + T && f < mv.n; f++) { nes_frame(&n, mv.p1[f], mv.p2[f]); if (f == start) { load(&s, n.ram); s.prevA = (mv.p1[f] & 1) ? 0x80 : 0; s.ground = ground; s.yh = n.ram[0xB5]; s.coll = n.ram[0x490]; s.t784 = n.ram[0x784]; printf("start: x %d.%02x v %d.%02x face %u move %u st %u y %u vy %d area %u engine %u\n", s.pos >> 8, s.pos & 255, (int8_t)s.v, s.f, s.face, s.move, s.st, s.y, (int8_t)s.vy, s.area, n.ram[0xE]); } if (f >= start && n.ram[0xE7] == area0) see(n.ram); if (f == start) area0 = n.ram[0xE7], see(n.ram); if (f >= start) { tp[f - start] = (n.ram[0x6D] << 16) | (n.ram[0x86] << 8) | n.ram[0x400]; tsp[f - start] = n.ram[0x57]; } }
  u32 goal = tp[T]; if (getenv("OPEN")) { open_ground = 1; m_tiles = 0; } else { m_tiles = MAP; m_cols = 4096; }
  // for an event: the nearest position that could touch its tile, by the right-hand probe at +$0D
  u32 need = 0; if (event) { int col0 = (s.pos >> 8) >> 4, found = -1; for (int cc = col0; cc < 4096 && found < 0; cc++) for (int row = 0; row < 13; row++) { u8 t = MAP[cc * 13 + row]; if (event == 1 ? (t == 0x6C || t == 0x1F) : m_climb(t) && t < 0x28) { found = cc; break; } } if (found < 0) { puts("no such tile on the map"); return 2; } need = (u32)(found * 16 - 0x0D) << 8; printf("event %d needs x >= %u (column %d)\n", event, need >> 8, found); }
  int hit = -1;
  // the movie's own inputs have to survive in this model, or the search means nothing
  { M t = s; static NES r; nes_power(&r); nes_reset(&r); for (int f = 0; f <= start; f++) nes_frame(&r, mv.p1[f], mv.p2[f]);
    for (int f = 1; f <= T + 3 && start + f < mv.n; f++) { u8 p = mv.p1[start + f]; int in = ((p & 0x80) ? B_R : 0) | ((p & 0x40) ? B_L : 0) | ((p & 2) ? B_B : 0) | ((p & 1) ? B_A : 0) | ((p & 0x20) ? B_D : 0) | ((p & 0x10) ? B_O : 0);
      nes_frame(&r, p, mv.p2[start + f]); m_step(&t, in); u32 rp = (r.ram[0x6D] << 16) | (r.ram[0x86] << 8) | r.ram[0x400];
      if (t.evt) { printf("movie's inputs: event %d in the model after %d frames; real engine %u st %u x %u\n", t.evt, f, r.ram[0xE], r.ram[0x1D], rp >> 8); break; }
      if (t.pos != rp || t.y != r.ram[0xCE] || t.v != r.ram[0x57]) { printf("movie's inputs leave the model after %d frames: model x %u.%02x y %u v %d st %u, real x %u.%02x y %u v %d st %u coll %02x/%02x evt %d\n", f, t.pos >> 8, t.pos & 255, t.y, (int8_t)t.v, t.st, rp >> 8, rp & 255, r.ram[0xCE], (int8_t)r.ram[0x57], r.ram[0x1D], t.coll, r.ram[0x490], t.evt); break; } } }
  M *cur = malloc(MAXN * sizeof(M)), *nxt = malloc(MAXN * sizeof(M)); static Back nb[MAXN]; int cnt = 1; int *tab = calloc(TAB, sizeof(int)), *stamp = calloc(TAB, sizeof(int)); cur[0] = s;
  for (int f = 1; f <= T; f++) {
    int k = 0;
    for (int i = 0; i < cnt; i++) for (int in = 0; in < 64; in++) {
      if ((in & B_O) && (in & B_D)) continue;
      M m = cur[i]; m_step(&m, in);
      if (m.pos >= 0x800000) continue;
      if (event) { if (m.evt == event) { hit = f; goto done; } if (m.evt) continue; if (m.pos + 640u * (u32)(T - f) < need) continue; }
      else if (m.pos + 640u * (u32)(T - f) <= goal) continue;   // can't beat the target even at full speed
      u32 h = hsh(&m) & (TAB - 1);
      for (;;) {
        if (stamp[h] != f) { stamp[h] = f; tab[h] = k; if (k >= MAXN) { puts("too many states"); return 1; } nb[k] = (Back){i, (u8)in}; nxt[k++] = m; break; }
        M *e = &nxt[tab[h]];
        if (same(e, &m)) { if (m.pos > e->pos) { e->pos = m.pos; nb[tab[h]] = (Back){i, (u8)in}; } break; }
        h = (h + 1) & (TAB - 1);
      }
    }
    { static M ts; static int alive = 1; if (f == 1) ts = s; if (alive) { u8 p = mv.p1[start + f]; int in = ((p & 0x80) ? B_R : 0) | ((p & 0x40) ? B_L : 0) | ((p & 2) ? B_B : 0) | ((p & 1) ? B_A : 0) | ((p & 0x20) ? B_D : 0) | ((p & 0x10) ? B_O : 0); m_step(&ts, in); int found = 0; for (int i = 0; i < k; i++) if (same(&nxt[i], &ts) && nxt[i].pos >= ts.pos) { found = 1; break; } if (!found) { alive = 0; printf("the movie's own state is missing at layer %d: x %u.%02x y %u v %d st %u evt %u; pos test %u need %u; in=%x\n", f, ts.pos >> 8, ts.pos & 255, ts.y, (int8_t)ts.v, ts.st, ts.evt, ts.pos + 640u * (u32)(T - f), need, in); } } }
    if (T <= 60 && !event) { backs[f] = malloc((k + 1) * sizeof(Back)); memcpy(backs[f], nb, k * sizeof(Back)); } M *t = cur; cur = nxt; nxt = t; cnt = k; u32 best = 0; for (int i = 0; i < cnt; i++) if (cur[i].pos > best) best = cur[i].pos;
    if (f % 4 == 0 || f == T || !cnt) { printf("%3d: %7d states; best %4u.%02x, movie %4u.%02x speed %d\n", f, cnt, best >> 8, best & 255, tp[f] >> 8, tp[f] & 255, (int8_t)tsp[f]); fflush(stdout); }
    if (!cnt) break;
  }
  done:
  if (event) { if (hit >= 0) printf("event %d reached after %d frames\n", event, hit); else printf("event %d NOT reachable within %d frames: %d states left\n", event, T, cnt); return 0; }
  printf("after %d frames from %d: %s the movie's %u.%02x\n", T, start, cnt ? "CAN beat" : "nothing beats", goal >> 8, goal & 255);
  if (cnt && T <= 60) { int bi = 0; for (int i = 0; i < cnt; i++) if (cur[i].pos > cur[bi].pos) bi = i; static u8 seq[8192]; int i = bi; for (int f = T; f >= 1; f--) { seq[f] = backs[f][i].in; i = backs[f][i].parent; }
    // replay those inputs on the real game
    static NES r; nes_power(&r); nes_reset(&r); for (int f = 0; f <= start; f++) nes_frame(&r, mv.p1[f], mv.p2[f]); M chk = s; printf("best inputs and the real game (model x / real x, y):\n");
    static const u8 MK[6] = {0x80, 0x40, 0x02, 0x01, 0x10, 0x20};
    for (int f = 1; f <= T; f++) { u8 in = 0; for (int b = 0; b < 6; b++) if (seq[f] >> b & 1) in |= MK[b]; nes_frame(&r, in, 0); m_step(&chk, seq[f]); char t[7] = "......"; for (int b = 0; b < 6; b++) if (seq[f] >> b & 1) t[b] = "RLBAUD"[b]; int rp = (r.ram[0x6D] << 16) | (r.ram[0x86] << 8) | r.ram[0x400]; if (f <= 6 || f % 4 == 0 || (u32)rp != chk.pos) printf(" %3d %s model %u.%02x y=%u st=%u v=%d | real %u.%02x y=%u st=%u v=%d %s\n", f, t, chk.pos >> 8, chk.pos & 255, chk.y, chk.st, (int8_t)chk.v, rp >> 8, rp & 255, r.ram[0xCE], r.ram[0x1D], (int8_t)r.ram[0x57], (u32)rp == chk.pos ? "" : "DIFF"); } }
  return 0;
}
