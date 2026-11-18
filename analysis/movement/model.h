// Horizontal and vertical movement on flat ground, from the proved summaries of the player routines:
// `jumpRam`, `xphysRam`, `animRam`, `frictionRam`, `mphRam`, `gravityRam` and the landing path. No walls, enemies or blocks.
#pragma once
#include "../../emu/nes.h"
typedef uint8_t u8; typedef uint32_t u32; typedef uint16_t u16;
enum { B_R = 1, B_L = 2, B_B = 4, B_A = 8, B_O = 16, B_D = 32 };   // B_O: Up or Select, which only the skid check sees
typedef struct {
  u32 pos;              // $6D $86 $400
  u8 v, f, abs_;        // $57 $705 $700
  u8 face, move, st;    // $33 $45 $1D
  u8 t783, r703;
  u8 y, ysub, vy, vf;   // $CE $416 $9F $433
  u8 g, gfall;          // $709 $70A
  u8 y0, rise;          // $708 $706
  u8 prevA;             // $0D's A bit
  u8 area;              // $74E
  u8 ground;            // the Y it lands at, with no tile map
  u8 yh, coll, t784;    // $B5 $490 $784
  u8 evt;               // sticky: 1 side pipe taken, 2 a climbable tile touched (the pole), 3 down a pipe, 4 ran into the axe
} M;
// The block buffer as one map: a tile per column of 16 pixels, 13 rows. NULL means open ground at `ground`.
static const u8 *m_tiles = 0; static int m_cols = 0;
static inline u8 m_tile(u32 pos, int x_add, int y, int y_add) {
  int px = (int)(pos >> 8) + x_add; int row = (((y + y_add) & 0xF0) - 0x20) & 0xFF;
  if (row >= 0xD0 || px < 0) return 0;
  int col = px >> 4; if (col >= m_cols) return 0;
  return m_tiles[col * 13 + (row >> 4)];
}
// Collision probe offsets are loaded by nes_load_rom.
static const u8 *const XADD = PRG + (0xE3B0 - 0x8000);
static const u8 *const YADD = PRG + (0xE3CC - 0x8000);
static inline int tgroup(u8 t) { return t >> 6; }
static inline int m_solid(u8 t) { return t >= PRG[0xDF8B - 0x8000 + tgroup(t)]; }
static inline int m_climb(u8 t) { return t >= PRG[0xDF96 - 0x8000 + tgroup(t)]; }
static inline int m_coin(u8 t) { return t == 0xC2 || t == 0xC3; }
static inline void m_impede(M *s, int dir) {
  int cl = 0;
  if (dir == 1) { cl = 1; if (!(s->v & 0x80)) { s->t784 = s->t784; s->v = 0; s->pos = (s->pos - 0x100) & 0xFFFFFF; } }
  else { cl = 2; if ((s->v & 0x80) || s->v == 0) { s->v = 0; s->pos = (s->pos + 0x100) & 0xFFFFFF; } }
  s->coll &= ~cl;
}
// PlayerBGCollision, small Mario, without coins being taken or blocks changing.
static inline void m_collide(M *s, int in) {
  if (s->st == 0 || s->st == 3) s->st = 2;
  if (s->yh != 1) return;
  s->coll = 0xFF;
  if (s->y >= 0xCF) return;
  int eb = 0x0E;
  // head
  if (s->y >= 0x10) {
    u8 t = m_tile(s->pos, XADD[eb], s->y, YADD[eb]);
    if (t && !m_coin(t) && s->vy >= 0x80 && (s->y & 15) >= 4) {
      if (m_solid(t)) s->vy = 1;
      else if (s->t784) s->vy = 1;
      else { s->t784 = 0x10; s->vy = 0; }
    }
  }
  // feet
  int done = 0;
  if (s->y < 0xCF) {
    u8 l = m_tile(s->pos, XADD[eb + 1], s->y, YADD[eb + 1]), r = m_tile(s->pos, XADD[eb + 2], s->y, YADD[eb + 2]);
    u8 t = l ? l : r;
    if (m_coin(l) || (!l && m_coin(r))) t = 0;
    if (t && !m_climb(t) && s->vy < 0x80) {
      if (t == 0xC5) { s->evt = 4; return; }
      if (t != 0x5F && t != 0x60) {
        if ((s->y & 15) < 5) {
          s->y &= 0xF0;
          if ((in & B_D) && r == 0x11 && l == 0x10) s->evt = 3;
          s->vy = 0; s->vf = 0; s->st = 0; done = 1;
        } else { m_impede(s, s->move); return; }
      }
    }
  }
  (void)done;
  // sides: the left pair, then the right pair
  int idx = eb + 2;
  for (int dir = 2; dir >= 1; dir--) {
    idx++;
    u8 t = 0; int hit = 0;
    if (s->y < 0x20) { }
    else { if (s->y >= 0xE4) return; t = m_tile(s->pos, XADD[idx], s->y, YADD[idx]); if (t && t != 0x1C && t != 0x6B && !m_climb(t)) hit = 1; else if (t && m_climb(t)) hit = 1; }
    idx++;
    if (!hit) { if (s->y < 8) continue; if (s->y >= 0xD0) return; t = m_tile(s->pos, XADD[idx], s->y, YADD[idx]); if (t) hit = 1; }
    if (!hit) continue;
    if (t == 0x5F || t == 0x60) return;
    if (m_climb(t)) { int nib = (s->pos >> 8) & 15; if (nib >= 6 && nib < 10) s->evt = 2; return; }   // $DE30: the pole's thinner than its tile
    if (m_coin(t)) return;
    if (s->st == 0 && s->face == 1 && (t == 0x6C || t == 0x1F)) { s->evt = 1; }
    m_impede(s, dir);
    return;
  }
}
static inline int jc(u8 a) { return a < 9 ? 0 : a < 0x10 ? 1 : a < 0x19 ? 2 : a < 0x1C ? 3 : 4; }
static inline void m_step(M *s, int in) {
  u8 rawlr = (in & B_R ? 1 : 0) | (in & B_L ? 2 : 0), a = in & B_A ? 0x80 : 0, b = in & B_B ? 0x40 : 0;
  u8 lr = (in & B_D) && s->st == 0 ? 0 : rawlr;   // $B119: on the ground, Down cancels left and right
  if (s->t783) s->t783--;
  if (s->t784) s->t784--;
  // jump start
  if (a && !s->prevA && s->st == 0) {
    const u8 *up = PRG + (0xB424 - 0x8000);
    const u8 *dn = PRG + (0xB42B - 0x8000);
    const u8 *sp = PRG + (0xB432 - 0x8000);
    int c = jc(s->abs_); s->ysub = 0; s->vf = 0; s->g = up[c]; s->gfall = dn[c]; s->vy = sp[c]; s->st = 1; s->y0 = s->y; s->rise = 1;
  }
  // X_Physics
  int running = s->st == 0 ? (s->area != 0 && lr == s->move && (b || s->t783)) : 0x19 <= s->abs_;
  int cl = running ? 0 : 1; int fc = running ? 0 : (s->r703 || 0x21 <= s->abs_) ? 2 : 1;
  const u8 *flo = PRG + (0xB447 - 0x8000);
  const u8 *mr = PRG + (0xB443 - 0x8000);
  const u8 *ml = PRG + (0xB440 - 0x8000);
  if (s->st == 0 && s->area == 0) cl = running ? 0 : 2;
  u8 maxr = mr[cl], maxl = ml[cl]; u32 add = flo[fc]; if (s->face != s->move) add <<= 1;
  if (s->st == 0 && s->area != 0 && lr == s->move && b) s->t783 = 0x0A;
  // the state's routine
  if (s->st == 0) {
    u8 mask = rawlr | b | ((in & (B_O | B_D)) ? 0x20 : 0);   // $6FC & $7F, which leaves out A
    if (0x1C <= s->abs_) s->r703 = s->abs_;
    else if (mask && (mask & 3) == s->move) s->r703 = 0;
    else if (mask && s->abs_ < 0x0B) { s->move = s->face; s->v = 0; s->f = 0; }
    if (lr) s->face = lr;
  } else if (s->st == 1) {
    if (s->vy < 0x80 || !(a && s->prevA)) { if (s->vy < 0x80 || (u8)(s->y0 - s->y) >= s->rise) s->g = s->gfall; }
  } else s->g = s->gfall;
  // ImposeFriction: on the ground always, in the air only with a direction held
  if (s->st == 0 || lr) {
    u8 jl = m_tiles ? (lr & s->coll) : lr;
    int dir = jl ? ((jl & 1) ? 1 : 2) : s->v == 0 ? 0 : s->v < 0x80 ? 2 : 1;
    if (dir) {
      u8 lo = add & 255, hi = add >> 8; u8 raw; int clamp;
      if (dir == 1) { raw = s->v + hi + (s->f + lo > 255); clamp = !((u8)(raw - maxr) & 0x80); s->f += lo; }
      else { raw = s->v - hi - (s->f < lo); clamp = (u8)(raw - maxl) & 0x80; s->f -= lo; }
      s->v = clamp ? (dir == 1 ? maxr : maxl) : raw;
      s->abs_ = (dir == 1 && clamp) ? maxr : (s->v & 0x80) ? (u8)(0 - s->v) : s->v;
    } else s->abs_ = 0;
  }
  // MovePlayerHorizontally
  { int sv = (int8_t)s->v; s->pos = (s->pos + (u32)(sv * 16)) & 0xFFFFFF; }
  // $B141: the moving direction follows the speed's sign
  if (s->v) s->move = s->v < 0x80 ? 1 : 2;
  // ImposeGravity, then landing
  if (s->st != 0) {
    u32 yy = ((u32)s->yh << 16 | (u32)s->y << 8 | s->ysub) + (u32)(int)(((int8_t)s->vy) * 256 + s->vf); s->ysub = yy & 255; s->y = (yy >> 8) & 255; s->yh = (yy >> 16) & 255;
    u32 nv = ((u32)s->vy << 8 | s->vf) + s->g; s->vf = nv & 255; s->vy = (nv >> 8) & 255;
    if (!((u8)(s->vy - 4) & 0x80) && s->vf >= 0x80) { s->vy = 4; s->vf = 0; }
    if (!m_tiles && s->vy < 0x80 && s->y >= s->ground && (s->y & 15) < 5 && s->y < s->ground + 16) { s->y &= 0xF0; s->vy = 0; s->vf = 0; s->st = 0; }
  }
  s->prevA = a;
  if (m_tiles) m_collide(s, in);
}
