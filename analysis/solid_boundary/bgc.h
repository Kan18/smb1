// PlayerBGCollision ($DC64) as a decision table, plus shared helpers.
// verify.c prints the table's predictions alongside traces from the NES model.
#ifndef BGC_H
#define BGC_H
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// RAM
enum {
  rGE = 0x0E, rState = 0x1D, rFacing = 0x33, rMovDir = 0x45, rXSp = 0x57, rPage = 0x6D, rX = 0x86,
  rYSp = 0x9F, rHigh = 0xB5, rY = 0xCE, rUpDown = 0x0B, rLR = 0x0C, rAB = 0x0A, rPrevAB = 0x0D,
  rEB = 0xEB, rXForce = 0x0705, rYForce = 0x0433, rYSub = 0x0416, rColl = 0x0490, rSwim = 0x0704,
  rJsAnim = 0x070E, rCrouch = 0x0714, rDisable = 0x0716, rArea = 0x074E, rSize = 0x0754,
  rBounce = 0x0784, rSideT = 0x0785, rScrL = 0x071C, rScrLP = 0x071A, rScrR = 0x071D, rScrRP = 0x071B,
  rOperMode = 0x770, rTask = 0x772, rScrollLock = 0x723, rTimerCtl = 0x747, rChangeArea = 0x6DE,
  rWorld = 0x75F, rLevel = 0x75C, rAreaNum = 0x760, rAreaPtr = 0x750, rStar = 0x79F, rInjury = 0x79E,
  rVForce = 0x709, rVForceDown = 0x70A, rClimbT = 0x789, rSprAttr = 0x3C4
};

// ROM entry addresses
enum {
  pcBG = 0xDC64, pcExit = 0xDC97, pcHeadChk = 0xDCBA, pcNY = 0xDCF2, pcFoot = 0xDCF6, pcCoin = 0xDD1A,
  pcFootM = 0xDD1D, pcLand = 0xDD44, pcInitSt = 0xDD5A, pcSide = 0xDD5E, pcExSCH = 0xDD9B,
  pcCSM = 0xDD9C, pcPipe = 0xDDCE, pcSideCoin = 0xDE05, pcAxe = 0xDE0E, pcClimb = 0xDE2E,
  pcPutVine = 0xDE88, pcImpede = 0xDF4B, pcNXSpd = 0xDF66, pcExIPM = 0xDF81, pcHeadColl = 0xBCED
};

static const uint8_t *const bbXAdd = PRG + (0xE3B0 - 0x8000);
static const uint8_t *const bbYAdd = PRG + (0xE3CC - 0x8000);

static inline uint16_t bb_addr(const uint8_t *ram, int idx) {
  unsigned sx = ram[rX] + bbXAdd[idx];
  unsigned pg = (ram[rPage] + (sx >> 8)) & 1;
  unsigned col = (sx & 0xFF) >> 4;
  uint8_t off = (uint8_t)(((ram[rY] + bbYAdd[idx]) & 0xF0) - 0x20);
  return (uint16_t)((pg ? 0x5D0 : 0x500) + col + off);
}
static inline uint8_t bb_tile(const uint8_t *ram, int idx) { return ram[bb_addr(ram, idx) & 0x7FF]; }

static inline int t_coin(uint8_t t) { return t == 0xC2 || t == 0xC3; }
static inline int t_hidden(uint8_t t) { return t == 0x5F || t == 0x60; }
static inline int t_climb(uint8_t t) { return t >= PRG[0xDF96 - 0x8000 + (t >> 6)]; }
static inline int t_headsolid(uint8_t t) { return t >= PRG[0xDF8B - 0x8000 + (t >> 6)]; }
static inline int t_spring(uint8_t t) { return t == 0x67 || t == 0x68; }
// What a falling Mario can land on (reaches LandPlyr's window test at ChkFootMTile).
static inline int t_footsolid(uint8_t t) { return t && !t_coin(t) && !t_climb(t) && !t_hidden(t) && t != 0xC5; }
// What stops a side probe when reached at CheckSideMTiles (pipe mouth treated as solid).
static inline int t_sidesolid(uint8_t t) { return t && !t_coin(t) && !t_climb(t) && !t_hidden(t); }

// Which probe set: 0 big, 7 big swimming, 14 small or crouching.
static inline int bgc_eb(const uint8_t *ram) {
  if (ram[rCrouch] || ram[rSize]) return 14;
  return ram[rSwim] ? 7 : 0;
}

enum {
  L_GATE = 1, L_HCOIN = 2, L_NY = 4, L_HIT = 8, L_FCOIN = 0x10, L_AXE = 0x20, L_LAND = 0x40, L_JS = 0x80,
  L_FAILLAND = 0x100, L_SCOIN = 0x200, L_CLIMB = 0x400, L_PIPE = 0x800, L_SIDEPUSH = 0x1000,
  L_SIDEFREE = 0x2000, L_SIDEHID = 0x4000, L_SIDESPR = 0x8000, L_NOHIT = 0x10000, L_SPUSHFREE = 0x20000
};
typedef struct {
  uint32_t leaf;
  uint8_t y, ysp, yforce, state, x, page, xsp, coll, sideT, ge;
} Out;

static inline void out_from_ram(Out *o, const uint8_t *r) {
  o->leaf = 0; o->y = r[rY]; o->ysp = r[rYSp]; o->yforce = r[rYForce]; o->state = r[rState]; o->x = r[rX];
  o->page = r[rPage]; o->xsp = r[rXSp]; o->coll = r[rColl]; o->sideT = r[rSideT]; o->ge = r[rGE];
}

// $00 = dir: 1 is the left-side code path (push -1), anything else the right-side path (push +1).
static inline int bgc_impede(Out *o, uint8_t dir) {
  int xbit, a;
  if (dir == 1) {
    xbit = 1;
    if (o->xsp & 0x80) { o->coll &= (uint8_t)~xbit; return 0; }
    a = -1;
  } else {
    xbit = 2;
    if (!((uint8_t)(o->xsp - 1) & 0x80)) { o->coll &= (uint8_t)~xbit; return 0; }
    a = 1;
  }
  o->sideT = 0x10; o->xsp = 0;
  unsigned v = (o->page << 8 | o->x) + a;
  o->x = v & 0xFF; o->page = (v >> 8) & 0xFF;
  o->coll &= (uint8_t)~xbit;
  return 1;
}

// `after_head` (optional) is the RAM at DoFootCheck when PlayerHeadCollision ran: that routine changes
// the speed and the block buffer, and it is treated as a black box here.
static inline Out bgc_predict(const uint8_t *r, const uint8_t *after_head) {
  Out o; out_from_ram(&o, r);
  if (r[rDisable] || r[rGE] == 0x0B || r[rGE] < 4) { o.leaf = L_GATE; return o; }
  if (r[rSwim]) o.state = 1;
  else if (r[rState] == 0 || r[rState] == 3) o.state = 2;
  if (r[rHigh] != 1) { o.leaf = L_GATE; return o; }
  o.coll = 0xFF;
  if (r[rY] >= 0xCF) { o.leaf = L_GATE; return o; }
  int eb = bgc_eb(r);
  const uint8_t *ext = PRG + (0xDC62 - 0x8000);
  uint8_t low = r[rY] & 0x0F;
  const uint8_t *m = r;
  if (r[rY] >= ext[(r[rSize] != 0) + (r[rCrouch] != 0)]) {
    uint8_t h = bb_tile(r, eb);
    if (h) {
      if (t_coin(h)) { o.leaf |= L_HCOIN; return o; }
      if ((o.ysp & 0x80) && low >= 4) {
        if (t_headsolid(h) || r[rArea] == 0 || r[rBounce]) { o.leaf |= L_NY; o.ysp = 1; }
        else {
          o.leaf |= L_HIT;
          if (after_head) { m = after_head; o.ysp = m[rYSp]; }
        }
      }
    }
  }
  uint8_t lf = bb_tile(m, eb + 1), rf = bb_tile(m, eb + 2), t = 0;
  if (t_coin(lf)) { o.leaf |= L_FCOIN; return o; }
  if (lf) t = lf;
  else if (rf) { if (t_coin(rf)) { o.leaf |= L_FCOIN; return o; } t = rf; }
  if (t && !t_climb(t) && !(o.ysp & 0x80)) {
    if (t == 0xC5) { o.leaf |= L_AXE; return o; }
    if (!t_hidden(t)) {
      if (r[rJsAnim]) { o.leaf |= L_JS; o.state = 0; }
      else if (low < 5) {
        o.leaf |= L_LAND; o.y = r[rY] & 0xF0; o.ysp = 0; o.yforce = 0; o.state = 0;
        if ((r[rUpDown] & 4) && rf == 0x11 && lf == 0x10) o.ge = 3;
      } else {
        o.leaf |= L_FAILLAND;
        bgc_impede(&o, r[rMovDir]);
        return o;
      }
    }
  }
  // Side checks: first the left pair ($00 = 2), then the right pair ($00 = 1). They see the Y that a
  // landing has just snapped.
  static uint8_t side[0x800];
  memcpy(side, m, 0x800);
  side[rY] = o.y;
  if ((o.leaf & L_LAND) && t_spring(t)) side[rJsAnim] = 1;  // ChkForLandJumpSpring starts the spring
  for (int pass = 2; pass >= 1; pass--) {
    int base = eb + (pass == 2 ? 3 : 5);
    uint8_t s = 0;
    int hit = 0;
    if (o.y >= 0x20) {
      s = bb_tile(side, base);
      if (s && s != 0x1C && s != 0x6B && !t_climb(s)) hit = 1;
    }
    if (!hit) {
      if (o.y < 8) { o.leaf |= L_NOHIT; return o; }
      s = bb_tile(side, base + 1);
      if (s) hit = 1;
    }
    if (!hit) continue;
    if (t_hidden(s)) { o.leaf |= L_SIDEHID; return o; }
    if (t_climb(s)) { o.leaf |= L_CLIMB; return o; }
    if (t_coin(s)) { o.leaf |= L_SCOIN; return o; }
    if (t_spring(s)) {
      if (side[rJsAnim]) { o.leaf |= L_SIDESPR; return o; }
    } else if (o.state == 0 && r[rFacing] == 1 && (s == 0x6C || s == 0x1F)) {
      o.leaf |= L_PIPE;
      if (o.ge == 8) o.ge = 2;
      return o;
    }
    o.leaf |= bgc_impede(&o, (uint8_t)pass) ? L_SIDEPUSH : L_SIDEFREE;
    return o;
  }
  o.leaf |= L_NOHIT;
  return o;
}

// Boot the warps TAS to the first frame Mario is under control in 1-1.
static inline void boot_1_1(NES *n, const char *rom, const char *movie) {
  if (nes_load_rom(rom)) { fprintf(stderr, "rom load failed\n"); exit(2); }
  Movie mv; char err[128];
  if (movie_load(movie, &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); exit(2); }
  if (movie_rom_matches(&mv, rom) != 1) { fprintf(stderr, "movie/ROM mismatch or missing identity\n"); exit(2); }
  nes_power(n); nes_reset(n);
  for (int f = 0; f < mv.n; f++) {
    if (mv.cmd[f] & 1) nes_reset(n);
    if (mv.cmd[f] & 2) nes_power(n);
    nes_frame(n, mv.p1[f], mv.p2[f]);
    if (n->err || !n->frame_done) { fprintf(stderr, "unsupported bootstrap at frame %d\n", f); exit(1); }
    if (n->ram[rOperMode] == 1 && n->ram[rGE] == 8 && n->ram[rTask] == 3) return;
  }
  fprintf(stderr, "no control frame found\n"); exit(2);
}
#endif
