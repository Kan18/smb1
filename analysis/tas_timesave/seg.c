// Searches one stretch of a level from a state of the warped TAS, without reading the TAS's inputs
// for that stretch: one frame per layer over game states. Inputs that reach the same state merge,
// and each layer keeps the best states per cell of (waypoint, facing, height, vertical speed,
// player state, horizontal speed), ranked by an estimate of the frames still to go.
// A result is replayed on the plain emulator from power-on before it is reported.
//
// usage: seg rom movie f0 frames width per_cell threads waypoint... goal
//   f0         start from the state after aligned frame f0 of the movie
//   waypoint   x>=X  x<=X  cam>=C   reached in order; X is level x (loopbacks are undone)
//   goal       pipe[:PTR]  side[:PTR]  axe  exit   (PTR: the AreaPointer the entry must have; exit: the
//              next level's first frame, so a flag grab is followed through its slide, walk and tally)
// env: TOP=24 for water (top speed), OUT=file.fm2 to write the result, NODOWN=1 to leave Down out,
//      GOALY=y the height Mario stands at on the goal (a pipe's top), priced within GOALYWIN px of it
//      (default 64); LATE=n frames a waypoint keeps
//      its own share of the width after the next one is first reached (default 30)
//      LAG=w values Mario's screen position past 112 at w frames a pixel, and keeps it apart in the
//      cells (for a pipe whose pointer a later command would overwrite once the camera reaches it),
//      up to LAGMAX pixels (default 24)
//      ENTRYV=v prices braking to speed v within 32 px of the goal (a pipe whose destination the
//      descent's scrolling can change)
//      ENDGAME=px keeps every distinct state within px of the goal x (up to ENDCAP, default 60000)
//      CELLY=k, CELLV=k cell resolution as shifts: height in 2^k px (default 2), speed in 2^k (default 1);
//      CELLF=k also puts the top k bits of the speed fraction $0705 in the cell (default 0), CELLX=k the top
//      k bits of the x subpixel $0400
//      NOLR=1 leaves out Left+Right together (RTA rules)
//      GOX=rounds runs Go-Explore instead of the beam (GSEL, GLEN, GTEMP, GCAP: see go_explore)
//      EXH=K (with BOUND) searches exhaustively from every state kept K frames before the bound
//      BOUND=f|tas drops states that can't reach the goal by frame f (tas: the TAS's goal frame, plus
//      BSLACK) by a lower bound on the frames left; DOM=1 drops states already held on an earlier frame
//      (DOM=2: comparing everything but the enemies)
//      TRACK=1 follows the TAS's own state through the layers and reports the layer where the
//      search drops it, and why (cell cap or width), with its score against the last one kept
#include "../../emu/nes.c"
#include "../../emu/movie.h"
#include <pthread.h>
#include <time.h>
#include <math.h>

enum { MAX_FRAMES = 4000, MAX_WAY = 8 };

// The idle loop is a JMP to itself. Skip complete iterations between PPU events.
static void fast_frame(NES *n, uint8_t pad) {
  n->pad[0] = pad; n->pad[1] = 0; n->polls = 0; n->frame_done = 0;
  unsigned fuel = 100000;
  while (!n->frame_done && fuel) {
    if (n->pc == 0x8057 && !n->strobe && !n->dma_pending && !n->nmi_pending && !n->nmi_polled &&
        n->nmi_line == (n->vbl && (n->ctrl & 0x80))) {
      int32_t k = (n->next_ev - 1 - n->fpos) / 9 - 1;
      if (k > 0) { n->cyc += 3 * (uint64_t)k; n->fpos += 9 * k; }
    }
    nes_step(n);
    fuel--;
  }
  if (!n->frame_done && !n->err) { n->err = 3; n->err_pc = n->pc; }
  n->frame++;
}

static uint16_t key_bytes[1200];
static int key_n;
static void key_range(int lo, int hi) { for (int a = lo; a <= hi; a++) key_bytes[key_n++] = a; }
static void key_init(void) {
  static const uint16_t one[] = {0x09, 0x0E, 0x1D, 0x33, 0x45, 0x57, 0x6D, 0x86, 0x9F, 0xB5, 0xCE, 0x10D, 0x10F, 0x3C4, 0x400,
    0x416, 0x433, 0x450, 0x456, 0x490, 0x499, 0x6A0, 0x6CC, 0x6CD, 0x6D6, 0x6DE, 0x6FF, 0x70F, 0x714, 0x71A, 0x71C, 0x71E,
    0x723, 0x725, 0x726, 0x728, 0x729, 0x739, 0x73A, 0x73B, 0x73F, 0x740, 0x747, 0x74E, 0x750, 0x751, 0x754, 0x755, 0x756,
    0x75C, 0x75F, 0x760, 0x770, 0x772, 0x775, 0x77F, 0x782, 0x783, 0x785, 0x78A, 0x791, 0x796, 0x79E, 0x7A0, 0x7A1,
    0x7A7, 0x7A8, 0x7F8, 0x7F9, 0x7FA};
  for (unsigned i = 0; i < sizeof one / sizeof *one; i++) key_bytes[key_n++] = one[i];
  key_range(0x0F, 0x1C); key_range(0x1E, 0x2C); key_range(0x46, 0x4C); key_range(0x58, 0x5E); key_range(0x6E, 0x74);
  key_range(0x87, 0x8D); key_range(0xA0, 0xA6); key_range(0xB6, 0xBC); key_range(0xCF, 0xD5); key_range(0x401, 0x407);
  key_range(0x417, 0x41D); key_range(0x434, 0x43A); key_range(0x700, 0x70A); key_range(0x72A, 0x72D);
  key_range(0x3E8, 0x3EF); key_range(0x500, 0x69F); key_range(0x7A7, 0x7AD);  // last: the RNG
}
static uint64_t key_hash(const NES *n) {
  uint64_t h = 1469598103934665603ULL;
  for (int i = 0; i < key_n; i++) { h ^= n->ram[key_bytes[i]]; h *= 1099511628211ULL; }
  h ^= n->ram[0x0D] & 0x80; h *= 1099511628211ULL;
  return h;
}

enum { W_XGE, W_XLE, W_CAM };
static struct { int kind, v; } way[MAX_WAY];
static int nway, goal_kind, goal_ptr = -1, goal_x, goal_y = -1, top_speed = 40, use_down = 1, late = 30;
static double lag_weight; static int lag_max = 24, endgame, endcap = 60000, entry_v, no_lr, goal_y_win = 64;
enum { G_PIPE, G_SIDE, G_AXE, G_EXIT };

static int level0;
static int in_flag(const NES *n) {  // flagpole, castle walk, tally, or the load of the next level
  const uint8_t *r = n->ram;
  return r[0x0E] == 4 || r[0x0E] == 5 || ((r[0x75F] << 8 | r[0x75C]) != level0) || (r[0x770] == 1 && r[0x772] != 3);
}
static int xpix(const NES *n) { return n->ram[0x6D] << 8 | n->ram[0x86]; }
static int cam(const NES *n) { return n->ram[0x71A] << 8 | n->ram[0x71C]; }

// Per state: the waypoint reached so far, and 1024 per loopback (8-4's take four pages off).
// had: the AreaPointer has been the goal's at some point (the parser only moves forward, so losing
// it again means a later pointer command was read and the goal's pipe now goes elsewhere).
typedef struct { uint8_t way; uint8_t loops; uint8_t had; } Prog;

static int goal_met(const NES *n) {
  const uint8_t *r = n->ram;
  int ptr_ok = goal_ptr < 0 || r[0x750] == goal_ptr;
  switch (goal_kind) {
  case G_PIPE: return r[0x0E] == 3 && ptr_ok;
  case G_SIDE: return r[0x0E] == 2 && ptr_ok;
  case G_AXE: return nes_final_victory(n);
  default: return r[0x770] == 1 && r[0x772] == 3 && r[0x0E] == 8 && (r[0x75F] << 8 | r[0x75C]) != level0;
  }
}

// Scrolling during a pipe descent can change its destination. Run through the
// start of the next area to check the pointer that was actually used.
static int destination_ok(const NES *entry) {
  if (goal_ptr < 0) return 1;
  static __thread NES t; t = *entry;
  for (int k = 0; k < 200; k++) {
    fast_frame(&t, 0);
    if (t.err) return 0;
    if (t.ram[0x772] == 0 || t.ram[0x0E] == 0) return t.ram[0x750] == goal_ptr || (goal_ptr == 0x30 && t.ram[0x75F] == 7);
  }
  return 0;
}

static Prog advance(const NES *before, const NES *n, Prog p) {
  if (xpix(n) + 600 < xpix(before)) p.loops++;
  if (goal_ptr >= 0 && n->ram[0x750] == goal_ptr) p.had = 1;
  int x = xpix(n) + 1024 * p.loops;
  while (p.way < nway) {
    int k = way[p.way].kind, v = way[p.way].v;
    int ok = k == W_XGE ? x >= v : k == W_XLE ? x <= v : cam(n) + 1024 * p.loops >= v;
    if (!ok) break;
    p.way++;
  }
  return p;
}

// Frames to cover dx (1/256 px) from speed v, accelerating at about the largest rate.
static double run_time(double dx, int v) {
  if (dx <= 0) return 0;
  const double a = 1.78, top = top_speed;
  double d = dx / 16, w = v > top ? top : v, reach = (top * top - w * w) / (2 * a);
  if (w < -top) w = -top;
  if (d <= reach) return (-w + sqrt(w * w + 2 * a * d)) / a;
  return (top - w) / a + (d - reach) / top;
}

// Estimate frames to fall from y to target at about the game's gravity, capped at top fall speed.
static int fall_time(int y, double vy, int target) {
  int t = 0;
  for (double q = y; q < target && t < 120; t++) {
    vy = vy + 0.4 > 4 ? 4 : vy + 0.4;
    q += vy;
  }
  return t;
}

// Frames to cover d (1/16 px) from speed v and stop at its end: full acceleration, top speed if
// there is room, then braking at about 1.75 a frame (as the TAS brakes). If Mario can't stop in
// time, *over is how far past the end he stops.
static double stop_time(double d, double v, double *over) {
  const double a = 1.78, b = 1.75, top = top_speed;
  *over = 0;
  if (v < 0) { double back = v * v / (2 * a); d += back; v = 0; }  // moving away first: roughly
  if (v * v / (2 * b) >= d) { *over = v * v / (2 * b) - d; return v / b; }
  double w2 = (d + v * v / (2 * a)) / (1 / (2 * a) + 1 / (2 * b)), w = sqrt(w2);
  if (w <= top) return (w - v) / a + w / b;
  return (top - v) / a + top / b + (d - (top * top - v * v) / (2 * a) - top * top / (2 * b)) / top;
}

static int64_t score_of(const NES *n, Prog p) {
  const uint8_t *r = n->ram;
  double x = (xpix(n) + 1024.0 * p.loops) * 256 + r[0x400], t = 0;
  int v = (int8_t)r[0x57];
  if (p.way < nway) {
    int k = way[p.way].kind, w = way[p.way].v;
    int at = k == W_CAM ? w + 112 : w;
    int next = p.way + 1 < nway ? (way[p.way + 1].kind == W_CAM ? way[p.way + 1].v + 112 : way[p.way + 1].v) : goal_x;
    double over = 0;
    int turns = k != W_XLE && (p.way + 1 < nway || goal_x) && next < at;
    if (turns) t = stop_time((at * 256.0 - x) / 16, v, &over);
    else if (k == W_XGE) t = run_time(w * 256.0 - x, v);
    else if (k == W_XLE) t = run_time(x - w * 256.0, -v);
    else t = run_time(at * 256.0 - x, v);
    // What is left after this waypoint. A turn back starts from rest at the waypoint (or past it,
    // if Mario can't stop in time); the rest is at top speed.
    int from = at;
    for (int j = p.way + 1; j <= nway; j++) {
      int to = j < nway ? (way[j].kind == W_CAM ? way[j].v + 112 : way[j].v) : goal_x;
      if (j == nway && !goal_x) break;
      if (j == p.way + 1 && turns) t += run_time((from - to) * 256.0 + over * 16, 0);
      else t += fabs((double)(to - from)) * 16 / top_speed;
      from = to;
    }
  } else if (goal_x) {
    double dx = goal_x * 256.0 - x;
    t = dx >= 0 ? run_time(dx, v) : run_time(-dx, -v);
    // Height near the goal, for a pipe entry: above it, Mario has to fall that far;
    // below it, he has to climb, which this can only price roughly.
    if (goal_y >= 0 && fabs(dx) < goal_y_win * 256.0 && r[0xB5] == 1) {
      double vy = (int8_t)r[0x9F] + r[0x433] / 256.0;
      if (r[0xCE] < goal_y) { int fall = fall_time(r[0xCE], vy, goal_y); if (fall > t) t = fall; }
      else if (r[0xCE] > goal_y + 2) t += 12 + (r[0xCE] - goal_y) / 4.0;
    }
  }
  // Camera lag: frames per pixel of Mario's screen position past 112, for goals (4-2's wrong warp)
  // that need the camera held back so a later pointer command isn't read before the area loads.
  if (lag_weight > 0) { int pos = xpix(n) - cam(n) - 112; if (pos > lag_max) pos = lag_max; if (pos > 0) t -= lag_weight * pos; }
  // Entry speed: in 4-2 the camera keeps scrolling during the descent with Mario's speed, so an
  // entry faster than ENTRYV reads the next pointer command. Price the braking it needs.
  if (entry_v > 0 && p.way >= nway && goal_x && fabs(x / 256.0 - goal_x) < 32 && v > entry_v) t += (v - entry_v) / 1.75;
  return (int64_t)llround(-t * 65536) + (int64_t)p.way * ((int64_t)1 << 50);
}

// Frames still needed, never more than the game can do: the remaining path (each waypoint in turn,
// then the goal x) at the largest acceleration ($1C8 a frame, 1.78 speed units) up to top speed, from
// the current speed on the first leg, from rest on a leg that turns back (Mario stops at the turning
// point), and at top speed otherwise. Height, walls, enemies and braking are ignored. A camera waypoint
// needs Mario 80 px past it (the camera moves only while he is at screen x 80 or more). The continuous
// formula can be off by a fraction of a frame on the discrete steps, so the bound is shaded down.
static double lower_bound(const NES *n, Prog p) {
  const uint8_t *r = n->ram;
  double x = (xpix(n) + 1024.0 * p.loops) * 256 + r[0x400], t = 0;
  int v = (int8_t)r[0x57], dir = v > 0 ? 1 : v < 0 ? -1 : 0, first = 1;
  for (int j = p.way; j <= nway; j++) {
    double to;
    if (j < nway) to = (way[j].kind == W_CAM ? way[j].v + 80 : way[j].v) * 256.0;
    else if (goal_x) to = goal_x * 256.0;
    else break;
    if (j < nway && ((way[j].kind == W_XGE && x >= to) || (way[j].kind == W_XLE && x <= to))) continue;
    double d = to - x; int ld = d > 0 ? 1 : d < 0 ? -1 : 0;
    if (ld == 0) continue;
    if (first) t += run_time(fabs(d), ld * v);
    else if (ld != dir) t += run_time(fabs(d), 0);
    else t += fabs(d) / 16 / top_speed;
    x = to; dir = ld; first = 0;
  }
  // Height (GOALY): Mario has to be at the goal's height when he gets there. Rising is at most 5 px a
  // frame on land (a jump starts at -5) and 2.5 swimming; falling starts from the current speed and gains
  // at most 0.5 a frame up to 4.5 (3.5 swimming). Both happen during the run, so the bound is the larger.
  if (goal_y >= 0 && r[0xB5] == 1) {
    int water = top_speed < 40;
    double y = r[0xCE], tv = 0;
    if (y > goal_y) tv = (y - goal_y) / (water ? 2.5 : 5.0);
    else if (y < goal_y) {
      double vy = (int8_t)r[0x9F] + r[0x433] / 256.0, cap = water ? 3.5 : 4.5;
      if (vy < 0) vy = 0;
      for (double q = y; q < goal_y && tv < 200; tv++) { vy = vy + 0.5 > cap ? cap : vy + 0.5; q += vy; }
    }
    if (tv > t) t = tv;
  }
  return t * 0.97 - 1;
}

// Cell resolution: CELLY=2 (pixels of height, as a shift: 2 is 4 px) and CELLV=1 (speed shift).
static int cell_yshift = 2, cell_vshift = 1, cell_frac_bits, cell_sub_bits;
static uint32_t cell_of(const NES *n, Prog p) {
  const uint8_t *r = n->ram;
  if (goal_kind == G_EXIT && in_flag(n)) return 0xFF000000u | (uint32_t)(r[0xCE] << 8) | r[0x7FA];
  int y = r[0xB5] == 1 ? r[0xCE] >> cell_yshift : r[0xB5] == 0 ? 0 : 255 >> cell_yshift, vy = (int8_t)r[0x9F], st = r[0x1D] & 3, v = (int8_t)r[0x57];
  if (vy > 5) vy = 5;
  if (vy < -5) vy = -5;
  if (v < -40) v = -40;
  if (v > 40) v = 40;
  int face = r[0x33] == 2 ? 1 : r[0x33] == 1 ? 0 : 2;
  uint32_t c = (uint32_t)p.way << 28 | (uint32_t)face << 26 | (uint32_t)y << 17 | (uint32_t)(vy + 5) << 13 | (uint32_t)st << 11 |
               (uint32_t)(((v + 40) >> cell_vshift) & 127);
  // The jump's gravity (VerticalForce, VerticalForceDown) and the friction adder the L+R launch
  // changes: same height and speeds with these different is a different arc ahead.
  c ^= ((uint32_t)r[0x709] * 0x9E3779B1u ^ (uint32_t)r[0x70A] * 0x85EBCA77u ^ (uint32_t)r[0x702] * 0xC2B2AE3Du) & 0x7FFu;
  if (lag_weight > 0) { int pos = xpix(n) - cam(n); c ^= (uint32_t)(pos >> 2) * 0x27D4EB2Fu & 0x7FFu; }
  // CELLF=k: the top k bits of the speed fraction ($0705), which decides the frame the speed next steps
  if (cell_frac_bits) c ^= (uint32_t)(r[0x705] >> (8 - cell_frac_bits)) * 0x165667B1u & 0x7FFu;
  // CELLX=k: the top k bits of the x subpixel ($0400)
  if (cell_sub_bits) c ^= (uint32_t)((r[0x400] >> (8 - cell_sub_bits)) + 1) * 0xD3A2646Cu & 0x7FFu;
  return c;
}

// Search heuristics for omitting inputs expected to have the same effect.
static int omit_input(const NES *n, uint8_t in) {
  const uint8_t *r = n->ram;
  if (r[0x756] == 2 || r[0x0E] != 8) return 0;
  int b = in & 0x02, lr = in & 0xC0;
  if (r[0x704]) return b && lr != 0x00;                                                  // swimming
  if (r[0x1D] != 0) return b != 0;                                                            // airborne
  return b && lr == 0xC0;                                                                // ground
}
static int alphabet(const NES *n, Prog p, uint8_t *in) {
  static const uint8_t base[] = {0x80, 0x81, 0x00, 0x01, 0x40, 0x41, 0xC0, 0xC1, 0x82, 0x83, 0x02, 0x03, 0x42, 0x43, 0xC2, 0xC3};
  int c = 0;
  for (unsigned i = 0; i < sizeof base; i++) {
    if (no_lr && (base[i] & 0xC0) == 0xC0) continue;
    if (!omit_input(n, base[i])) in[c++] = base[i];
  }
  int x = xpix(n) + 1024 * p.loops;
  if (in_flag(n)) { in[0] = 0; return 1; }  // input does nothing here
  if (use_down && goal_kind == G_PIPE && p.way >= nway && abs(x - goal_x) <= 40) {
    static const uint8_t down[] = {0xA2, 0xA0, 0x22, 0x20, 0x60, 0x62};
    for (unsigned i = 0; i < sizeof down; i++) in[c++] = down[i];
  }
  return c;
}

// fine: x to 1/65536 px (with Player_X_MoveForce), then speed, to break ties the score can't see.
// Without it, equal scores fall in arbitrary order and the cell cap drops the TAS's own states.
typedef struct { uint64_t hash, dom; int64_t score, fine; uint32_t parent, cell; uint8_t input, band, end; Prog prog; } Child;
// With LAG, each band of camera lag (0, 1-7, 8-15, 16+ px past 112) keeps its own share of the width,
// as the waypoint levels do: building lag costs speed at once and pays only later.
// A state whose SideCollisionTimer runs is where lag starts (the camera holds while it runs), so
// it joins the first band before any lag shows.
static int lag_band(const NES *n) {
  int pos = xpix(n) - cam(n) - 112;
  if (pos <= 0) return n->ram[0x785] && xpix(n) - cam(n) >= 80 ? 1 : 0;
  return pos < 8 ? 1 : pos < 16 ? 2 : 3;
}

static NES *cur, *nxt;
static Prog *cur_prog, *nxt_prog;
static uint32_t cur_n, picked_n;
static Child *picked;
static uint32_t *par[MAX_FRAMES];
static uint8_t *inp[MAX_FRAMES];
static int width, per_cell, threads, lives0, tracking;
static volatile int shared_i;
static Child **tchild;
static size_t *tn, *tcap;
static volatile int goal_at = -1; static volatile uint32_t goal_parent; static volatile uint8_t goal_input;
static pthread_mutex_t goal_lock = PTHREAD_MUTEX_INITIALIZER;
static volatile long wrong_pipe; static volatile int wrong_ptr_seen;
// BOUND: drop a child whose frame plus lower_bound passes the bound frame (BOUND=tas: the TAS's goal frame,
// plus BSLACK). DOM=1: drop a child whose state (the key without the frame counter, the frame rule, the
// timer and the RNG) a kept state already had on an earlier frame; DOM=2 also leaves the enemy slots out.
static int bound = -1, dom_mode, cur_frame; static volatile long bound_cut, dom_cut;
static uint64_t *domtab; static size_t dommask;
static uint64_t dom_hash(const NES *n) {
  const uint8_t *r = n->ram;
  uint64_t h = 1469598103934665603ULL;
  for (int i = 0; i < key_n; i++) {
    int a = key_bytes[i];
    if (a == 0x09 || a == 0x77F || (a >= 0x7A7 && a <= 0x7AD) || (a >= 0x7F8 && a <= 0x7FA)) continue;
    if (dom_mode >= 2 && ((a >= 0x0F && a <= 0x14) || (a >= 0x16 && a <= 0x1B) || (a >= 0x1E && a <= 0x23) ||
        (a >= 0x46 && a <= 0x4B) || (a >= 0x58 && a <= 0x5D) || (a >= 0x6E && a <= 0x73) || (a >= 0x87 && a <= 0x8C) ||
        (a >= 0xA0 && a <= 0xA5) || (a >= 0xB6 && a <= 0xBB) || (a >= 0xCF && a <= 0xD4) || (a >= 0x401 && a <= 0x406) ||
        (a >= 0x417 && a <= 0x41C) || (a >= 0x434 && a <= 0x439))) continue;
    h ^= r[a]; h *= 1099511628211ULL;
  }
  h ^= r[0x0D] & 0x80; h *= 1099511628211ULL;
  return h | 1;  // 0 marks an empty slot
}
static int dom_seen(uint64_t h) {
  for (size_t i = h & dommask;; i = (i + 1) & dommask) { if (domtab[i] == h) return 1; if (!domtab[i]) return 0; }
}
static void dom_add(uint64_t h) {
  for (size_t i = h & dommask;; i = (i + 1) & dommask) { if (domtab[i] == h) return; if (!domtab[i]) { domtab[i] = h; return; } }
}
static Child *endpool;

static int dead_state(const NES *n) {
  const uint8_t *r = n->ram;
  if (goal_kind == G_EXIT && in_flag(n)) return r[0x75A] != lives0 || r[0x770] != 1;
  return r[0x0E] == 6 || r[0x0E] == 0x0B || r[0x770] != 1 || r[0xB5] > 1 || r[0x75A] != lives0 ||
         (r[0x75F] << 8 | r[0x75C]) != level0;
}

static void *expand(void *arg) {
  long t = (long)arg;
  for (;;) {
    int i0 = __sync_fetch_and_add(&shared_i, 64);
    if ((uint32_t)i0 >= cur_n) return NULL;
    for (uint32_t i = i0; i < (uint32_t)i0 + 64 && i < cur_n; i++) {
      uint8_t in[24];
      const NES *par = &cur[i];
      int c = alphabet(par, cur_prog[i], in);
      for (int k = 0; k < c; k++) {
        NES next = *par;
        NES *sp = &next;
        fast_frame(sp, in[k]);
        if (sp->err) continue;
        Prog p = advance(par, sp, cur_prog[i]);
        if (p.way >= nway && goal_met(sp) && ((goal_kind != G_PIPE && goal_kind != G_SIDE) || destination_ok(sp))) {
          pthread_mutex_lock(&goal_lock);
          if (goal_at < 0 || i < goal_parent) { goal_at = 1; goal_parent = i; goal_input = in[k]; }
          pthread_mutex_unlock(&goal_lock);
          continue;
        }
        if (dead_state(sp)) continue;
        if (p.had && sp->ram[0x750] != goal_ptr && sp->ram[0x0E] == 8) continue;  // the goal's pipe now goes elsewhere
        if ((sp->ram[0x0E] == 2 || sp->ram[0x0E] == 3) && p.way >= nway) {  // a pipe, but not the goal's
          __sync_fetch_and_add(&wrong_pipe, 1);
          if (!wrong_ptr_seen) wrong_ptr_seen = 0x100 | sp->ram[0x750];
        }
        if (sp->ram[0x0E] != 8 && !(goal_kind == G_EXIT && in_flag(sp))) continue;
        if (tn[t] == tcap[t]) { tcap[t] *= 2; tchild[t] = realloc(tchild[t], tcap[t] * sizeof(Child)); }
        int64_t sc = goal_kind == G_EXIT && in_flag(sp) ? INT64_MAX / 2 : score_of(sp, p);
        int64_t fine = ((((int64_t)xpix(sp) + 1024 * p.loops) * 256 + sp->ram[0x400]) * 256 + sp->ram[0x705]) * 256 + (uint8_t)(sp->ram[0x57] + 128);
        int xe = xpix(sp) + 1024 * p.loops;
        uint8_t end = endgame > 0 && p.way >= nway && abs(xe - goal_x) <= endgame && sp->ram[0x0E] == 8;
        if (bound >= 0 && !(goal_kind == G_EXIT && in_flag(sp)) && cur_frame + lower_bound(sp, p) > bound) { __sync_fetch_and_add(&bound_cut, 1); continue; }
        tchild[t][tn[t]++] = (Child){key_hash(sp), dom_mode ? dom_hash(sp) : 0, sc, fine, i, cell_of(sp, p), in[k], (uint8_t)(lag_weight > 0 ? lag_band(sp) : 0), end, p};
      }
    }
  }
}

static void *rebuild(void *arg) {
  (void)arg;
  for (;;) {
    int i0 = __sync_fetch_and_add(&shared_i, 64);
    if ((uint32_t)i0 >= picked_n) return NULL;
    for (uint32_t i = i0; i < (uint32_t)i0 + 64 && i < picked_n; i++) {
      nxt[i] = cur[picked[i].parent];
      fast_frame(&nxt[i], picked[i].input);
      nxt_prog[i] = picked[i].prog;
    }
  }
}

static void run_threads(void *(*fn)(void *)) {
  pthread_t th[64];
  shared_i = 0;
  for (long t = 0; t < threads; t++) pthread_create(&th[t], NULL, fn, (void *)t);
  for (int t = 0; t < threads; t++) pthread_join(th[t], NULL);
}


// ---- Exhaustive endgame (EXH=K, with BOUND) ------------------------------------------------------------
// From a set of root states (the beam's states K frames before the bound, or Go-Explore's archive cells
// that can still finish in time), search depth-first over the search alphabet, cutting a branch once its frame
// plus lower_bound passes the bound (or one frame before the best goal found so far), and skipping a
// (state key, frame) pair already searched (a shared table). The roots, input alphabet,
// state keys and timing estimate all limit the scope of the experiment.
enum { EXH_MAXD = 120 };
static int exh_k, exh_best = 1 << 30, exh_best_root = -1, exh_best_len; static uint8_t exh_best_path[EXH_MAXD];
static uint64_t *exh_tab; static size_t exh_mask; static volatile long exh_nodes, exh_full;
static int exh_nroot; static const NES **exh_roots; static int *exh_rframe; static Prog *exh_rprog;
static int exh_seen(uint64_t h) {
  h |= 1;
  size_t i = h & exh_mask;
  for (int probe = 0; probe < 64; probe++, i = (i + 1) & exh_mask) {
    uint64_t v = exh_tab[i];
    if (v == h) return 1;
    if (!v) { if (__sync_bool_compare_and_swap(&exh_tab[i], 0, h)) return 0; if (exh_tab[i] == h) return 1; }
  }
  __sync_fetch_and_add(&exh_full, 1);
  return 0;
}
static void exh_dfs(NES *stack, int depth, int f, Prog p, uint8_t *path, int root) {
  const NES *parent = &stack[depth];
  uint8_t in[24];
  int c = alphabet(parent, p, in);
  for (int k = 0; k < c; k++) {
    NES *sp = &stack[depth + 1];
    *sp = *parent;
    fast_frame(sp, in[k]);
    __sync_fetch_and_add(&exh_nodes, 1);
    int f1 = f + 1;
    if (sp->err) continue;
    Prog q = advance(parent, sp, p);
    if (q.way >= nway && goal_met(sp)) {
      if ((goal_kind == G_PIPE || goal_kind == G_SIDE) && !destination_ok(sp)) continue;
      pthread_mutex_lock(&goal_lock);
      if (f1 < exh_best || (f1 == exh_best && root < exh_best_root)) {
        exh_best = f1; exh_best_root = root; exh_best_len = depth + 1;
        memcpy(exh_best_path, path, depth); exh_best_path[depth] = in[k];
      }
      pthread_mutex_unlock(&goal_lock);
      continue;
    }
    if (dead_state(sp) || (q.had && sp->ram[0x750] != goal_ptr && sp->ram[0x0E] == 8)) continue;
    if (sp->ram[0x0E] != 8 && !(goal_kind == G_EXIT && in_flag(sp))) continue;
    int limit = bound < exh_best - 1 ? bound : exh_best - 1;
    if (f1 >= limit || f1 + lower_bound(sp, q) > limit || depth + 1 >= EXH_MAXD) continue;
    if (exh_seen(key_hash(sp) ^ (uint64_t)f1 * 0x9E3779B97F4A7C15ULL)) continue;
    path[depth] = in[k];
    exh_dfs(stack, depth + 1, f1, q, path, root);
  }
}
static void *exh_worker(void *arg) {
  (void)arg;
  NES *stack = malloc((EXH_MAXD + 1) * sizeof *stack);
  uint8_t path[EXH_MAXD];
  for (;;) {
    int r = __sync_fetch_and_add(&shared_i, 1);
    if (r >= exh_nroot) break;
    if (exh_rframe[r] + 1 > (bound < exh_best - 1 ? bound : exh_best - 1)) continue;
    stack[0] = *exh_roots[r];
    exh_dfs(stack, 0, exh_rframe[r], exh_rprog[r], path, r);
  }
  free(stack);
  return NULL;
}
static void run_threads(void *(*fn)(void *));
static double now(void);
// Runs the endgame search over roots [0, n); returns the best goal frame (1 << 30 if none).
static int exh_run(int n, double t0) {
  if (!exh_tab) { exh_mask = (1u << 26) - 1; exh_tab = calloc(exh_mask + 1, sizeof *exh_tab); }
  exh_nroot = n; shared_i = 0;
  run_threads(exh_worker);
  printf("EXHAUSTIVE: %d root states, %ld frames emulated, %ld table misses; best goal %s%d (%.0f s)\n", n, exh_nodes, exh_full,
         exh_best < (1 << 30) ? "f" : "none ", exh_best < (1 << 30) ? exh_best : 0, now() - t0);
  return exh_best;
}

// A total order, so the threads' output order never decides which of two tied states is kept (it did:
// the same run gave +3 and +23 frames in 8-4's water section).
static int better(const Child *x, const Child *y) {
  if (x->score != y->score) return x->score > y->score ? -1 : 1;
  if (x->fine != y->fine) return x->fine > y->fine ? -1 : 1;
  if (x->hash != y->hash) return x->hash < y->hash ? -1 : 1;
  if (x->parent != y->parent) return x->parent < y->parent ? -1 : 1;
  return x->input < y->input ? -1 : x->input > y->input;
}
static int by_hash(const void *a, const void *b) {
  const Child *x = a, *y = b;
  if (x->hash != y->hash) return x->hash < y->hash ? -1 : 1;
  return better(x, y);
}
static int by_cell(const void *a, const void *b) {
  const Child *x = a, *y = b;
  if (x->cell != y->cell) return x->cell < y->cell ? -1 : 1;
  return better(x, y);
}
static int by_score(const void *a, const void *b) { return better(a, b); }

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void write_movie(const char *file, const Movie *mv, const uint8_t *in, int count) {
  FILE *f = fopen(file, "w");
  if (!f) { perror(file); return; }
  fprintf(f, "version 3\nemuVersion 22020\nrerecordCount 0\npalFlag 0\nromFilename Super Mario Bros.\nromChecksum %s\n"
             "guid 00000000-0000-0000-0000-000000000000\nfourscore 0\nmicrophone 0\nport0 1\nport1 0\nport2 0\nFDS 0\nNewPPU 0\n",
          mv->checksum);
  fprintf(f, "|1|........|........||\n");  // the reset frame the startup convention drops
  for (int i = 0; i < count; i++) {
    char s[9] = "........";
    for (int b = 0; b < 8; b++) if (in[i] >> (7 - b) & 1) s[b] = "RLDUTSBA"[b];
    fprintf(f, "|0|%s|........||\n", s);
  }
  fclose(f);
}

// ---- Go-Explore (GOX=rounds) ---------------------------------------------------------------------------
// An archive of cells, each holding the earliest state found in it and the inputs that reach it. Every
// round picks GSEL cells (default 1000), favouring ones picked less often and ones whose frame plus
// lower bound is early, and plays GLEN frames (default 32) of random inputs from each; an input repeats
// with probability 0.75. A state joins the archive if its cell is new or it reaches the cell on an earlier
// frame. A set-up that loses time now (a ledge to stand on, camera lag) keeps its own cell instead of being
// pushed out of a beam. Cells: waypoint, x/8 (with loopbacks), y/8, speed/4, vertical direction, player
// state, facing, swimming, camera lag/8 with LAG. Uses BOUND to skip cells and stop rollouts that can't
// reach the goal by then.
typedef struct { uint64_t key; int frame; int64_t score; double promise; uint32_t chosen; Prog prog; uint8_t *path; } GCell;
typedef struct { uint64_t key; int frame; int64_t score; double promise; Prog prog; uint32_t from; NES *state; uint8_t *tail; int tlen; } GCand;
static GCell *gcells; static NES *gstates; static uint32_t gn, gcap; static uint32_t *gidx; static size_t gmask;
static int g_f0, g_best = -1; static uint8_t *g_best_path; static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;
static uint32_t *g_sel; static int g_nsel, g_len, g_round; static GCand **g_cand; static size_t *g_ncand, *g_capcand;

static uint64_t gcell_of(const NES *n, Prog p) {
  const uint8_t *r = n->ram;
  int x = xpix(n) + 1024 * p.loops, y = r[0xB5] == 1 ? r[0xCE] : r[0xB5] == 0 ? 0 : 255, v = (int8_t)r[0x57], vy = (int8_t)r[0x9F];
  uint64_t k = (uint64_t)p.way << 56 ^ (uint64_t)(x >> 3) << 36 ^ (uint64_t)(y >> 3) << 28 ^ (uint64_t)((v + 64) >> 2) << 20 ^
               (uint64_t)(vy < 0 ? 0 : vy == 0 ? 1 : 2) << 16 ^ (uint64_t)(r[0x1D] & 3) << 12 ^ (uint64_t)(r[0x33] & 3) << 8 ^
               (uint64_t)(r[0x704] != 0) << 6;
  if (lag_weight > 0) k ^= (uint64_t)((xpix(n) - cam(n)) >> 3 & 63);
  return k * 0x9E3779B97F4A7C15ULL | 1;
}
static uint32_t gfind(uint64_t key) {  // index+1, or 0
  for (size_t i = key & gmask;; i = (i + 1) & gmask) { if (!gidx[i]) return 0; if (gcells[gidx[i] - 1].key == key) return gidx[i]; }
}
static void ginsert(uint64_t key, uint32_t id) {
  for (size_t i = key & gmask;; i = (i + 1) & gmask) if (!gidx[i]) { gidx[i] = id + 1; return; }
}
static uint64_t g_rng(uint64_t *s) { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }

static void *g_explore(void *arg) {
  long t = (long)arg;
  for (;;) {
    int si = __sync_fetch_and_add(&shared_i, 1);
    if (si >= g_nsel) return NULL;
    uint32_t c = g_sel[si]; GCell base = gcells[c];
    uint64_t rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)g_round << 32 | (uint64_t)si);
    NES state = gstates[c];
    Prog p = base.prog; int f = base.frame; uint8_t prev = 0x80, tail[256]; int tl = 0;
    for (int k = 0; k < g_len && tl < 256; k++) {
      NES previous = state;
      uint8_t in[24];
      int nin = alphabet(&previous, p, in), keep = 0;
      for (int q = 0; q < nin; q++) if (in[q] == prev) keep = 1;
      uint8_t a = keep && g_rng(&rs) % 4 ? prev : in[g_rng(&rs) % nin];
      fast_frame(&state, a); f++; tail[tl++] = a; prev = a;
      const NES *sp = &state;
      if (sp->err) break;
      p = advance(&previous, sp, p);
      if (p.way >= nway && goal_met(sp)) {
        int ok = (goal_kind != G_PIPE && goal_kind != G_SIDE) || destination_ok(sp);
        if (ok) {
          pthread_mutex_lock(&g_lock);
          if (g_best < 0 || f < g_best) {
            g_best = f; g_best_path = realloc(g_best_path, f - g_f0);
            memcpy(g_best_path, base.path, base.frame - g_f0); memcpy(g_best_path + (base.frame - g_f0), tail, tl);
          }
          pthread_mutex_unlock(&g_lock);
        }
        break;
      }
      if (dead_state(sp) || (p.had && sp->ram[0x750] != goal_ptr && sp->ram[0x0E] == 8)) break;
      if (sp->ram[0x0E] != 8 && !(goal_kind == G_EXIT && in_flag(sp))) break;
      double lb = lower_bound(sp, p);
      if (bound >= 0 && f + lb > bound) break;
      uint64_t key = gcell_of(sp, p); uint32_t have = gfind(key);
      int64_t sc = score_of(sp, p);
      if (have && (gcells[have - 1].frame < f || (gcells[have - 1].frame == f && gcells[have - 1].score >= sc))) continue;
      if (g_ncand[t] == g_capcand[t]) { g_capcand[t] *= 2; g_cand[t] = realloc(g_cand[t], g_capcand[t] * sizeof(GCand)); }
      GCand *cd = &g_cand[t][g_ncand[t]++];
      cd->key = key; cd->frame = f; cd->score = sc; cd->promise = f + lb; cd->prog = p; cd->from = c; cd->tlen = tl;
      cd->state = malloc(sizeof *cd->state);
      *cd->state = state;
      cd->tail = malloc(tl); memcpy(cd->tail, tail, tl);
    }
  }
}

static int by_cand(const void *a, const void *b) {
  const GCand *x = a, *y = b;
  if (x->key != y->key) return x->key < y->key ? -1 : 1;
  if (x->frame != y->frame) return x->frame < y->frame ? -1 : 1;
  return x->score > y->score ? -1 : x->score < y->score;
}

static int go_explore(const Movie *mv, int f0, int frames, const NES *s0, Prog p0, int tas_goal) {
  int rounds = atoi(getenv("GOX"));
  g_nsel = getenv("GSEL") ? atoi(getenv("GSEL")) : 1000; g_len = getenv("GLEN") ? atoi(getenv("GLEN")) : 32;
  double temp = getenv("GTEMP") ? atof(getenv("GTEMP")) : 4;
  gcap = getenv("GCAP") ? atoi(getenv("GCAP")) : 400000; g_f0 = f0;
  gcells = calloc(gcap, sizeof *gcells); gstates = malloc((size_t)gcap * sizeof *gstates);
  gmask = 1; while (gmask < (size_t)gcap * 2) gmask <<= 1; gidx = calloc(gmask, sizeof *gidx); gmask--;
  g_sel = malloc(g_nsel * sizeof *g_sel);
  g_cand = calloc(threads, sizeof *g_cand); g_ncand = calloc(threads, sizeof *g_ncand); g_capcand = calloc(threads, sizeof *g_capcand);
  for (int t = 0; t < threads; t++) { g_capcand[t] = 4096; g_cand[t] = malloc(4096 * sizeof(GCand)); }
  gstates[0] = cur[0];
  gcells[0] = (GCell){gcell_of(s0, p0), f0, score_of(s0, p0), f0 + lower_bound(s0, p0), 0, p0, NULL}; ginsert(gcells[0].key, 0); gn = 1;
  double t0 = now(); uint64_t rs = 12345; double *w = malloc((size_t)gcap * sizeof *w);
  printf("go-explore: %d rounds of %d cells x %d frames (TAS f%d)\n", rounds, g_nsel, g_len, tas_goal);
  for (g_round = 0; g_round < rounds; g_round++) {
    double minp = 1e18, tot = 0;
    for (uint32_t i = 0; i < gn; i++) if (gcells[i].promise < minp) minp = gcells[i].promise;
    for (uint32_t i = 0; i < gn; i++) {
      double pr = gcells[i].promise;
      w[i] = (bound >= 0 && pr > bound) || (g_best >= 0 && pr >= g_best) || gcells[i].frame >= f0 + frames ? 0 :
             exp2(-(pr - minp) / temp) / sqrt(1.0 + gcells[i].chosen);
      tot += w[i];
    }
    if (tot <= 0) { printf("round %d: no cell can still improve\n", g_round); break; }
    for (int si = 0; si < g_nsel; si++) {
      double u = (g_rng(&rs) >> 11) * (1.0 / 9007199254740992.0) * tot, acc = 0; uint32_t i = 0;
      for (; i + 1 < gn; i++) { acc += w[i]; if (acc > u) break; }
      g_sel[si] = i; gcells[i].chosen++;
    }
    for (int t = 0; t < threads; t++) g_ncand[t] = 0;
    shared_i = 0; run_threads(g_explore);
    size_t nc = 0; for (int t = 0; t < threads; t++) nc += g_ncand[t];
    GCand *all = malloc((nc + 1) * sizeof *all); size_t m = 0;
    for (int t = 0; t < threads; t++) { memcpy(all + m, g_cand[t], g_ncand[t] * sizeof(GCand)); m += g_ncand[t]; }
    qsort(all, nc, sizeof *all, by_cand);
    for (size_t i = 0; i < nc; i++) {
      GCand *cd = &all[i];
      if (i && all[i - 1].key == cd->key) { free(cd->state); free(cd->tail); continue; }
      uint32_t have = gfind(cd->key), id;
      if (have && (gcells[have - 1].frame < cd->frame || (gcells[have - 1].frame == cd->frame && gcells[have - 1].score >= cd->score))) { free(cd->state); free(cd->tail); continue; }
      if (have) id = have - 1;
      else { if (gn == gcap) { free(cd->state); free(cd->tail); continue; } id = gn++; ginsert(cd->key, id); gcells[id].chosen = 0; }
      const GCell *from = &gcells[cd->from];
      uint8_t *path = malloc(cd->frame - f0);
      memcpy(path, from->path, from->frame - f0); memcpy(path + (from->frame - f0), cd->tail, cd->tlen);
      if (have) free(gcells[id].path);
      gcells[id].key = cd->key; gcells[id].frame = cd->frame; gcells[id].score = cd->score; gcells[id].promise = cd->promise;
      gcells[id].prog = cd->prog; gcells[id].path = path;
      gstates[id] = *cd->state; free(cd->state); free(cd->tail);
    }
    free(all);
    if (g_round % 50 == 0 || g_round == rounds - 1) {
      int maxway = 0, bx = 0; double bestp = 1e18;
      for (uint32_t i = 0; i < gn; i++) if (gcells[i].prog.way > maxway) maxway = gcells[i].prog.way;
      for (uint32_t i = 0; i < gn; i++) if (gcells[i].prog.way == maxway && gcells[i].promise < bestp) { bestp = gcells[i].promise; bx = i; }
      const NES *b = &gstates[bx];
      printf("round %d: furthest waypoint level %d, its best cell f%d x=%d y=%d v=%d (finish no earlier than f%.1f)\n", g_round, maxway,
             gcells[bx].frame, xpix(b) + 1024 * gcells[bx].prog.loops, b->ram[0xCE], (int8_t)b->ram[0x57], bestp);
      printf("round %d: %u cells, earliest possible finish f%.1f, best goal %s%d (%.0f s)\n", g_round, gn, minp,
             g_best < 0 ? "none " : "f", g_best < 0 ? 0 : g_best, now() - t0);
      fflush(stdout);
    }
  }
  if (exh_k && bound >= 0) {
    // The archive's cells within EXH frames of the bound that can still finish in time, earliest first.
    uint32_t *ids = malloc(gn * sizeof *ids); int n = 0;
    for (uint32_t i = 0; i < gn; i++) if (gcells[i].frame >= bound - exh_k && gcells[i].frame < bound && gcells[i].promise <= bound) ids[n++] = i;
    for (int a = 1; a < n; a++) { uint32_t v = ids[a]; int b = a; while (b > 0 && gcells[ids[b - 1]].promise > gcells[v].promise) { ids[b] = ids[b - 1]; b--; } ids[b] = v; }
    exh_roots = malloc((n + 1) * sizeof *exh_roots); exh_rframe = malloc((n + 1) * sizeof *exh_rframe); exh_rprog = malloc((n + 1) * sizeof *exh_rprog);
    for (int a = 0; a < n; a++) { exh_roots[a] = &gstates[ids[a]]; exh_rframe[a] = gcells[ids[a]].frame; exh_rprog[a] = gcells[ids[a]].prog; }
    if (g_best >= 0) exh_best = g_best;
    int best = exh_run(n, t0);
    if (best < (1 << 30) && exh_best_root >= 0 && (g_best < 0 || best < g_best)) {
      const GCell *c = &gcells[ids[exh_best_root]];
      g_best = best; g_best_path = realloc(g_best_path, best - f0);
      memcpy(g_best_path, c->path, c->frame - f0); memcpy(g_best_path + (c->frame - f0), exh_best_path, exh_best_len);
    }
  }
  if (g_best < 0) { printf("no goal found (TAS f%d)\n", tas_goal); return 1; }
  static uint8_t path_in[MAX_FRAMES * 8]; int count = 0;
  for (int k = 0; k <= f0; k++) path_in[count++] = mv->p1[k];
  for (int k = 0; k < g_best - f0; k++) path_in[count++] = g_best_path[k];
  static NES n; nes_power(&n); nes_reset(&n);
  for (int k = 0; k < count; k++) { nes_frame(&n, path_in[k], 0); if (n.err) break; }
  int ok = !n.err && goal_met(&n) && ((goal_kind != G_PIPE && goal_kind != G_SIDE) || destination_ok(&n));
  printf("GOAL on f%d (TAS f%d, %+d), plain replay %s (%.0f s)\n", g_best, tas_goal, g_best - tas_goal, ok ? "agrees" : "DISAGREES", now() - t0);
  if (!ok) return 2;
  if (getenv("OUT")) write_movie(getenv("OUT"), mv, path_in, count);
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 10 || nes_load_rom(argv[1])) {
    fprintf(stderr, "usage: seg rom movie f0 frames width per_cell threads waypoint... goal\n"); return 2;
  }
  Movie mv; char err[128];
  if (movie_load(argv[2], &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
  int f0 = atoi(argv[3]), frames = atoi(argv[4]);
  width = atoi(argv[5]); per_cell = atoi(argv[6]); threads = atoi(argv[7]);
  if (movie_rom_matches(&mv, argv[1]) != 1) {
    fprintf(stderr, "movie ROM checksum must match\n"); return 2;
  }
  if (f0 < 0 || f0 >= mv.n || f0 >= MAX_FRAMES * 8 || frames < 1 ||
      frames >= MAX_FRAMES || frames >= MAX_FRAMES * 8 - f0 ||
      width < 1 || per_cell < 1 || threads < 1 || threads > 64) return 2;
  for (int f = 0; f <= f0; f++) {
    if (mv.p2[f] || mv.cmd[f]) {
      fprintf(stderr, "unsupported input in movie prefix at frame %d\n", f); return 2;
    }
  }
  for (int a = 8; a < argc - 1; a++) {
    int v;
    if (sscanf(argv[a], "x>=%d", &v) == 1) way[nway].kind = W_XGE;
    else if (sscanf(argv[a], "x<=%d", &v) == 1) way[nway].kind = W_XLE;
    else if (sscanf(argv[a], "cam>=%d", &v) == 1) way[nway].kind = W_CAM;
    else { fprintf(stderr, "bad waypoint %s\n", argv[a]); return 2; }
    way[nway++].v = v;
    if (nway == MAX_WAY) break;
  }
  const char *g = argv[argc - 1];
  if (!strncmp(g, "pipe", 4)) goal_kind = G_PIPE;
  else if (!strncmp(g, "side", 4)) goal_kind = G_SIDE;
  else if (!strcmp(g, "axe")) goal_kind = G_AXE;
  else if (!strcmp(g, "exit")) goal_kind = G_EXIT;
  else { fprintf(stderr, "bad goal %s\n", g); return 2; }
  const char *colon = strchr(g, ':');
  if (colon) goal_ptr = (int)strtol(colon + 1, NULL, 16);
  if (getenv("GOALX")) goal_x = atoi(getenv("GOALX"));
  else if (nway) goal_x = way[nway - 1].kind == W_CAM ? way[nway - 1].v + 112 : way[nway - 1].v;
  if (getenv("TOP")) top_speed = atoi(getenv("TOP"));
  if (getenv("NODOWN")) use_down = 0;
  if (getenv("GOALY")) goal_y = atoi(getenv("GOALY"));
  if (getenv("GOALYWIN")) goal_y_win = atoi(getenv("GOALYWIN"));
  if (getenv("LATE")) late = atoi(getenv("LATE"));
  if (getenv("LAG")) lag_weight = atof(getenv("LAG"));
  if (getenv("LAGMAX")) lag_max = atoi(getenv("LAGMAX"));
  if (getenv("ENDGAME")) endgame = atoi(getenv("ENDGAME"));
  if (getenv("ENTRYV")) entry_v = atoi(getenv("ENTRYV"));
  if (getenv("ENDCAP")) endcap = atoi(getenv("ENDCAP"));
  no_lr = getenv("NOLR") != NULL;
  tracking = getenv("TRACK") != NULL;
  if (getenv("CELLY")) cell_yshift = atoi(getenv("CELLY"));
  if (getenv("CELLV")) cell_vshift = atoi(getenv("CELLV"));
  if (getenv("CELLF")) cell_frac_bits = atoi(getenv("CELLF"));
  if (getenv("CELLX")) cell_sub_bits = atoi(getenv("CELLX"));
  key_init();
  size_t cap = (size_t)width * (nway + 1) * (lag_weight > 0 ? 4 : 1) + (size_t)endcap;
  endpool = malloc((cap * 24 + 1) * sizeof(Child));
  cur = malloc(cap * sizeof *cur); nxt = malloc(cap * sizeof *nxt);
  cur_prog = calloc(cap, sizeof(Prog)); nxt_prog = calloc(cap, sizeof(Prog));
  picked = malloc(cap * sizeof(Child));
  tchild = calloc(threads, sizeof *tchild); tn = calloc(threads, sizeof *tn); tcap = calloc(threads, sizeof *tcap);
  for (int t = 0; t < threads; t++) { tcap[t] = 1 << 16; tchild[t] = malloc(tcap[t] * sizeof(Child)); }
  if (!cur || !nxt || !picked) { fprintf(stderr, "out of memory\n"); return 2; }

  static NES s0;
  nes_power(&s0); nes_reset(&s0);
  for (int f = 0; f <= f0; f++) {
    fast_frame(&s0, mv.p1[f]);
    if (s0.err) { fprintf(stderr, "unsupported execution replaying the TAS at frame %d\n", f); return 2; }
  }
  cur[0] = s0;
  cur_n = 1;
  lives0 = s0.ram[0x75A]; level0 = s0.ram[0x75F] << 8 | s0.ram[0x75C];
  cur_prog[0] = advance(&s0, &s0, (Prog){0});
  // The TAS's own frame for this goal, for comparison.
  int tas_goal = -1, tas_lb_at = -1; double tas_lb_max = 0;
  {
    static NES t; t = s0; Prog p = cur_prog[0];
    for (int f = f0 + 1; f < mv.n && f <= f0 + frames; f++) {
      static NES b; b = t;
      fast_frame(&t, mv.p1[f]);
      p = advance(&b, &t, p);
      if (p.way >= nway && goal_met(&t) && ((goal_kind != G_PIPE && goal_kind != G_SIDE) || destination_ok(&t))) { tas_goal = f; break; }
      if (t.ram[0x0E] == 8) { double lb = f + lower_bound(&t, p); if (lb > tas_lb_max) { tas_lb_max = lb; tas_lb_at = f; } }
    }
  }
  printf("start s_%d x=%d; goal %s, %d waypoints, goal x %d; the TAS reaches it on f%d\n", f0, xpix(&s0), g, nway, goal_x, tas_goal);
  if (getenv("LBCHECK")) { printf("lower bound on the TAS's path: largest frame+bound f%.1f (at f%d), TAS goal f%d: %s\n", tas_lb_max, tas_lb_at, tas_goal, tas_lb_max <= tas_goal ? "holds" : "VIOLATED"); return 0; }
  if (getenv("BOUND")) {
    bound = !strcmp(getenv("BOUND"), "tas") ? tas_goal : atoi(getenv("BOUND"));
    if (bound < 0) { fprintf(stderr, "BOUND=tas, but the TAS doesn't reach the goal in the horizon\n"); return 2; }
    if (getenv("BSLACK")) bound += atoi(getenv("BSLACK"));
    printf("bound: goal by f%d; the start state's lower bound is f%.1f\n", bound, f0 + lower_bound(&s0, cur_prog[0]));
  }
  if (getenv("DOM")) { dom_mode = atoi(getenv("DOM")); dommask = (1u << 25) - 1; domtab = calloc(dommask + 1, sizeof *domtab); }
  if (getenv("EXH")) { exh_k = atoi(getenv("EXH")); if (bound < 0) { fprintf(stderr, "EXH needs BOUND\n"); return 2; } }
  if (getenv("GOX")) return go_explore(&mv, f0, frames, &s0, cur_prog[0], tas_goal);
  fflush(stdout);
  double t0 = now();
  int found = -1, first[MAX_WAY + 1];
  for (int q = 0; q <= MAX_WAY; q++) first[q] = -1;
  for (int d = 0; d < frames; d++) {
    int f = f0 + 1 + d;  // the frame being played
    cur_frame = f;
    for (int t = 0; t < threads; t++) tn[t] = 0;
    run_threads(expand);
    if (goal_at >= 0) {
      static uint8_t path_in[MAX_FRAMES * 8];
      int count = 0;
      for (int k = 0; k <= f0; k++) path_in[count++] = mv.p1[k];
      static uint8_t tail[MAX_FRAMES];
      uint32_t i = goal_parent;
      tail[d] = goal_input;
      for (int l = d - 1; l >= 0; l--) { tail[l] = inp[l][i]; i = par[l][i]; }
      for (int l = 0; l <= d; l++) path_in[count++] = tail[l];
      // plain replay from power-on
      static NES n; nes_power(&n); nes_reset(&n);
      int ok = -1;
      for (int k = 0; k < count; k++) { nes_frame(&n, path_in[k], 0); if (n.err) break; }
      if (!n.err && goal_met(&n) && ((goal_kind != G_PIPE && goal_kind != G_SIDE) || destination_ok(&n))) ok = count - 1;
      printf("GOAL on f%d (TAS f%d, %+d), plain replay %s (%.0f s)\n  inputs from f%d:", f, tas_goal, f - tas_goal,
             ok == f ? "agrees" : "DISAGREES", now() - t0, f0 + 1);
      for (int l = 0; l <= d; l++) printf(" %02X", tail[l]);
      printf("\n");
      if (ok != f) return 2;
      if (getenv("OUT")) write_movie(getenv("OUT"), &mv, path_in, count);
      found = f;
      break;
    }
    size_t total = 0;
    for (int t = 0; t < threads; t++) total += tn[t];
    Child *all = malloc((total + 1) * sizeof(Child));
    size_t m = 0;
    for (int t = 0; t < threads; t++) { memcpy(all + m, tchild[t], tn[t] * sizeof(Child)); m += tn[t]; }
    // The TAS's state after this frame, to see whether the search keeps it.
    static NES tas, tas_before; static Prog tas_prog; static int tas_alive = 1, tas_match = 0;
    if (d == 0) { tas = s0; tas_prog = cur_prog[0]; }
    uint64_t tas_h = 0;
    if (tracking && tas_alive && f >= mv.n) tas_alive = 0;
    if (tracking && tas_alive) {
      tas_before = tas; fast_frame(&tas, mv.p1[f]); tas_prog = advance(&tas_before, &tas, tas_prog);
      tas_h = key_hash(&tas);
    }
    qsort(all, total, sizeof(Child), by_hash);
    size_t u = 0;
    for (size_t i = 0; i < total; i++) if (!u || all[u - 1].hash != all[i].hash) all[u++] = all[i];
    if (dom_mode) {  // the same situation was already held on an earlier frame
      size_t v = 0;
      for (size_t i = 0; i < u; i++) { if (dom_seen(all[i].dom)) { dom_cut++; continue; } all[v++] = all[i]; }
      u = v;
    }
    int64_t tas_score = 0; uint32_t tas_cell = 0; int tas_seen = 0, tas_rank = -1;
    if (tracking && tas_alive) for (size_t i = 0; i < u; i++) if (all[i].hash == tas_h) { tas_seen = 1; tas_score = all[i].score; tas_cell = all[i].cell; }
    // Not generated although a kept state matched the TAS on every key byte: a byte outside the key
    // decides the frame. Show where that state and the TAS's differ.
    if (tracking && tas_alive && !tas_seen && d > 0) {
      printf("TRACK f%d: the kept state that matched the TAS's on the key bytes differs elsewhere (TAS/kept):", f);
      const NES *m = &cur[tas_match];
      for (int a = 0; a < 0x800; a++) if (m->ram[a] != tas_before.ram[a]) printf(" %03X=%02X/%02X", a, tas_before.ram[a], m->ram[a]);
      printf("\n");
    }
    qsort(all, u, sizeof(Child), by_cell);
    // Per cell: the best half of per_cell, then the rest spread evenly over the cell's remaining
    // members. Near-ties (states that differ in a speed fraction or a scroll byte the score can't
    // weigh) then survive in proportion, rather than by which side of the tie-break they fall.
    // Endgame states (within ENDGAME px of the goal) skip the caps: every distinct one is kept, up to
    // ENDCAP, so the destination check can decide among more candidates.
    size_t w = 0, ne = 0;
    for (size_t i = 0; i < u; i++) if (all[i].end) { endpool[ne++] = all[i]; all[i].end = 2; }
    if (ne > (size_t)endcap) { qsort(endpool, ne, sizeof(Child), by_score); ne = endcap; }
    for (size_t i = 0; i < u;) {
      size_t j = i;
      while (j < u && all[j].cell == all[i].cell) j++;
      size_t m = j - i, keep = (size_t)per_cell, top = keep / 2;
      if (all[i].end == 2) { i = j; continue; }
      for (size_t r = 0; r < m; r++) if (all[i + r].hash == tas_h && tas_seen) tas_rank = (int)r;
      if (m <= keep) { for (size_t r = 0; r < m; r++) all[w++] = all[i + r]; }
      else {
        for (size_t r = 0; r < top; r++) all[w++] = all[i + r];
        size_t rest = keep - top, pool = m - top;
        for (size_t q = 0; q < rest; q++) all[w++] = all[i + top + q * pool / rest];
      }
      i = j;
    }
    qsort(all, w, sizeof(Child), by_score);
    // Each waypoint level keeps up to `width` states, and a level
    // stays in the beam until `late` frames after the next level is first reached.
    for (size_t i = 0; i < w; i++) if (all[i].prog.way <= nway && first[all[i].prog.way] < 0) {
      first[all[i].prog.way] = f;
      printf("f%d: first reached waypoint level %d\n", f, all[i].prog.way);
    }
    picked_n = 0;
    uint32_t count[MAX_WAY + 1][4] = {{0}};
    for (size_t i = 0; i < w; i++) {
      int lv = all[i].prog.way, nextf = -1, bd = all[i].band;
      for (int q = lv + 1; q <= nway; q++) if (first[q] >= 0) { nextf = first[q]; break; }
      if (nextf >= 0 && f > nextf + late) continue;
      if (all[i].end == 2) continue;
      if (count[lv][bd] >= (uint32_t)width) continue;
      count[lv][bd]++;
      picked[picked_n++] = all[i];
    }
    for (size_t i = 0; i < ne; i++) picked[picked_n++] = endpool[i];
    if (dom_mode) for (uint32_t i = 0; i < picked_n; i++) dom_add(picked[i].dom);
    int64_t last = picked_n ? picked[picked_n - 1].score : 0; int last_way = picked_n ? picked[picked_n - 1].prog.way : 0;
    free(all);
    par[d] = malloc(picked_n * sizeof(uint32_t) + 4); inp[d] = malloc(picked_n + 1);
    for (uint32_t i = 0; i < picked_n; i++) { par[d][i] = picked[i].parent; inp[d][i] = picked[i].input; }
    run_threads(rebuild);
    NES *ts = cur; cur = nxt; nxt = ts;
    Prog *tp = cur_prog; cur_prog = nxt_prog; nxt_prog = tp;
    cur_n = picked_n;
    if (exh_k && bound >= 0 && f == bound - exh_k) {
      exh_roots = malloc(cur_n * sizeof *exh_roots); exh_rframe = malloc(cur_n * sizeof *exh_rframe); exh_rprog = malloc(cur_n * sizeof *exh_rprog);
      for (uint32_t i = 0; i < cur_n; i++) { exh_roots[i] = &cur[i]; exh_rframe[i] = f; exh_rprog[i] = cur_prog[i]; }
      int best = exh_run(cur_n, t0);
      if (best >= (1 << 30)) { printf("no kept state at f%d reaches the goal by f%d\n", f, bound); found = -1; break; }
      static uint8_t path_in[MAX_FRAMES * 8], tail[MAX_FRAMES]; int count = 0;
      for (int k = 0; k <= f0; k++) path_in[count++] = mv.p1[k];
      uint32_t i = exh_best_root;
      for (int l = d; l >= 0; l--) { tail[l] = inp[l][i]; i = par[l][i]; }
      for (int l = 0; l <= d; l++) path_in[count++] = tail[l];
      for (int l = 0; l < exh_best_len; l++) path_in[count++] = exh_best_path[l];
      static NES n; nes_power(&n); nes_reset(&n);
      for (int k = 0; k < count; k++) { nes_frame(&n, path_in[k], 0); if (n.err) break; }
      int ok = !n.err && goal_met(&n) && ((goal_kind != G_PIPE && goal_kind != G_SIDE) || destination_ok(&n));
      printf("GOAL on f%d (TAS f%d, %+d), plain replay %s (%.0f s)\n", best, tas_goal, best - tas_goal, ok ? "agrees" : "DISAGREES", now() - t0);
      if (!ok) return 2;
      if (getenv("OUT")) write_movie(getenv("OUT"), &mv, path_in, count);
      found = best;
      break;
    }
    // Kept means some state equals the TAS's on every key byte.
    if (tracking && tas_alive) {
      int kept = 0;
      for (uint32_t i = 0; i < cur_n && !kept; i++) {
        int k = 0;
        const NES *v = &cur[i];
        for (; k < key_n; k++) if (v->ram[key_bytes[k]] != tas.ram[key_bytes[k]]) break;
        if (k == key_n) { kept = 1; tas_match = i; }
      }
      if (!kept) {
        tas_alive = 0;
        printf("TRACK f%d: the TAS's state is %s", f, !tas_seen ? "not generated (an input outside the alphabet, or a state the search had already lost)" :
               "cut by the cell cap or the width");
        if (tas_seen) printf(": rank %d in cell %08X, score %.1f frames against the last kept %.1f (TAS x=%d y=%d v=%d way %d)",
                             tas_rank, tas_cell, -(double)(tas_score - (int64_t)tas_prog.way * ((int64_t)1 << 50)) / 65536,
                             -(double)(last - (int64_t)last_way * ((int64_t)1 << 50)) / 65536,
                             xpix(&tas), tas.ram[0xCE], (int8_t)tas.ram[0x57], tas_prog.way);
        printf("\n");
        // what tells the TAS's state apart from the best one kept in its cell
        if (tas_seen) for (uint32_t i = 0; i < picked_n; i++) if (picked[i].cell == tas_cell) {
          static NES c; c = cur[i];
          printf("  differs from the cell's best (TAS/best):");
          for (int k = 0; k < key_n; k++) if (c.ram[key_bytes[k]] != tas.ram[key_bytes[k]])
            printf(" %03X=%02X/%02X", key_bytes[k], tas.ram[key_bytes[k]], c.ram[key_bytes[k]]);
          printf("\n");
          break;
        }
        fflush(stdout);
      }
    }
    if (!cur_n) { printf("f%d: no states left\n", f); break; }
    if (d % 20 == 0 || getenv("VERBOSE")) {
      const NES *b = &cur[0];
      if (wrong_pipe) printf("f%d: %ld pipe entries with another AreaPointer so far (first $%02X)\n", f, wrong_pipe, wrong_ptr_seen & 0xFF);
      if (lag_weight > 0) {
        int most = -999;
        for (uint32_t i = 0; i < cur_n; i++) { const NES *v = &cur[i]; int pos = xpix(v) - cam(v) - 112; if (pos > most) most = pos; }
        printf("f%d: most camera lag kept %d px\n", f, most);
      }
      if (bound >= 0 || dom_mode) printf("f%d: %ld children past the bound, %ld dominated so far\n", f, bound_cut, dom_cut);
      printf("f%d: %zu children, %zu distinct, kept %u; best way %d x=%d.%02X y=%d v=%d cam=%d est %.1f frames (%.0f s)\n", f, total, u,
             cur_n, cur_prog[0].way, xpix(b) + 1024 * cur_prog[0].loops, b->ram[0x400], b->ram[0xCE], (int8_t)b->ram[0x57], cam(b),
             -(double)(picked[0].score - (int64_t)cur_prog[0].way * ((int64_t)1 << 50)) / 65536, now() - t0);
      fflush(stdout);
    }
  }
  if (found < 0) printf("no goal within %d frames (TAS f%d)\n", frames, tas_goal);
  printf("done in %.0f s\n", now() - t0);
  return found >= 0 ? 0 : 1;
}
