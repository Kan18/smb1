// Exhaustive breadth-first search over controller-1 inputs (all 256 byte values per
// frame; controller 2 idle; no resets after frame 0), merging states only when the full
// machine state is byte-identical after canonicalisation.
//
// Stack memory is retained. A moving stack pointer does not justify erasing bytes.
//
// RAM bytes listed in the dead-byte file are also zeroed at frame boundaries. That is
// sound only if, in every explored frame, each such byte is written before it is read;
// every frame run is checked, and on a violation the byte is moved to the live set and
// the search restarts from scratch (the dead file is rewritten).
//
// usage: bfs rom.nes max_frames dead.txt [movie.fm2 start_frame]
//   Without a movie: start from power-on (+ reset on frame 0, as in the TAS) and report
//   the first frame at which any state has OperMode == 1 (gameplay started).
//   With a movie: replay exactly start_frame aligned inputs under the project's fixed
//   reset/controller-2-idle rules, then search for the final-victory predicate.
//   Depth zero is checked. These C results are experiments, not Lean certificates.
#include "nes.h"
#include "movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>
#include <ctype.h>

typedef struct { uint64_t h; NES s; } Entry;
typedef struct { Entry *e; size_t cap, n; } Set;

static uint8_t dead[0x800], acc[0x800];
// At most 32,768 entries per layer; growth temporarily retains the old table too.
// A larger frontier is unresolved, never evidence that no route exists.
enum { MAX_SET_CAP = 65536 };

static void canon(NES *n) {
  for (int a = 0; a < 0x800; a++) if (dead[a]) n->ram[a] = 0;
  // Cycle parity and bus-decay timestamps affect future execution. Keep them.
  n->frame = 0; n->polls = 0; n->err_pc = 0; n->frame_done = 0;
  n->pad[0] = n->pad[1] = 0;
}

static uint64_t hash(const NES *n) {
  const uint8_t *p = (const uint8_t *)n;
  uint64_t h = 1469598103934665603ULL;
  for (size_t i = 0; i < sizeof *n; i++) { h ^= p[i]; h *= 1099511628211ULL; }
  return h | 1;  // 0 marks an empty slot
}

static void set_init(Set *s, size_t cap) {
  if (cap > MAX_SET_CAP) {
    fprintf(stderr, "state capacity reached; search unresolved\n");
    exit(1);
  }
  s->cap = cap; s->n = 0; s->e = calloc(cap, sizeof(Entry));
  if (!s->e) { fprintf(stderr, "state allocation failed; search unresolved\n"); exit(1); }
}
static void set_free(Set *s) { free(s->e); s->e = NULL; s->n = s->cap = 0; }

static int set_insert(Set *s, const NES *n);
static void set_grow(Set *s) {
  Set t; set_init(&t, s->cap * 2);
  for (size_t i = 0; i < s->cap; i++) if (s->e[i].h) set_insert(&t, &s->e[i].s);
  free(s->e); *s = t;
}
static int set_insert(Set *s, const NES *n) {
  uint64_t h = hash(n);
  size_t i = h % s->cap;
  while (s->e[i].h) {
    if (s->e[i].h == h && !memcmp(&s->e[i].s, n, sizeof *n)) return 0;
    i = (i + 1) % s->cap;
  }
  // Check for a duplicate before growing: a full frontier may still merge this state.
  if ((s->n + 1) * 2 > s->cap) { set_grow(s); return set_insert(s, n); }
  s->e[i].h = h; s->e[i].s = *n; s->n++;
  return 1;
}

static int frame_arg(const char *text, int *out) {
  char *end;
  errno = 0;
  long value = strtol(text, &end, 10);
  if (errno || end == text || *end || value < 0 || value > INT_MAX) return 1;
  *out = (int)value;
  return 0;
}

static int goal(const NES *n, int victory) {
  return victory ? nes_final_victory(n) : n->ram[0x770] == 1;
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 6) { fprintf(stderr, "usage: %s rom max_frames dead.txt [movie start_frame]\n", argv[0]); return 2; }
  int max_frames, f0 = 0, victory = argc == 6;
  if (frame_arg(argv[2], &max_frames) || (victory && frame_arg(argv[5], &f0))) {
    fprintf(stderr, "frame bounds must be nonnegative integers\n"); return 2;
  }
  if (nes_load_rom(argv[1])) { fprintf(stderr, "rom load failed\n"); return 2; }
  FILE *df = fopen(argv[3], "r");
  if (!df) { perror("dead-byte file"); return 2; }
  char token[32];
  int read;
  while ((read = fscanf(df, "%31s", token)) == 1) {
    int delimiter = fgetc(df);
    if (delimiter != EOF && !isspace((unsigned char)delimiter)) {
      fprintf(stderr, "dead-byte address token too long\n"); fclose(df); return 2;
    }
    char *end;
    errno = 0;
    unsigned long a = strtoul(token, &end, 16);
    if (errno || end == token || *end || a >= 0x800) {
      fprintf(stderr, "invalid dead-byte address\n"); fclose(df); return 2;
    }
    dead[a] = 1;
  }
  if (read != EOF || ferror(df)) { fprintf(stderr, "invalid dead-byte file\n"); fclose(df); return 2; }
  fclose(df);
  // Goal observations count as reads too, even if the CPU does not read a byte.
  dead[0x770] = dead[0x75f] = dead[0x75c] = 0;
  static NES entry;
  nes_power(&entry);
  nes_reset(&entry);
  if (victory) {
    Movie mv;
    char err[128];
    if (movie_load(argv[4], &mv, err) || movie_align(&mv, err)) { fprintf(stderr, "%s\n", err); return 2; }
    if (movie_rom_matches(&mv, argv[1]) != 1) { fprintf(stderr, "movie ROM checksum missing or mismatched\n"); return 2; }
    if (f0 > mv.n) { fprintf(stderr, "start frame exceeds aligned movie length %d\n", mv.n); return 2; }
    for (int fr = 0; fr < f0; fr++) {
      if (mv.cmd[fr] || mv.p2[fr]) { fprintf(stderr, "movie prefix violates reset/controller rules at frame %d\n", fr); return 2; }
      nes_frame(&entry, mv.p1[fr], 0);
      if (entry.err) { fprintf(stderr, "unsupported movie prefix at frame %d; search unresolved\n", fr); return 1; }
    }
    free(mv.cmd); free(mv.p1); free(mv.p2);
  }
  if (entry.err) { fprintf(stderr, "unsupported entry; search unresolved\n"); return 1; }
  printf("goal=%s; entry after %d aligned inputs; horizon=%d\n",
    victory ? "final victory" : "OperMode=1", f0, max_frames);
  if (goal(&entry, victory)) { printf("goal already reached at depth 0\n"); return 0; }
  nes_acc = acc;
restart:;
  NES start = entry;
  canon(&start);
  Set cur; set_init(&cur, 1024);
  set_insert(&cur, &start);
  for (int depth = 0; depth < max_frames; depth++) {
    long long f = (long long)f0 + depth;
    Set next; set_init(&next, 1024);
    int reached = 0;
    unsigned long long runs = 0;
    for (size_t i = 0; i < cur.cap; i++) {
      if (!cur.e[i].h) continue;
      for (int in = 0; in < 256; in++) {
        NES n = cur.e[i].s;
        memset(acc, 0, sizeof acc);
        nes_frame(&n, in, 0);
        runs++;
        for (int b = 0; b < 0x800; b++) if (dead[b] && acc[b] == 2) {
          printf("frame %lld: byte $%03X read before written; marking live and restarting\n", f, b);
          dead[b] = 0;
          FILE *o = fopen(argv[3], "w");
          if (!o) { perror("dead-byte file"); return 2; }
          for (int k = 0; k < 0x800; k++) if (dead[k]) fprintf(o, "%03x\n", k);
          if (fclose(o)) { perror("dead-byte file"); return 2; }
          set_free(&cur);
          set_free(&next);
          goto restart;
        }
        if (n.err) { printf("frame %lld: unsupported execution (error %d) near %04X; search unresolved\n", f, n.err, n.err_pc); return 1; }
        if (goal(&n, victory)) reached = 1;
        canon(&n);
        set_insert(&next, &n);
      }
    }
    printf("depth %d (after frame %lld): %zu distinct states (%llu frame runs)%s\n", depth + 1, f, next.n, runs,
           reached ? "  <-- goal reached" : "");
    fflush(stdout);
    set_free(&cur);
    cur = next;
    if (reached) { set_free(&cur); return 0; }
  }
  set_free(&cur);
  printf("horizon completed: no goal at any depth from 0 through %d\n", max_frames);
  return 0;
}
