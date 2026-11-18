// Strict input helpers shared by the two replay tools.
#ifndef ENGINE_BOUNDS_INPUT_H
#define ENGINE_BOUNDS_INPUT_H
#include <errno.h>
#include <limits.h>
#include <ctype.h>
static unsigned number(const char *s, int base, unsigned limit) {
  char *end;
  errno = 0;
  unsigned long v = strtoul(s, &end, base);
  if (!*s || *s == '-' || *s == '+' || isspace((unsigned char)*s) || *end || errno || v > limit) {
    fprintf(stderr, "invalid number: %s\n", s); exit(2);
  }
  return (unsigned)v;
}
static void window(const Movie *m, const char *rom, int first, int end) {
  if (movie_rom_matches(m, rom) != 1) {
    fprintf(stderr, "missing or mismatched movie ROM checksum\n"); exit(2);
  }
  if (first >= end || end > m->n) {
    fprintf(stderr, "require 0 <= FIRST < END <= aligned movie length (%d)\n", m->n); exit(2);
  }
}
#endif
