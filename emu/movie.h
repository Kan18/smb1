// Shared FM2 reader for the C tools, with startup alignment and a ROM checksum check.
//
// For the target movie, callers power on and reset, then play the frames after
// its initial idle reset row. This matches `Smb.initial` and `tasInputs` in Lean.
#ifndef MOVIE_H
#define MOVIE_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  int n;                    // frames
  uint8_t *cmd, *p1, *p2;   // per frame: command bits (1 reset, 2 power), controllers 1 and 2
  char checksum[64];        // romChecksum header value ("base64:..."), or ""
  int uses_p2;              // some frame presses a controller-2 button
} Movie;

// A controller field: exactly 8 characters, each '.' or ' ' (released) or the button's letter
// in the order RLDUTSBA, followed by '|'. Returns -1 if malformed.
static inline int movie_pad(const char *s) {
  uint8_t b = 0;
  for (int i = 0; i < 8; i++) {
    if (s[i] == '.' || s[i] == ' ') continue;
    if (s[i] != "RLDUTSBA"[i]) return -1;
    b |= 1 << (7 - i);
  }
  return s[8] == '|' ? b : -1;
}

// Returns 0 on success. On failure, writes a message to err (at least 128 bytes).
// Frame lines have the form "|cmd|pad1|pad2|...". The second pad may be absent or empty.
static inline int movie_load(const char *path, Movie *m, char *err) {
  memset(m, 0, sizeof *m);
  FILE *f = fopen(path, "r");
  if (!f) { snprintf(err, 128, "cannot open %s", path); return 1; }
  int cap = 1024;
  m->cmd = malloc(cap); m->p1 = malloc(cap); m->p2 = malloc(cap);
  char line[512];
  while (fgets(line, sizeof line, f)) {
    if (!strchr(line, '\n') && !feof(f)) { snprintf(err, 128, "line too long near frame %d", m->n); fclose(f); return 1; }
    if (!strncmp(line, "romChecksum ", 12)) {
      snprintf(m->checksum, sizeof m->checksum, "%s", line + 12);
      m->checksum[strcspn(m->checksum, "\r\n")] = 0;
      continue;
    }
    if (line[0] != '|') continue;
    char *end;
    long cmd = strtol(line + 1, &end, 10);
    int p1 = -1, p2 = 0;
    if (end != line + 1 && *end == '|') p1 = movie_pad(end + 1);
    if (p1 >= 0) {
      char *f2 = end + 10;  // controller 2's field, or the end of the line when port 2 is absent
      if (*f2 && *f2 != '|' && *f2 != '\n' && *f2 != '\r') p2 = movie_pad(f2);
    }
    if (p1 < 0 || p2 < 0) { snprintf(err, 128, "malformed frame %d", m->n); fclose(f); return 1; }
    if (cmd & ~3L) { snprintf(err, 128, "unsupported command %ld at frame %d", cmd, m->n); fclose(f); return 1; }
    if (m->n == cap) { cap *= 2; m->cmd = realloc(m->cmd, cap); m->p1 = realloc(m->p1, cap); m->p2 = realloc(m->p2, cap); }
    m->cmd[m->n] = cmd;
    m->p1[m->n] = p1;
    m->p2[m->n] = p2;
    if (p2) m->uses_p2 = 1;
    m->n++;
  }
  int bad = ferror(f);
  fclose(f);
  if (bad) { snprintf(err, 128, "read error in %s", path); return 1; }
  if (!m->n) { snprintf(err, 128, "no frames in %s", path); return 1; }
  return 0;
}

// Drop the idle first row, which may include a reset command. The caller powers on
// and resets before replay. Later commands remain in the movie.
static inline int movie_align(Movie *m, char *err) {
  if (m->n == 0 || m->p1[0] || m->p2[0] || (m->cmd[0] & 2)) {
    snprintf(err, 128, "startup conversion requires an idle first frame (reset or nothing)");
    return 1;
  }
  m->n--;
  memmove(m->cmd, m->cmd + 1, m->n); memmove(m->p1, m->p1 + 1, m->n); memmove(m->p2, m->p2 + 1, m->n);
  return 0;
}

// --- MD5 (RFC 1321), for the movie's ROM checksum: base64 of MD5(PRG+CHR) ---
static inline void movie_md5(const uint8_t *msg, size_t len, uint8_t out[16]) {
  static const uint32_t K[64] = {
    0xd76aa478,0xe8c7b756,0x242070db,0xc1bdceee,0xf57c0faf,0x4787c62a,0xa8304613,0xfd469501,
    0x698098d8,0x8b44f7af,0xffff5bb1,0x895cd7be,0x6b901122,0xfd987193,0xa679438e,0x49b40821,
    0xf61e2562,0xc040b340,0x265e5a51,0xe9b6c7aa,0xd62f105d,0x02441453,0xd8a1e681,0xe7d3fbc8,
    0x21e1cde6,0xc33707d6,0xf4d50d87,0x455a14ed,0xa9e3e905,0xfcefa3f8,0x676f02d9,0x8d2a4c8a,
    0xfffa3942,0x8771f681,0x6d9d6122,0xfde5380c,0xa4beea44,0x4bdecfa9,0xf6bb4b60,0xbebfbc70,
    0x289b7ec6,0xeaa127fa,0xd4ef3085,0x04881d05,0xd9d4d039,0xe6db99e5,0x1fa27cf8,0xc4ac5665,
    0xf4292244,0x432aff97,0xab9423a7,0xfc93a039,0x655b59c3,0x8f0ccc92,0xffeff47d,0x85845dd1,
    0x6fa87e4f,0xfe2ce6e0,0xa3014314,0x4e0811a1,0xf7537e82,0xbd3af235,0x2ad7d2bb,0xeb86d391};
  static const uint8_t R[64] = {7,12,17,22,7,12,17,22,7,12,17,22,7,12,17,22,5,9,14,20,5,9,14,20,
    5,9,14,20,5,9,14,20,4,11,16,23,4,11,16,23,4,11,16,23,4,11,16,23,6,10,15,21,6,10,15,21,6,10,15,21,6,10,15,21};
  uint32_t h[4] = {0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476};
  size_t total = ((len + 8) / 64 + 1) * 64;
  uint8_t *buf = calloc(total, 1);
  memcpy(buf, msg, len); buf[len] = 0x80;
  uint64_t bits = (uint64_t)len * 8;
  for (int i = 0; i < 8; i++) buf[total - 8 + i] = bits >> (8 * i);
  for (size_t off = 0; off < total; off += 64) {
    uint32_t w[16];
    for (int i = 0; i < 16; i++)
      w[i] = buf[off + 4*i] | buf[off + 4*i + 1] << 8 | buf[off + 4*i + 2] << 16 | (uint32_t)buf[off + 4*i + 3] << 24;
    uint32_t a = h[0], b = h[1], c = h[2], d = h[3];
    for (int i = 0; i < 64; i++) {
      uint32_t F; int g;
      if (i < 16) { F = (b & c) | (~b & d); g = i; }
      else if (i < 32) { F = (d & b) | (~d & c); g = (5*i + 1) % 16; }
      else if (i < 48) { F = b ^ c ^ d; g = (3*i + 5) % 16; }
      else { F = c ^ (b | ~d); g = (7*i) % 16; }
      uint32_t t = d; d = c; c = b;
      uint32_t x = a + F + K[i] + w[g];
      b = b + ((x << R[i]) | (x >> (32 - R[i])));
      a = t;
    }
    h[0] += a; h[1] += b; h[2] += c; h[3] += d;
  }
  free(buf);
  for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) out[4*i + j] = h[i] >> (8 * j);
}

// 1 if the movie's romChecksum matches the iNES file's PRG+CHR, 0 if not, -1 if unknown.
static inline int movie_rom_matches(const Movie *m, const char *rom_path) {
  if (strncmp(m->checksum, "base64:", 7)) return -1;
  FILE *f = fopen(rom_path, "rb");
  if (!f) return -1;
  static uint8_t raw[0x10000];
  size_t len = fread(raw, 1, sizeof raw, f);
  fclose(f);
  if (len <= 16) return -1;
  uint8_t d[16];
  movie_md5(raw + 16, len - 16, d);
  static const char *b64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  char enc[32]; int k = 0;
  for (int i = 0; i < 16; i += 3) {
    uint32_t v = d[i] << 16 | (i + 1 < 16 ? d[i + 1] << 8 : 0) | (i + 2 < 16 ? d[i + 2] : 0);
    enc[k++] = b64[v >> 18 & 63]; enc[k++] = b64[v >> 12 & 63];
    enc[k++] = i + 1 < 16 ? b64[v >> 6 & 63] : '=';
    enc[k++] = i + 2 < 16 ? b64[v & 63] : '=';
  }
  enc[k] = 0;
  return !strcmp(m->checksum + 7, enc);
}

#endif
