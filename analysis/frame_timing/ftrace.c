// Per-frame trace of the transition state and NMI handler timing. Uses emu/nes.c unchanged.
// usage: ftrace rom movie [--tas-startup] > trace.csv
// Columns: see the header line. Times are CPU cycles since the handler's NMI entry.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NMI_ENTRY 0x8082
#define ENDLESS   0x8057
#define SKIP_S0   0x815C   // SkipSprite0
#define S0_CLR    0x813D
#define S0_HIT    0x8150
#define HANDLER_OPER 0x8173  // jsr OperModeExecutionTree's caller region
#define SKIP_MAIN 0x8178
#define RTI_PC    0x8181

int main(int argc, char **argv) {
  int tas = argc > 3 && !strcmp(argv[3], "--tas-startup");
  if (argc < 3 || nes_load_rom(argv[1])) { fprintf(stderr, "usage/rom\n"); return 2; }
  Movie mv; char err[128];
  if (movie_load(argv[2], &mv, err) || (tas && movie_align(&mv, err))) { fprintf(stderr, "%s\n", err); return 2; }
  static NES n;
  nes_power(&n);
  if (tas) nes_reset(&n);
  printf("frame,pad,polls,nmis,reent,int_pc,s_min,nmi_fpos,t_s0,t_main,t_rti,main_fpos,itc,tc,pause,ptimer,mode,task,scr,ges,st,wet,star,cat,y,x,page,pstate,eit5,mus,tmr,alt,world,level,area,atype,dint,yhi,lock,fw,msg,fetch,sp0,size,status,aptr,ectrl,coll,flagy,ptimer2\n");
  uint64_t nmi_cyc = 0;
  uint8_t s_min = 0xff;
  for (int f = 0; f < mv.n; f++) {
    if (mv.cmd[f] & 1) nes_reset(&n);
    if (mv.cmd[f] & 2) nes_power(&n);
    n.pad[0] = mv.p1[f]; n.pad[1] = mv.p2[f]; n.polls = 0; n.frame_done = 0;
    int nmis = 0, reent = 0; unsigned int_pc = 0xffff; int nmi_fpos = -1;
    long t_s0 = -1, t_main = -1, t_rti = -1; int main_fpos = -1;
    s_min = n.s;
    unsigned fuel = 200000;
    while (!n.frame_done && fuel--) {
      uint16_t pc0 = n.pc;
      if (pc0 == SKIP_S0) t_s0 = n.cyc - nmi_cyc;
      if (pc0 == SKIP_MAIN) { t_main = n.cyc - nmi_cyc; main_fpos = n.fpos; }
      if (pc0 == RTI_PC) t_rti = n.cyc - nmi_cyc;
      nes_step(&n);
      if (n.s < s_min) s_min = n.s;
      if (n.pc == NMI_ENTRY && pc0 != NMI_ENTRY) {
        uint16_t ret = n.ram[0x100 | (uint8_t)(n.s + 2)] | n.ram[0x100 | (uint8_t)(n.s + 3)] << 8;
        nmis++;
        if (ret != ENDLESS && ret != ENDLESS + 1) { /* classify below */ }
        int_pc = ret;
        if (ret != ENDLESS) reent++;
        nmi_cyc = n.cyc;
        nmi_fpos = n.fpos;
      }
    }
    if (n.err || !n.frame_done) {
      fprintf(stderr, "unsupported or fuel exhausted at %04x frame %d\n", n.err ? n.err_pc : n.pc, f);
      return 1;
    }
    n.frame++;
    const uint8_t *r = n.ram;
    int tmr = r[0x7f8] * 100 + r[0x7f9] * 10 + r[0x7fa];
    printf("%d,%d,%u,%d,%d,%d,%d,%d,%ld,%ld,%ld,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d\n",
      f, mv.p1[f], n.polls, nmis, reent, int_pc, s_min, nmi_fpos, t_s0, t_main, t_rti, main_fpos,
      r[0x77f], r[0x747], r[0x776], r[0x777], r[0x770], r[0x772], r[0x73c], r[0x0e], r[0x7a0], r[0x7a1],
      r[0x746], r[0x6de], r[0xce], r[0x86], r[0x6d], r[0x1d], r[0x79b], r[0x7b1], tmr, r[0x752], r[0x75f], r[0x75c],
      r[0x760], r[0x74e], r[0x769], r[0xb5], r[0x723], r[0x6d7], r[0x719], r[0x757], r[0x722], r[0x754], r[0x756], r[0x750], r[0x710], r[0x490], r[0xd4], r[0x787]);
  }
  return 0;
}
