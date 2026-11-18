// How VRAM buffer 1's offset ($0300) accumulates during play ($0770 = 1, $0772 = 3).
// The NMI clears buffer 1 only when $0773 isn't 6; on a frame that draws buffer 2 its entries wait for the next NMI.
// At each NMI this records $0300, what the frame added to it, $0773, and runs of consecutive buffer-2 frames.
// usage: buffer_streak rom movie [last-frame]    Exit: 0 reported, 1 the model failed on the movie, 2 bad input or wrong ROM.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
static int addHist[256], atNmi[256], streakHist[64];
static int incs[0x10000][64]; // writer PC -> increase -> count, during play
int main(int argc,char **argv) {
  if(argc<3 || nes_load_rom(argv[1])) return 2;
  Movie m;char err[128];
  if(movie_load(argv[2],&m,err)||movie_align(&m,err)) { fprintf(stderr,"%s\n",err); return 2; }
  if(movie_rom_matches(&m,argv[1])!=1) { fprintf(stderr,"missing or mismatched movie ROM checksum\n"); return 2; }
  int end=argc>3?atoi(argv[3]):m.n; if(end>m.n)end=m.n;
  static NES n;nes_power(&n);nes_reset(&n);
  int after=0, streak=0, maxStreak=0, maxAdd=0, maxAddF=-1, maxAt=0, maxAtF=-1, inPlay=0, maxAny=0, maxAnyF=-1;
  for(int f=0;f<end;f++) {
    if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);
    n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; unsigned fuel=100000;
    while(!n.frame_done&&fuel--) {
      if(n.pc==0x8082) {
        int play=n.ram[0x770]==1&&n.ram[0x772]==3, v=n.ram[0x300], c=n.ram[0x773];
        if(play&&inPlay) {
          int add=v-after; if(add<0)add=0;
          addHist[add]++; atNmi[v]++;
          if(add>maxAdd){maxAdd=add;maxAddF=f;}
          if(v>maxAt){maxAt=v;maxAtF=f;}
          if(c==6){streak++; if(streak>maxStreak)maxStreak=streak;}
          else { if(streak<64)streakHist[streak]++; streak=0; }
        }
        inPlay=play;
        after = (c==6) ? v : 0;
      }
      int pc=n.pc, before=n.ram[0x300], play2=n.ram[0x770]==1&&n.ram[0x772]==3;
      nes_step(&n);
      if(play2) {
        int d=n.ram[0x300]-before;
        if(d>0&&d<64) incs[pc][d]++;
        if(n.ram[0x300]>maxAny){maxAny=n.ram[0x300];maxAnyF=f;}
      }
    }
    if(n.err||!n.frame_done) { fprintf(stderr,"model stopped at frame %d, err %d\n",f,n.err); return 1; }
    n.frame++;
  }
  printf("frames %d\nadded per frame (value:count):",end); for(int i=0;i<256;i++) if(addHist[i])printf(" %d:%d",i,addHist[i]);
  printf("\n$0300 at NMI:"); for(int i=0;i<256;i++) if(atNmi[i])printf(" %d:%d",i,atNmi[i]);
  printf("\nbuffer-2 runs ended (length:count):"); for(int i=0;i<64;i++) if(streakHist[i])printf(" %d:%d",i,streakHist[i]);
  printf("\nincreases by writer (pc:+d:count):");
  for(int pc=0;pc<0x10000;pc++) for(int d=1;d<64;d++) if(incs[pc][d]) printf(" %04X:+%d:%d",pc,d,incs[pc][d]);
  printf("\nhighest $0300 at any instruction in play %d (frame %d)",maxAny,maxAnyF);
  printf("\nlongest buffer-2 run %d; most added in a frame %d (frame %d); highest $0300 at NMI %d (frame %d)\n",maxStreak,maxAdd,maxAddF,maxAt,maxAtF);
  return 0;
}
