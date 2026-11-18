// The VRAM buffer offsets' ranges during play ($0770 = 1, $0772 = 3), for choosing a clean-run contract: their values at each instruction, and $0340 where the column writers read it.
// usage: buffer_range rom movie [last-frame]    Exit: 0 reported, 1 the model failed on the movie, 2 bad input or wrong ROM.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
static int h300[256],h340[256],col1[256],col2[256],at8175[256],at8175c[32];
int main(int argc,char **argv) {
  if(argc<3 || nes_load_rom(argv[1])) return 2;
  Movie m;char err[128];
  if(movie_load(argv[2],&m,err)||movie_align(&m,err)) { fprintf(stderr,"%s\n",err); return 2; }
  if(movie_rom_matches(&m,argv[1])!=1) { fprintf(stderr,"missing or mismatched movie ROM checksum\n"); return 2; }
  int end=argc>3?atoi(argv[3]):m.n; if(end>m.n)end=m.n;
  static NES n;nes_power(&n);nes_reset(&n);
  int first300=-1,first340=-1;
  for(int f=0;f<end;f++) {
    if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);
    n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; unsigned fuel=100000;
    while(!n.frame_done&&fuel--) {
      if(n.ram[0x770]==1&&n.ram[0x772]==3) {
        h300[n.ram[0x300]]=1;h340[n.ram[0x340]]=1;
        if(n.ram[0x300]>=0x40&&first300<0)first300=f;
        if(n.pc==0x88b5)col1[n.ram[0x340]]++;
        if(n.pc==0x898d)col2[n.ram[0x340]]++;
        if(n.pc==0x8175){at8175[n.ram[0x340]]++;}
      }
      nes_step(&n);
    }
    if(n.err||!n.frame_done) { fprintf(stderr,"model stopped at frame %d, err %d\n",f,n.err); return 1; }
    n.frame++;
  }
  printf("frames %d; $0300 at instructions:",end); for(int i=0;i<256;i++) if(h300[i])printf(" %d",i);
  printf("\n$0340 at instructions:"); for(int i=0;i<256;i++) if(h340[i])printf(" %d",i);
  printf("\n$0340 at $88B5:"); for(int i=0;i<256;i++) if(col1[i])printf(" %d:%d",i,col1[i]);
  printf("\n$0340 at $898D:"); for(int i=0;i<256;i++) if(col2[i])printf(" %d:%d",i,col2[i]);
  printf("\n$0340 at $8175:"); for(int i=0;i<256;i++) if(at8175[i])printf(" %d:%d",i,at8175[i]);
  printf("\nfirst frame with $0300 >= $40 in play: %d\n",first300);(void)first340;(void)at8175c;
  return 0;
}
