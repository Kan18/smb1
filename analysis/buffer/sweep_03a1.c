#include "../../emu/nes.h"
#include "../../emu/movie.h"
// For every TAS frame F in [F0, F1), force Platform_X_Scroll ($03A1) to each V in [V0, V1] at the frame's start and
// compare Mario's position (page:x, in pixels) with the unedited run after 1 and N frames, on the TAS's own inputs.
// Prints, per frame, the best gain and the value that gave it, and the frame's pos-for-scroll ($0755).
static void run(NES *n, uint8_t p) { n->pad[0]=p; n->pad[1]=0; n->polls=0; n->frame_done=0; unsigned f=100000; while(!n->frame_done&&f--) nes_step(n); n->frame++; }
static int pos(const NES *n){ return n->ram[0x6d]*256+n->ram[0x86]; }
int main(int argc,char**argv){
  if(argc<8){fprintf(stderr,"usage: sweep_03a1 ROM MOVIE F0 F1 V0 V1 N\n");return 1;}
  nes_load_rom(argv[1]); Movie m; char err[128]; if(movie_load(argv[2],&m,err)||movie_align(&m,err)){fprintf(stderr,"%s\n",err);return 1;}
  int F0=atoi(argv[3]),F1=atoi(argv[4]),V0=strtol(argv[5],0,16),V1=strtol(argv[6],0,16),N=atoi(argv[7]);
  static NES s,a,b; nes_power(&s); nes_reset(&s);
  for(int f=0;f<F0;f++) run(&s,m.p1[f]);
  int best_all=-1000000, bf=-1, bv=-1;
  for(int F=F0;F<F1;F++){
    a=s; int a1=0; for(int k=0;k<N;k++){ run(&a,m.p1[F+k]); if(k==0) a1=pos(&a); }
    int best=-1000000, best1=0, vb=-1, errs=0;
    for(int v=V0;v<=V1;v++){
      b=s; b.ram[0x3a1]=v; int b1=0;
      for(int k=0;k<N;k++){ run(&b,m.p1[F+k]); if(k==0) b1=pos(&b); }
      if(b.err){errs++;continue;}
      int g=pos(&b)-pos(&a);
      if(g>best){best=g;best1=b1-a1;vb=v;}
    }
    printf("F=%d scrollpos=%d best=$%02X gain1=%+d gainN=%+d errs=%d\n",F,s.ram[0x755],vb,best1,best,errs);
    if(best>best_all){best_all=best;bf=F;bv=vb;}
    run(&s,m.p1[F]);
  }
  printf("overall best gain after %d frames: %+d px at F=%d v=$%02X\n",N,best_all,bf,bv);
}
