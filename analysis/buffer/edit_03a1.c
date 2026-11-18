#include "../../emu/nes.h"
#include "../../emu/movie.h"
// Force Platform_X_Scroll ($03A1) to V at the start of TAS frame F (1-1 surface) and compare Mario's position
// (page:x) and the screen's left edge with the unedited run over the next N frames.
static void run(NES *n, uint8_t p) { n->pad[0]=p; n->pad[1]=0; n->polls=0; n->frame_done=0; unsigned f=100000; while(!n->frame_done&&f--) nes_step(n); n->frame++; }
static int pos(const NES *n){ return n->ram[0x6d]*256+n->ram[0x86]; }
static int scr(const NES *n){ return n->ram[0x71a]*256+n->ram[0x71c]; }
int main(int argc,char**argv){
  nes_load_rom(argv[1]); Movie m; char err[128]; movie_load(argv[2],&m,err); movie_align(&m,err);
  int F=atoi(argv[3]), N=atoi(argv[4]);
  static NES s,a,b; nes_power(&s); nes_reset(&s);
  for(int f=0;f<F;f++) run(&s,m.p1[f]);
  printf("frame %d: mario %d screen %d pos-for-scroll %d $03A1=%d\n",F,pos(&s),scr(&s),s.ram[0x755],s.ram[0x3a1]);
  for(int v=0;v<256;v+=0x10){
    a=s; b=s; b.ram[0x3a1]=v;
    for(int k=0;k<N;k++){ run(&a,m.p1[F+k]); run(&b,m.p1[F+k]); }
    printf("v=$%02X: after %d frames mario %+d px, screen %+d px vs unedited%s\n",v,N,pos(&b)-pos(&a),scr(&b)-scr(&a),b.err?" (model error)":"");
  }
}
