#include "../../emu/nes.h"
#include "../../emu/movie.h"
// For each cell in [LO,HI] and sampled TAS frames on 1-1's surface: set the cell to each of a few values at the frame's
// start, run two frames, and compare game RAM (outside OAM $0200-$02FF, the buffers $0300-$0362 and the cell) with the
// unedited run. The comparison reports changes at the end of the replay.
static void run(NES *n, uint8_t p) { n->pad[0]=p; n->pad[1]=0; n->polls=0; n->frame_done=0; unsigned f=100000; while(!n->frame_done&&f--) nes_step(n); n->frame++; }
int main(int argc,char**argv){
  nes_load_rom(argv[1]); Movie m; char err[128]; movie_load(argv[2],&m,err); movie_align(&m,err);
  int lo=strtol(argv[3],0,16), hi=strtol(argv[4],0,16);
  static NES s, a, b; nes_power(&s); nes_reset(&s);
  static int affected[0x800], tried[0x800], firstF[0x800], firstD[0x800];
  for(int f=0; f<1188; f++){
    if(f>=200 && f%7==0 && s.ram[0x74e]==1 && s.ram[0x770]==1 && s.ram[0x772]==3){
      a=s; run(&a,m.p1[f]); run(&a,m.p1[f+1]);
      for(int c=lo;c<=hi;c++) for(int k=0;k<4;k++){
        uint8_t v=(uint8_t)(0x35+k*0x47); if(v==s.ram[c]) continue;
        b=s; b.ram[c]=v; run(&b,m.p1[f]); run(&b,m.p1[f+1]); tried[c]++;
        if(b.err){ affected[c]++; if(!firstF[c]){firstF[c]=f; firstD[c]=-1;} continue; }
        for(int i=0;i<0x800;i++){ if((i>=0x200&&i<0x363)||i==c) continue; if(a.ram[i]!=b.ram[i]){ affected[c]++; if(!firstF[c]){firstF[c]=f; firstD[c]=i;} break; } }
      }
    }
    run(&s,m.p1[f]);
  }
  for(int c=lo;c<=hi;c++) if(tried[c]) printf("$%04X: %d/%d runs changed game RAM%s", c, affected[c], tried[c], affected[c]? "":"\n"), affected[c]? printf(" (first at frame %d, $%04X)\n", firstF[c], firstD[c]):0;
}
