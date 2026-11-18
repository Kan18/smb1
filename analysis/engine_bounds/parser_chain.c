// The parser's state at each frame's $AF67, one line per frame: hex bytes of its cells, along a movie until 1-1 ends.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
static const int C[]={0xE7,0xE8,0x72C,0x72D,0x72E,0x72F,0x730,0x731,0x732,0x734,0x735,0x729,0x72A,0x72B,0x728,0x725,0x726,0x71F,0x727,0x6A0,0x742,0x741,0x743,0x733,0x74E,0x721,0x720};
int main(int c,char**v){ if(nes_load_rom(v[1]))return 2; Movie m; char err[128]; if(movie_load(v[2],&m,err)||movie_align(&m,err)){puts(err);return 2;}
 int N=atoi(v[3]); static NES n; nes_power(&n); nes_reset(&n);
 for(int f=0;f<N&&f<m.n;f++){ n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; if(m.cmd[f]&1)nes_reset(&n);
  unsigned fuel=200000; int seen=0; while(!n.frame_done&&fuel--){ if(n.pc==0xAF67&&!seen){ seen=1; if(n.ram[0x772]==3&&n.ram[0x770]==1){ for(unsigned i=0;i<sizeof C/sizeof*C;i++) printf("%02x",n.ram[C[i]]); putchar('\n'); } } nes_step(&n);} if(n.err)return 1; n.frame++;
  if(n.ram[0x75C]==1&&f>1500) break; }
}
