// Prints each change of the game's phase bytes at frame ends along a movie, for the milestones in lean/Smb/Goal/OneOne.lean.
// usage: milestones rom movie frames
#include "../../emu/nes.h"
#include "../../emu/movie.h"
static unsigned phi(NES *n) {
  unsigned p=n->ram[0x6d]*256+n->ram[0x86], l=n->ram[0x71a]*256+n->ram[0x71c];
  return ((p-l)&65535)<32768 ? p*256+n->ram[0x400] : l*256;
}
int main(int argc,char **argv) {
  if(argc!=4 || nes_load_rom(argv[1])) return 2;
  Movie m;char err[128];
  if(movie_load(argv[2],&m,err)||movie_align(&m,err)||movie_rom_matches(&m,argv[1])!=1) return 2;
  static NES n;nes_power(&n);nes_reset(&n);
  int end=atoi(argv[3]); unsigned last=~0u;
  puts("s_f mode task engine area_type world level area alt state y x:phi itc timer");
  for(int f=0;f<end&&f<m.n;f++) {
    if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);
    n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0;
    unsigned fuel=100000;
    while(!n.frame_done&&fuel--) nes_step(&n);
    if(n.err||!n.frame_done)return 1;n.frame++;
    unsigned key=n.ram[0x770]|n.ram[0x772]<<8|n.ram[0xe]<<16|(unsigned)n.ram[0x74e]<<24;
    key^=(n.ram[0x75f]*7u+n.ram[0x75c]*31u+n.ram[0x760]*127u)<<3;
    if(key!=last) printf("%d %u %u %u %u %u %u %u %u %u %u %u %u %u%u%u\n",f,n.ram[0x770],n.ram[0x772],n.ram[0xe],n.ram[0x74e],n.ram[0x75f],n.ram[0x75c],n.ram[0x760],n.ram[0x751+0],n.ram[0x1d],n.ram[0xce],phi(&n),n.ram[0x77f],n.ram[0x7f8],n.ram[0x7f9],n.ram[0x7fa]);
    last=key;
  }
}
