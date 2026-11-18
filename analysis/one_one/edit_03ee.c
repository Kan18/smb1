// Forces SprDataOffset_Ctrl ($03EE) to each value at a block hit on a movie, at the instruction that reads it ($BCF0), and reports what the rest of the frame and the next frames do against the unedited run.
// This edits state: it tests what a corrupted byte does, not whether a run can corrupt it.
// usage: edit_03ee rom movie [nth-hit] [frames]    Exit: 0 reported, 1 hit not found or the unedited run failed, 2 bad input.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
static int finish(NES *n) {   // the rest of the current frame
  unsigned fuel=100000;
  while(!n->frame_done&&fuel--) nes_step(n);
  if(!n->frame_done) return 0;
  n->frame++;
  return 1;
}
static int frame(NES *n, uint8_t p0, uint8_t p1) {
  n->pad[0]=p0;n->pad[1]=p1;n->polls=0;n->frame_done=0;
  return finish(n);
}
int main(int argc,char **argv) {
  if(argc<3 || nes_load_rom(argv[1])) return 2;
  Movie m;char err[128];
  if(movie_load(argv[2],&m,err)||movie_align(&m,err)) { fprintf(stderr,"%s\n",err); return 2; }
  if(movie_rom_matches(&m,argv[1])!=1) { fprintf(stderr,"missing or mismatched movie ROM checksum\n"); return 2; }
  int nth=argc>3?atoi(argv[3]):0, after=argc>4?atoi(argv[4]):60;
  static NES n,snap,base,e; nes_power(&n);nes_reset(&n);
  int found=0,hit=-1,count=0;
  for(int f=0;f<m.n&&!found;f++) {
    if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);
    n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; unsigned fuel=100000;
    while(!n.frame_done&&fuel--) {
      if(n.pc==0xbcf0&&n.ram[0x770]==1&&count++==nth) { found=1;hit=f;snap=n;break; }
      nes_step(&n);
    }
    if(found) break;
    if(n.err||!n.frame_done) { fprintf(stderr,"model stopped at frame %d, err %d\n",f,n.err); return 1; }
    n.frame++;
  }
  if(!found) { fprintf(stderr,"no block hit number %d\n",nth); return 1; }
  printf("hit %d on frame %d; $03EE was %d, Mario at x %u page %d, $0E %d, world %d-%d\n",nth,hit,snap.ram[0x3ee],snap.ram[0x86],snap.ram[0x6d],snap.ram[0xe],snap.ram[0x75f]+1,snap.ram[0x75c]+1);
  base=snap;
  if(!finish(&base)||base.err) { fprintf(stderr,"unedited frame failed\n"); return 1; }
  puts("value: zero-page bytes differing at the frame's end | that frame | after more frames");
  for(int v=0;v<256;v++) {
    e=snap; e.ram[0x3ee]=v; int done=finish(&e);
    int nd=0; char list[300]="";
    for(int a=0;a<0x100;a++) if(e.ram[a]!=base.ram[a]){ if(nd<8) sprintf(list+strlen(list)," %02X:%02X",a,e.ram[a]); nd++; }
    unsigned pg1=e.ram[0x6d],x1=e.ram[0x86],eng1=e.ram[0xe]; int k=1;
    for(;k<after&&hit+k<m.n&&!e.err&&done;k++) done=frame(&e,m.p1[hit+k],m.p2[hit+k]);
    printf("%3d $%02X: d=%d%s | p%u x%u e%u | p%u x%u e%u mode %u task %u err %d done %d pc %04X world %d-%d\n",v,v,nd,list,pg1,x1,eng1,e.ram[0x6d],e.ram[0x86],e.ram[0xe],e.ram[0x770],e.ram[0x772],e.err,done,e.pc,e.ram[0x75f]+1,e.ram[0x75c]+1);
  }
  return 0;
}
