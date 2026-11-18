// Forces VRAM_Buffer2_Offset ($0340) to each value where a buffer-2 writer reads it during 1-1 surface play:
// the column renderer at $88B5 or the attribute writer at $898D. Then it runs on with the movie's inputs and
// compares each run with the unedited one. This edits state: it tests what a corrupted $0340 does, not whether
// a run can corrupt it. Buffer 1 reaches $0340 once its offset passes about 54.
// usage: edit_0340 rom movie site nth [frames]    site: 88b5 or 898d. Exit: 0 reported, 1 read not found or the
// unedited run failed, 2 bad input or wrong ROM.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdlib.h>
#include <string.h>
static int finish(NES *n) {
  unsigned fuel=100000;
  while(!n->frame_done&&fuel--) nes_step(n);
  if(!n->frame_done) return 0;
  n->frame++;
  return 1;
}
static int frame(NES *n, uint8_t p0, uint8_t p1) { n->pad[0]=p0;n->pad[1]=p1;n->polls=0;n->frame_done=0; return finish(n); }
// Game state: RAM other than sprite memory ($0200-$02FF) and the two VRAM buffers and offsets ($0300-$0362).
static int gameDiff(const NES *a, const NES *b, char *list, int max) {
  int nd=0; list[0]=0;
  for(int i=0;i<0x800;i++) { if(i>=0x200&&i<0x363) continue;
    if(a->ram[i]!=b->ram[i]) { if(nd<max) sprintf(list+strlen(list)," %03X:%02X/%02X",i,a->ram[i],b->ram[i]); nd++; } }
  return nd;
}
int main(int argc,char **argv) {
  if(argc<5 || nes_load_rom(argv[1])) return 2;
  Movie m;char err[128];
  if(movie_load(argv[2],&m,err)||movie_align(&m,err)) { fprintf(stderr,"%s\n",err); return 2; }
  if(movie_rom_matches(&m,argv[1])!=1) { fprintf(stderr,"missing or mismatched movie ROM checksum\n"); return 2; }
  unsigned site=(unsigned)strtol(argv[3],0,16); int nth=atoi(argv[4]), after=argc>5?atoi(argv[5]):600;
  if(site!=0x88b5&&site!=0x898d) return 2;
  static NES n,snap,base,e; nes_power(&n);nes_reset(&n);
  int found=0,at=-1,count=0;
  for(int f=0;f<m.n&&!found;f++) {
    if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);
    n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; unsigned fuel=100000;
    while(!n.frame_done&&fuel--) {
      if(n.pc==site&&n.ram[0x770]==1&&n.ram[0x772]==3&&n.ram[0x74e]==1&&n.ram[0x75f]==0&&n.ram[0x75c]==0&&count++==nth) { found=1;at=f;snap=n;break; }
      nes_step(&n);
    }
    if(found) break;
    if(n.err||!n.frame_done) { fprintf(stderr,"model stopped at frame %d, err %d\n",f,n.err); return 1; }
    n.frame++;
  }
  if(!found) { fprintf(stderr,"no read number %d at %04X\n",nth,site); return 1; }
  // The continuations replay only controller bytes, so a reset or power command after the edit would be lost.
  for(int f=at+1;f<m.n&&f<at+after;f++) if(m.cmd[f]&3) { fprintf(stderr,"movie resets or powers on at frame %d, after the edit\n",f); return 2; }
  printf("read %d at %04X on frame %d: $0340 was %d, Mario page %d x %u y %u\n",nth,site,at,snap.ram[0x340],snap.ram[0x6d],snap.ram[0x86],snap.ram[0xce]);
  // the unedited run, frame by frame, for comparison
  static NES traj[4096]; if(after>4000) after=4000;
  base=snap; if(!finish(&base)||base.err) { fprintf(stderr,"unedited frame failed\n"); return 1; }
  traj[0]=base;
  for(int k=1;k<after&&at+k<m.n;k++) { traj[k]=traj[k-1]; if(!frame(&traj[k],m.p1[at+k],m.p2[at+k])||traj[k].err) { fprintf(stderr,"unedited run failed\n"); return 1; } }
  int counts[5]={0};
  puts("value: class | frames run, then: page x y engine mode task world-level | game RAM differing (addr:edited/unedited)");
  for(int v=0;v<256;v++) {
    // An exit counts only at the end of a frame that completed inside the model.
    e=snap; e.ram[0x340]=v; int done=finish(&e), k=0, lastFC=e.ram[0x09], still=0, leftAt=-1;
    if(done&&!e.err&&e.ram[0x770]==1&&(e.ram[0x75f]||e.ram[0x75c])) leftAt=at+1;
    while(done&&!e.err&&k+1<after&&at+k+1<m.n) {
      k++; done=frame(&e,m.p1[at+k],m.p2[at+k]);
      if(e.ram[0x09]==lastFC) still++; else { still=0; lastFC=e.ram[0x09]; }
      if(leftAt<0&&done&&!e.err&&e.ram[0x770]==1&&(e.ram[0x75f]||e.ram[0x75c])) leftAt=at+k+1;
    }
    char list[400]; int nd=gameDiff(&e,&traj[k],list,10);
    int cls = (e.err||!done) ? 0 : still>=30 ? 1 : nd==0 ? 2 : 3;
    if(leftAt>=0&&leftAt<1943) cls=4;
    counts[cls]++;
    static const char *names[]={"model error","hang","picture only","state changed","LEFT 1-1 EARLY"};
    if(cls==4&&(e.err||!done)) printf("(left on a supported frame %d, model error later) ",leftAt);
    printf("%3d $%02X: %s | %d, then p%d x%u y%u e%u mode %u task %u %d-%d | %d differ%s\n",v,v,names[cls],k,
      e.ram[0x6d],e.ram[0x86],e.ram[0xce],e.ram[0xe],e.ram[0x770],e.ram[0x772],e.ram[0x75f]+1,e.ram[0x75c]+1,nd,list);
  }
  printf("summary: model error %d, hang %d, picture only %d, state changed %d, left 1-1 before frame 1943: %d\n",counts[0],counts[1],counts[2],counts[3],counts[4]);
  return 0;
}
