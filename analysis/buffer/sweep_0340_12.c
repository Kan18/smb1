// For 1-2: at every read of VRAM_Buffer2_Offset ($0340) by a buffer-2 writer (the column renderer at $88B5 or the
// attribute writer at $898D) while a candidate ceiling brick is on screen, force $0340 to that brick's block-record
// address low byte, the value buffer 1 would leave there if the brick's head-hit record started at offset 62. Then run
// on with the movie's inputs and compare with the unedited run, as analysis/one_one/edit_0340.c does for 1-1.
// Candidate bricks: row 0 (the ceiling), page columns 8-15, at the spots a jump can reach (40-47, 72-75, 88-89,
// 104-111, 136-137); the low byte is $80 + 2*(column & 15). Like edit_0340, this edits state: it shows what a
// corrupted $0340 does, not whether a run can produce one, and the inputs aren't adapted to the edit.
// usage: sweep_0340_12 rom movie [frames]
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
static int in12(const NES *n) { return n->ram[0x770]==1&&n->ram[0x75f]==0&&n->ram[0x75c]==1; }
static int px(const NES *n) { return n->ram[0x6d]*256+n->ram[0x86]; }
static const int spots[][2]={{40,47},{72,75},{88,89},{104,111},{136,137}};
// Game state: RAM other than sprite memory ($0200-$02FF) and the two VRAM buffers and offsets ($0300-$0362).
static int gameDiff(const NES *a, const NES *b) {
  int nd=0;
  for(int i=0;i<0x800;i++) { if(i>=0x200&&i<0x363) continue; if(a->ram[i]!=b->ram[i]) nd++; }
  return nd;
}
int main(int argc,char **argv) {
  if(argc<3 || nes_load_rom(argv[1])) return 2;
  Movie m;char err[128];
  if(movie_load(argv[2],&m,err)||movie_align(&m,err)) { fprintf(stderr,"%s\n",err); return 2; }
  if(movie_rom_matches(&m,argv[1])!=1) { fprintf(stderr,"missing or mismatched movie ROM checksum\n"); return 2; }
  int after=argc>3?atoi(argv[3]):300; if(after>4000) after=4000;
  static NES n,snap,e; static NES traj[4000];
  nes_power(&n);nes_reset(&n);
  // the frame the unedited run leaves 1-2
  int leave=-1;
  { static NES t; t=n; int was=0;
    for(int f=0;f<m.n;f++) { if(m.cmd[f]&1)nes_reset(&t);if(m.cmd[f]&2)nes_power(&t);
      if(!frame(&t,m.p1[f],m.p2[f])||t.err) break;
      if(in12(&t)) was=1; else if(was&&t.ram[0x770]==1) { leave=f; break; } } }
  printf("unedited run leaves 1-2 after frame %d\n",leave);
  puts("read: frame site $0340 screen-left-col | value: class, frames run, Mario px vs unedited, $03EE edited/unedited, game RAM differing");
  int reads=0,counts[7]={0},strays[7]={0}; int bestGain=-1000000;
  for(int f=0;f<m.n;f++) {
    if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);
    n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; unsigned fuel=100000;
    while(!n.frame_done&&fuel--) {
      if((n.pc==0x88b5||n.pc==0x898d)&&n.ram[0x772]==3&&in12(&n)) {
        int left=n.ram[0x71a]*256+n.ram[0x71c], vals[16], nv=0;
        for(unsigned s=0;s<sizeof spots/sizeof spots[0];s++) for(int c=spots[s][0];c<=spots[s][1];c++)
          if(c*16>=left&&c*16+16<=left+256) { int v=0x80+2*(c&15),k; for(k=0;k<nv&&vals[k]!=v;k++) {}
            if(k==nv) vals[nv++]=v; }
        if(nv) {
          snap=n; reads++;
          traj[0]=snap; int ok=finish(&traj[0])&&!traj[0].err, len=1;
          for(;ok&&len<after&&f+len<m.n;len++) { traj[len]=traj[len-1]; ok=frame(&traj[len],m.p1[f+len],m.p2[f+len])&&!traj[len].err; }
          printf("read %d: frame %d %04X $0340=%02X left-col %d |",reads,f,n.pc,snap.ram[0x340],left/16);
          for(int i=0;i<nv;i++) {
            // stray: the first value other than 0 or 1 seen in $03EE (the block-object index) at a frame's end
            e=snap; e.ram[0x340]=vals[i]; int done=finish(&e), k=0, lastFC=e.ram[0x09], still=0, leftAt=-1;
            int stray=done&&e.ram[0x3ee]>1?e.ram[0x3ee]:-1;
            while(done&&!e.err&&k+1<len) {
              k++; done=frame(&e,m.p1[f+k],m.p2[f+k]);
              if(stray<0&&done&&e.ram[0x3ee]>1) stray=e.ram[0x3ee];
              if(e.ram[0x09]==lastFC) still++; else { still=0; lastFC=e.ram[0x09]; }
              if(still>=30) break;
              if(leftAt<0&&done&&!e.err&&e.ram[0x770]==1&&!in12(&e)) leftAt=f+k;
            }
            int nd=gameDiff(&e,&traj[k]);
            // A stop inside the NMI's buffer draw (WriteBufferToScreen, $8E92-$8EE5) means the draw ran past vblank:
            // the model doesn't do PPU writes during rendering, which on hardware change only the picture and timing.
            int ppu=e.err==2&&e.err_pc>=0x8e92&&e.err_pc<0x8ee6;
            int cls=ppu?6:(e.err||!done)?0:still>=30?1:nd==0?2:3;
            if(leftAt>=0&&(leave<0||leftAt<leave)) cls=4;
            int gain=in12(&e)&&in12(&traj[k])?px(&e)-px(&traj[k]):0;
            if(cls>=2&&gain>bestGain) bestGain=gain;
            if(cls==3&&gain>0) cls=5;
            counts[cls]++; if(stray>=0) strays[cls]++;
            static const char *names[]={"MODEL ERROR","hang","converged","state changed","LEFT 1-2 EARLY","AHEAD","draw overran vblank"};
            printf(" $%02X:%s,%d,%+d,%02X/%02X,%d",vals[i],names[cls],k,gain,e.ram[0x3ee],traj[k].ram[0x3ee],nd);
            if(stray>=0) printf(",03EE=%02X",stray);
            if(e.err) printf(",err%d@%04X",e.err,e.err_pc);
          }
          putchar('\n'); fflush(stdout);
        }
      }
      nes_step(&n);
    }
    if(n.err||!n.frame_done) { fprintf(stderr,"model stopped at frame %d, err %d\n",f,n.err); return 1; }
    n.frame++;
  }
  printf("summary over %d reads: model error %d, buffer draw overran vblank %d, hang %d, converged %d, state changed %d, "
    "left 1-2 early %d, ahead %d; best gain %+d px\n",
    reads,counts[0],counts[6],counts[1],counts[2],counts[3],counts[4],counts[5],bestGain);
  printf("with a stray $03EE (not 0 or 1): model error %d, hang %d, state changed %d, ahead %d\n",strays[0],strays[1],strays[3],strays[5]);
  return 0;
}
