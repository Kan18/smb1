// Over-approximation of Mario's vertical state (y mod 16, speed, move force, sub-pixel counter, force) reachable from
// any jump start and any walk-off (any counter, any class), allowing on any frame: releasing A, and the ROM's mid-air
// speed writes (head bonk -> 1, block bump -> 0, brick shatter -> -2 while rising; stomp bounce -> -4 or -3 while
// falling). Reports any frame whose descent enters a row 5 px or more deep (the foot-clip condition). See
// vertical_physics.py for the transcription it follows.
// From the repository root, after creating scratch/:
//   cc -O2 emu/nes.c analysis/buffer/vertical_steps.c -o scratch/vertical_steps
//   scratch/vertical_steps "$ROM"
#include "../../emu/nes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
// state: y16 0..15, sp -6..9 (16 values), mf, dm, fsel 0..9 (class*2 + down?)
#define SPO 6
#define NS (16*16*256*256*10)
static uint8_t *vis; static uint32_t *q; static long qh,qt; static long clips=0, maxdepth=-1, sixsteps=0;
static long idx(int y16,int sp,int mf,int dm,int f){return ((((long)y16*16+(sp+SPO))*256+mf)*256+dm)*10+f;}
static void push(int y16,int sp,int mf,int dm,int f){ if(sp<-6||sp>9) {fprintf(stderr,"speed out of range %d\n",sp);exit(1);}
  long i=idx(y16,sp,mf,dm,f); if(vis[i>>3]&(1<<(i&7))) return; vis[i>>3]|=1<<(i&7); q[qt++]=(uint32_t)i; }
int main(int argc, char **argv){
  if (argc != 2) { fprintf(stderr, "usage: vertical_steps ROM\n"); return 2; }
  if (nes_load_rom(argv[1])) { fprintf(stderr, "ROM load failed\n"); return 2; }
  const uint8_t *jump_force = PRG + (0xB424 - 0x8000);
  const uint8_t *fall_force = PRG + (0xB42B - 0x8000);
  const uint8_t *jump_speed = PRG + (0xB432 - 0x8000);
  vis=calloc(NS/8+1,1); q=malloc(sizeof(uint32_t)*(size_t)NS/2);
  for(int c=0;c<5;c++){ push(0,(int8_t)jump_speed[c],0,0,c*2); for(int dm=0;dm<256;dm++) push(0,0,0,dm,c*2+1); }
  long reported=0;
  while(qh<qt){
    long i=q[qh++]; int f=i%10; i/=10; int dm=i%256; i/=256; int mf=i%256; i/=256; int sp=(int)(i%16)-SPO; int y16=(int)(i/16);
    int c=f/2, down=f&1;
    for(int rel=0;rel<2;rel++){                        // rel=1: A released / force dumped this frame
      int d2=down; if(rel){ if(down) continue; d2=1; }
      if(sp>=0) d2=1;                                  // JumpSwimSub dumps the force once not rising
      int force=d2?fall_force[c]:jump_force[c];
      int dsum=dm+mf, c1=dsum>>8, dm2=dsum&255; int step=sp+c1; int ny=y16+step;
      int mfs=mf+force, c2=mfs>>8, mf2=mfs&255; int sp2=sp+c2; if(sp2>=4&&mf2>=0x80){sp2=4;mf2=0;}
      if(step>=6) sixsteps++;
      if(ny>=16 && sp2>=0){                            // descending into the next row
        int depth=ny-16; if(depth>maxdepth) maxdepth=depth;
        if(depth>=5){ clips++; if(reported++<10) printf("clip: y16=%d sp=%d mf=%02X dm=%02X class %d down %d -> step %d depth %d\n",y16,sp,mf,dm,c,d2,step,depth); }
        ny-=16;                                        // or the row is empty there: keep falling
      }
      while(ny<0) ny+=16; while(ny>=16) ny-=16;
      int nf=c*2+d2;
      push(ny,sp2,mf2,dm2,nf);
      if(sp2<0){ push(ny,1,mf2,dm2,nf); push(ny,0,mf2,dm2,nf); push(ny,-2,mf2,dm2,nf); }   // bonk, bump, shatter
      else { push(ny,-4,mf2,dm2,c*2+1); push(ny,-3,mf2,dm2,c*2+1); }                     // stomp bounce
    }
  }
  printf("states %ld, steps of 6+ seen %ld, deepest entry %ld, clips %ld\n",qt,sixsteps,maxdepth,clips);
}
