// How high can VRAM buffer 1's offset ($0300) get in 1-1's bonus room? Coin pickups set $0773 to 6, so the NMI
// skips buffer 1's clear, and each pickup adds 14 (coins and score). This searches inputs from the TAS's state
// on entering the room, keeping per frame the state with the highest $0300 for each physics state and coin set.
// It's a beam search, not exhaustive: a high result is a witness, a low one is only evidence.
// usage: bonus_overflow rom movie start-frame frames [beam]    Exit: 0 reported, 1 the model failed, 2 bad input or wrong ROM.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <stdlib.h>
#include <string.h>
typedef struct { NES n; int peak; } St;
static const unsigned char pads[] = {0x00,0x01,0x02,0x80,0x81,0x82,0x40,0x41,0x42,0xC0,0xC1,0xC2,0x04,0x05,0x06,0x84,0x85,0x86};
static unsigned coins(const NES *n) { unsigned b=0; int k=0;
  for (int r=3;r<=7;r+=2) for (int c=4;c<=10;c++) { if (n->ram[0x500+r*16+c]==0xc2) b|=1u<<k; k++; } return b; }
static const int keyCells[] = {0x86,0x6d,0xce,0xb5,0x57,0x9f,0x400,0x416,0x433,0x705,0x1d,0x0a,0x0d,0x714,0x754,0x756,
  0x700,0x701,0x702,0x709,0x70a,0x0e,0x45,0x33};
static unsigned long long key(const NES *n) { unsigned long long h=1469598103934665603ull;
  for (size_t i=0;i<sizeof(keyCells)/sizeof(int);i++) { h^=n->ram[keyCells[i]]; h*=1099511628211ull; }
  h^=coins(n); h*=1099511628211ull; return h; }
static int run(NES *n, unsigned char pad) { int peak=0; n->pad[0]=pad; n->pad[1]=0; n->polls=0; n->frame_done=0;
  unsigned fuel=100000; while(!n->frame_done&&fuel--) { nes_step(n); if(n->ram[0x300]>peak) peak=n->ram[0x300]; }
  n->frame++; return (n->err||!n->frame_done) ? -1 : peak; }
static int cmpSt(const void *a, const void *b) { const St *x=a,*y=b;
  int fx=x->n.ram[0x300], fy=y->n.ram[0x300]; return fy-fx; }
int main(int argc,char **argv) {
  if(argc<5||nes_load_rom(argv[1])) return 2;
  Movie m;char err[128]; if(movie_load(argv[2],&m,err)||movie_align(&m,err)) { fprintf(stderr,"%s\n",err); return 2; }
  if(movie_rom_matches(&m,argv[1])!=1) { fprintf(stderr,"missing or mismatched movie ROM checksum\n"); return 2; }
  int start=atoi(argv[3]), frames=atoi(argv[4]), beam=argc>5?atoi(argv[5]):20000;
  if(start<0||start>=m.n||frames<1||beam<1) { fprintf(stderr,"need 0 <= start < movie length, frames >= 1, beam >= 1\n"); return 2; }
  static NES base; nes_power(&base); nes_reset(&base);
  for(int f=0;f<start;f++){ if(m.cmd[f]&1)nes_reset(&base); if(m.cmd[f]&2)nes_power(&base);
    if(run(&base,m.p1[f])<0) return 1; }
  size_t cap=(size_t)beam*sizeof(pads);
  St *cur=malloc(sizeof(St)*(size_t)beam), *nxt=malloc(sizeof(St)*cap);
  size_t hsz=1; while(hsz<4*(size_t)beam) hsz<<=1;
  unsigned long long *tab=malloc(sizeof(unsigned long long)*hsz);
  cur[0].n=base; cur[0].peak=0; int nc=1, best=0;
  for(int f=0;f<frames;f++) {
    size_t nn=0;
    for(int i=0;i<nc;i++) for(size_t p=0;p<sizeof(pads);p++) {
      St *s=&nxt[nn]; *s=cur[i]; int pk=run(&s->n,pads[p]); if(pk<0) continue;
      if(s->n.ram[0x770]!=1||s->n.ram[0x772]!=3||s->n.ram[0x74e]!=2) continue;  // left the room or play
      if(pk>s->peak) s->peak=pk;
      if(s->peak>best){best=s->peak;
        printf("frame %d: $0300 peak %d, coins left %d, x=%d y=%d\n",start+f+1,best,__builtin_popcount(coins(&s->n)),s->n.ram[0x86],s->n.ram[0xce]); fflush(stdout);}
      nn++;
    }
    // keep the highest $0300 for each physics state and coin set
    qsort(nxt,nn,sizeof(St),cmpSt);
    memset(tab,0,sizeof(unsigned long long)*hsz); nc=0;
    for(size_t i=0;i<nn&&nc<beam;i++){ unsigned long long k=key(&nxt[i].n)+1; size_t h=(k*0x9E3779B97F4A7C15ull)&(hsz-1);
      while(tab[h]&&tab[h]!=k) h=(h+1)&(hsz-1);
      if(!tab[h]){ tab[h]=k; cur[nc++]=nxt[i]; } }
    if(f%10==9){ printf("frame %d: %d states\n",start+f+1,nc); fflush(stdout); }
  }
  printf("highest $0300 reached: %d\n",best);
  return 0;
}
