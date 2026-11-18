// Hit counts along a movie for every site the 1-1 work has reasoned about, with the first frame and state.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
typedef struct { const char*name; unsigned n; int first; int lv; } H; static H h[64]; static int nh;
static void hit(int i,const char*name,int f,const uint8_t*r){ if(i>=nh)nh=i+1; h[i].name=name; if(!h[i].n){h[i].first=f;h[i].lv=(r[0x75F]+1)*100+r[0x75C]+1;} h[i].n++; }
#define TRIC(i) (((i)&4)?0x0F:0xF0)
int main(int c,char**v){ if(nes_load_rom(v[1]))return 2; Movie m; char err[128]; if(movie_load(v[2],&m,err)||movie_align(&m,err)){puts(err);return 2;}
 int shift=getenv("SHIFT")?atoi(getenv("SHIFT")):0; static NES n; nes_power(&n); if(getenv("TRICRAM")) for(int i=0;i<0x800;i++) n.ram[i]=TRIC(i); nes_reset(&n); for(int i=0;i<shift;i++) nes_frame(&n,0,0); int shown=0,lastlv=-1,p398=-1; int maxp3=0,max3=0,max4p=0,max4=0,max398=0,max14=0,m734=-1,resets=0; int levels[256]={0}; int rows[16]={0}; uint8_t e9vals[256]={0}; int players=0;
 for(int f=0;f<m.n;f++){ n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; if(m.cmd[f]&1){nes_reset(&n);resets++;} if(m.cmd[f]&2){nes_power(&n);nes_reset(&n);}
  unsigned fuel=400000; while(!n.frame_done&&fuel--){ unsigned pc=n.pc; const uint8_t*r=n.ram; unsigned ea=(r[6]|r[7]<<8)+n.y;
   if(r[0x770]==2)hit(19,"victory mode",f,r); if(pc==0xB2BF)hit(0,"$B2BF slide skipped, slot 5 not the flag",f,r);
   if(pc==0x9864&&n.x==5)hit(1,"$9864 star flag overwrites slot 5",f,r);
   if(pc==0x9864)hit(2,"$9864 star flag placed",f,r);
   if(pc==0xB724&&n.x==5)hit(3,"$B724 bubble setup with X=5, writes $E9",f,r);
   if(pc==0xB724&&n.x!=5&&n.x>2)hit(4,"$B724 bubble setup with X>2, not 5",f,r);
   if(pc==0xB93E)hit(5,"$B93E vine slot stored",f,r);
   if(pc==0x91AD)hit(6,"$91AD vine started by the area setup",f,r);
   if(pc==0xB1D3)hit(7,"$B1D3 vine flag set",f,r);
   if(pc==0xD773)hit(8,"$D773 Bowser defeated store",f,r);
   if(pc==0xD758&&r[0x16+n.x]==0x2D&&0)hit(9,"",f,r);
   if(pc==0x9AC4&&r[0x734]>9)hit(10,"$9AC4 stair counter wrapped",f,r);
   if(pc==0xC0C8)hit(11,"$C0C8 loop command resets the area offset",f,r);
   if(pc==0xDCBF&&n.x==2)hit(12,"$DCBC head guard read past its table, X=2 ($AD)",f,r);
   if(pc==0x941B)hit(13,"$941B background screen subtract",f,r);
   if(pc==0xE41B){ rows[n.y>>4]++; if(ea<0x500||ea>0x69F){hit(14,"$E41B block read outside the buffers",f,r); if(shown++<6) printf("  oob read %04x val %02x, f %d %d-%d: X=%u x-slot id %02x y=%u hi=%u, ret %02x%02x engine %u state %u\n",ea,r[ea&0x7ff],f,r[0x75F]+1,r[0x75C]+1,n.x,n.x?r[0x16 + n.x - 1]:0xff,r[0xCE + n.x],r[0xB5 + n.x],r[0x100+((n.s+3)&255)],r[0x100+((n.s+2)&255)],r[0xE],r[0x1D]);}}
   if((pc==0xBD4B||pc==0xDE20||pc==0xE007)&&(ea<0x500||ea>0x69F))hit(15,"block store outside the buffers",f,r);
   if(pc==0xE3F0&&0)hit(16,"",f,r);
   if(pc==0x8E16){ unsigned t=r[6]|r[7]<<8; if(t<0x8000)hit(17,"$8E16 jump engine into RAM",f,r);}
   if(r[0x398]>max398){max398=r[0x398]; p398=f;}  if(r[0x14]>max14&&r[0x14]<0x80)max14=r[0x14]; if(r[0x14]>=0x80)hit(18,"$14 has its top bit set",f,r);
   if(r[0x300]>max3)max3=r[0x300]; if(r[0x340]>max4)max4=r[0x340];
   if(r[0x772]==3&&r[0x770]==1){ if(r[0x300]>maxp3)maxp3=r[0x300]; if(r[0x340]>max4p)max4p=r[0x340]; }
   if(r[0x77A])players=1;
   nes_step(&n);} if(n.err){printf("emulator stopped at frame %d, pc %04x\n",f,n.pc);break;} n.frame++; const uint8_t*r=n.ram; { int lv=(r[0x75F]+1)*16+r[0x75C]+1; if(r[0x770]==1&&lv!=lastlv&&r[0x772]==3&&!getenv("QUIET")){ printf("%d-%d@%d ",r[0x75F]+1,r[0x75C]+1,f); lastlv=lv; } } if(r[0x770]==1) levels[(r[0x75F]&15)*16+(r[0x75C]&15)]++; e9vals[r[0xE9]]=1; if(f%60000==0){ fprintf(stderr,"f %d world %d-%d lives %d mode %d\n",f,r[0x75F]+1,r[0x75C]+1,r[0x75A],r[0x770]); } }
 printf("\n$0398 peak at frame %d\n",p398); printf("frames %d resets %d two-player %d\n",m.n,resets,players); printf("levels played:"); for(int i=0;i<256;i++) if(levels[i]) printf(" %d-%d(%d)",i/16+1,i%16+1,levels[i]); puts("");
 for(int i=0;i<nh;i++) if(h[i].name&&h[i].n) printf("%-52s %7u hits, first frame %d in %d-%d\n",h[i].name,h[i].n,h[i].first,h[i].lv/100,h[i].lv%100);
 printf("peaks: $0300 %d in play (%d any time), $0340 %d in play (%d any time), $0398 %d, $14 %d\nrow counts at $E41B:",maxp3,max3,max4p,max4,max398,max14); for(int i=0;i<16;i++) printf(" %x:%d",i,rows[i]); puts(""); int e=0; for(int i=0;i<256;i++) e+=e9vals[i]; printf("distinct $E9 values %d\n",e); }
