// What the 1-1 argument relies on, measured per level along a movie: buffer peaks in play, enemy slots occupied, the flag at each slide, vine state, block metatiles.
// An optional output file records the first visit to $AF67 in each frame, if it occurs during play.
// Usage: level_facts ROM MOVIE [PARSER_STATES]
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include <string.h>
static const int C[]={0xE7,0xE8,0x72C,0x72D,0x72E,0x72F,0x730,0x731,0x732,0x734,0x735,0x729,0x72A,0x72B,0x728,0x725,0x726,0x71F,0x727,0x6A0,0x742,0x741,0x743,0x733,0x74E,0x721,0x720};
int main(int c,char**v){ if(nes_load_rom(v[1]))return 2; Movie m; char err[128]; if(movie_load(v[2],&m,err)||movie_align(&m,err)){puts(err);return 2;}
 FILE*o=c>3?fopen(v[3],"w"):0; static NES n; nes_power(&n); nes_reset(&n);
 int key=-1,start=0,p3=0,p4=0,slots=0,noflag=0,slides=0,e=0,vine=0,v758=0,bb=0,behind=0,back=0,hi=0,water=0; int last0e=0; uint8_t seen[256]={0}; uint8_t idsSeen[256]={0};
 puts("| Level | From frame | Frames | `$0300` peak | `$0340` peak | Slots 0-4 occupied | Slides with no flag | `$0758` set | Vine metatile in buffer | `$0729` set | `$0728` set | Area types |");
 puts("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|");
 char types[16]="";
 for(int f=0;f<m.n;f++){ n.pad[0]=m.p1[f];n.pad[1]=m.p2[f];n.polls=0;n.frame_done=0; if(m.cmd[f]&1)nes_reset(&n);
  unsigned fuel=200000; int got=0; while(!n.frame_done&&fuel--){ if(o&&n.pc==0xAF67&&!got){ got=1; if(n.ram[0x772]==3&&n.ram[0x770]==1){ fprintf(o,"%d-%d ",n.ram[0x75F]+1,n.ram[0x75C]+1); for(unsigned i=0;i<sizeof C/sizeof*C;i++) fprintf(o,"%02x",n.ram[C[i]]); fputc('\n',o);} }
    if(n.ram[0x729])behind=1; if(n.ram[0x728]&&n.ram[0x772]==3)back=1; nes_step(&n);}
  if(n.err){printf("err at %d\n",f);break;} n.frame++; const uint8_t*r=n.ram; if(r[0x770]!=1)continue;
  int k=r[0x75F]*16+r[0x75C];
  if(k!=key){ if(key>=0) printf("| %d-%d | %d | %d | %d | %d | %d | %d/%d | %d | %d | %d | %d | %s |\n",key/16+1,key%16+1,start,f-start,p3,p4,slots,noflag,slides,v758,vine,behind,back,types); key=k;start=f;p3=p4=slots=noflag=slides=v758=vine=behind=back=0;types[0]=0; memset(seen,0,256);}
  if(r[0x772]==3){ if(r[0x300]>p3)p3=r[0x300]; if(r[0x340]>p4)p4=r[0x340]; }
  int s=0; for(int i=0;i<5;i++) s+=r[0x0F+i]!=0; if(s>slots)slots=s;
  if(r[0xE]==4&&last0e!=4){ slides++; if(r[0x1B]!=0x30)noflag++; } last0e=r[0xE];
  if(r[0x758])v758=1;
  for(int a=0x500;a<0x6A0;a++) if(r[a]==0x56||r[a]==0x5B){vine=1;break;}
  if(!seen[r[0x74E]&255]){ seen[r[0x74E]&255]=1; char t[4]; snprintf(t,4,"%d ",r[0x74E]&7); strncat(types,t,15-strlen(types)); }
 }
 if(key>=0) printf("| %d-%d | %d | %d | %d | %d | %d | %d/%d | %d | %d | %d | %d | %s |\n",key/16+1,key%16+1,start,m.n-start,p3,p4,slots,noflag,slides,v758,vine,behind,back,types);
 if(o)fclose(o); }
