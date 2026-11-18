// drive rom (movie startframe | @statefile) script [out-state]
// script: comma-separated N:BUTTONS (BUTTONS from RLDUTSBA letters, '.' for none). Prints one line per frame.
// PNG=prefix writes <prefix><frame>.png (emu/render.h, 2x with the block grid) at the frames listed in PNGAT
// (comma-separated, or 'all'), and at the last frame if PNGAT is unset.
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include "../../emu/render.h"
#include <stdlib.h>
#include <string.h>
static NES n;
static int wantPng(int f,int last){const char*at=getenv("PNGAT");if(!getenv("PNG"))return 0;if(!at)return last;
  if(!strcmp(at,"all"))return 1;for(const char*p=at;*p;){if(atoi(p)==f)return 1;p=strchr(p,',');if(!p)break;p++;}return 0;}
static void png(int f){char path[512];snprintf(path,sizeof path,"%s%d.png",getenv("PNG"),f);render_png(&n,path,2,1);}
static uint8_t btn(const char *s){uint8_t b=0;for(;*s&&*s!=',';s++){const char*k=strchr("RLDUTSBA",*s);if(k)b|=0x80>>(k-"RLDUTSBA");}return b;}
void show(int f,uint8_t p){
  const uint8_t*r=n.ram;
  printf("%5d %c%c%c%c x=%4d.%02X sx=%3d y=%02X vy=%02X vx=%02X st=%d sz=%d L=%4d b1=%02X b2=%02X c=%02X tk=%d s32=%02X tm=%02X sc=%02X fc=%02X coin=%d%d en:",
    f,p&0x80?'R':'-',p&0x40?'L':'-',p&1?'A':'-',p&2?'B':'-',r[0x6d]*256+r[0x86],r[0x400],r[0x3ad],r[0xce],r[0x9f],r[0x57],r[0x756],r[0x754],
    r[0x71a]*256+r[0x71c],r[0x300],r[0x340],r[0x773],r[0x71f],r[0x73d],r[0x787],r[0x785],r[0x9],r[0x7ed],r[0x7ee]);
  for(int i=0;i<6;i++) if(r[0xf + i]) printf(" %d:%02X@%d,%02X/%02X",i,r[0x16 + i],r[0x6e + i]*256+r[0x87 + i],r[0xcf + i],r[0x1e + i]);
  printf(" fl:"); for(int i=0;i<6;i++) if(r[0x12c + i]) printf(" %d=%02X",i,r[0x12c + i]);
  printf(" fb:%02X,%02X 3ee=%02X\n",r[0x24],r[0x25],r[0x3ee]);
}
int main(int argc,char**argv){
  if(nes_load_rom(argv[1])) return 2;
  int ai=2;
  if(argv[2][0]=='@'){FILE*f=fopen(argv[2]+1,"rb");fread(&n,sizeof n,1,f);fclose(f);ai=3;}
  else{Movie m;char err[128];if(movie_load(argv[2],&m,err)||movie_align(&m,err)){puts(err);return 2;}
    int sf=atoi(argv[3]);nes_power(&n);nes_reset(&n);
    for(int f=0;f<sf;f++){if(m.cmd[f]&1)nes_reset(&n);if(m.cmd[f]&2)nes_power(&n);nes_frame(&n,m.p1[f],m.p2[f]);}
    ai=4;}
  const char*s=argc>ai?argv[ai]:""; int f=0; int quiet=getenv("Q")!=0;
  while(*s){int k=atoi(s);const char*c=strchr(s,':');if(!c)break;uint8_t b=btn(c+1);
    for(int i=0;i<k;i++){nes_frame(&n,b,0);if(!quiet)show(f,b);if(wantPng(f,0))png(f);f++;if(n.err){printf("err %d at %04X\n",n.err,n.err_pc);return 1;}}
    s=strchr(c,',');if(!s)break;s++;}
  if(quiet) show(f,0);
  if(getenv("PNG")&&!getenv("PNGAT")) png(f-1);
  if(argc>ai+1){FILE*o=fopen(argv[ai+1],"wb");fwrite(&n,sizeof n,1,o);fclose(o);}
}
