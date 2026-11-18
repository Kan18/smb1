// Replays a movie, edits RAM after one frame, and keeps replaying its inputs, to see what a change of state does to
// a run: movie_edit ROM MOVIE EDITFRAME FROM TO EVERY [ADDR=VAL ...] (hex). Prints Mario every EVERY frames from FROM
// to TO and on frames with the side-collision timer at 16; PNG=prefix PNGAT=frame also writes that frame (render.h).
#include "../../emu/nes.h"
#include "../../emu/movie.h"
#include "../../emu/render.h"
int main(int argc,char**argv){
  if(nes_load_rom(argv[1])) return 2;
  Movie m;char err[128]; if(movie_load(argv[2],&m,err)||movie_align(&m,err)){puts(err);return 2;}
  int ef=atoi(argv[3]),from=atoi(argv[4]),to=atoi(argv[5]),every=atoi(argv[6]); static NES n; nes_power(&n);nes_reset(&n);
  for(int f=0;f<=to&&f<m.n;f++){ if(m.cmd[f]&1)nes_reset(&n); if(m.cmd[f]&2)nes_power(&n); nes_frame(&n,m.p1[f],m.p2[f]);
    if(n.err){printf("model error f%d at %04X\n",f,n.err_pc);return 1;}
    if(f==ef) for(int a=7;a<argc;a++){unsigned ad,v; sscanf(argv[a],"%x=%x",&ad,&v); n.ram[ad]=v;}
    const uint8_t*r=n.ram; uint8_t p=m.p1[f];
    if(f>=from&&((f-from)%every==0||r[0x785]==16)){
      printf("f%d %c%c%c%c%c%c x=%d y=%02X sx=%d L=%d sc=%2d st=%d stat=%d sz=%d dir=%d\n",f,
      p&0x80?'R':'-',p&0x40?'L':'-',p&0x20?'D':'-',p&0x10?'U':'-',p&1?'A':'-',p&2?'B':'-',
      r[0x6d]*256+r[0x86],r[0xce],(r[0x86]-r[0x71c])&255,r[0x71a]*256+r[0x71c],r[0x785],r[0x1d],r[0x756],r[0x754],r[0x33]);}
    if(getenv("PNG")&&f==atoi(getenv("PNGAT"))){char path[512];snprintf(path,sizeof path,"%s%d.png",getenv("PNG"),f);render_png(&n,path,2,1);}
  }
}
