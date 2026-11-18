// Beam search for the largest screen X ($86 - $071C) Fire Mario can have on reaching world X >= goal (and, with
// GOALY=yy, standing at Y $yy), from a saved state. Inputs come in 3-frame steps from {R, R+A, none, A, L, L+A}, all
// with B held so no fireball is thrown; goomba 29 must stay alive between the 1-2 pillars once loaded. Score =
// SW*screenX + X + TB*SideCollisionTimer (env SW, TB). usage: screen_x_beam ROM @STATE WIDTH GOALX
#include "../../emu/nes.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { NES s; int parent; uint8_t in; } Node;
static const uint8_t opts[]={0x82,0x83,0x02,0x03,0x42,0x43};
#define NOPT 6
#define STEP 3
#define MAXSTEPS 400
static int hist_parent[MAXSTEPS][4096]; static uint8_t hist_in[MAXSTEPS][4096];
static int px(const NES*n){return n->ram[0x6d]*256+n->ram[0x86];}
static int sx(const NES*n){return (n->ram[0x86]-n->ram[0x71c])&255;}
static int SW=64, TB=0; static int score(const NES*n){return SW*sx(n)+px(n)+TB*n->ram[0x785];}
// goomba 29 (enemy list column 29) must stay alive once spawned: some slot holds a goomba between the pillars
static int g29ok(const NES*n){ if(n->ram[0x71a]*256+n->ram[0x71c]<200) return 1; for(int i=0;i<5;i++){ int x=n->ram[0x6e + i]*256+n->ram[0x87 + i];
  if(n->ram[0xf + i]&&n->ram[0x16 + i]==6&&x>=430&&x<=500&&n->ram[0x1e + i]<2) return 1;} return 0; }
static int cmp(const void*a,const void*b){return score(&((Node*)b)->s)-score(&((Node*)a)->s);}
int main(int argc,char**argv){
  if(nes_load_rom(argv[1])) return 2;
  int W=atoi(argv[3]), goal=atoi(argv[4]); if(W>4096)W=4096; if(getenv("SW")) SW=atoi(getenv("SW")); if(getenv("TB")) TB=atoi(getenv("TB"));
  Node *beam=calloc(W,sizeof(Node)), *next=calloc((size_t)W*NOPT,sizeof(Node)); int nb=1;
  FILE*f=fopen(argv[2]+1,"rb");fread(&beam[0].s,sizeof(NES),1,f);fclose(f); beam[0].parent=-1;
  int best=-1, bestStep=-1, bestIdx=-1;
  for(int step=0;step<MAXSTEPS&&nb;step++){
    int nn=0;
    for(int i=0;i<nb;i++) for(int o=0;o<NOPT;o++){
      Node*c=&next[nn]; c->s=beam[i].s; c->parent=i; c->in=opts[o]; int ok=1;
      for(int k=0;k<STEP;k++){ nes_frame(&c->s,opts[o],0); if(c->s.err||c->s.ram[0x0e]!=8||c->s.ram[0x756]!=2||c->s.ram[0xb5]!=1||!g29ok(&c->s)){ok=0;break;} }
      if(ok) nn++;
    }
    qsort(next,nn,sizeof(Node),cmp);
    // dedup on position/speed/camera
    int kept=0;
    for(int i=0;i<nn&&kept<W;i++){ const uint8_t*r=next[i].s.ram; int dup=0;
      for(int j=0;j<kept;j++){ const uint8_t*q=beam[j].s.ram;
        if(q[0x86]==r[0x86]&&q[0x6d]==r[0x6d]&&q[0xce]==r[0xce]&&q[0x57]==r[0x57]&&q[0x9f]==r[0x9f]&&q[0x71c]==r[0x71c]&&q[0x400]==r[0x400]&&q[0x785]==r[0x785]){dup=1;break;} }
      if(dup) continue;
      // nodes that reached the goal are recorded and dropped from the beam
      if(px(&next[i].s)>=goal&&(!getenv("GOALY")||(next[i].s.ram[0xce]==strtol(getenv("GOALY"),0,16)&&next[i].s.ram[0x1d]==0))){ if(sx(&next[i].s)>best){best=sx(&next[i].s);bestStep=step;bestIdx=kept;
          hist_parent[step][kept]=next[i].parent; hist_in[step][kept]=next[i].in;
          // reconstruct now
          char buf[8192]; int len=0; int idx=kept;
          uint8_t seq[MAXSTEPS]; for(int s=step;s>=0;s--){ seq[s]=hist_in[s][idx]; idx=hist_parent[s][idx]; }
          for(int s=0;s<=step;){int e=s; while(e<=step&&seq[e]==seq[s]) e++; len+=snprintf(buf+len,sizeof buf-len,"%d:%02X,",(e-s)*STEP,seq[s]); s=e;}
          printf("step %d: reached X %d with screen X %d (L %d) | %s\n",step,px(&next[i].s),best,px(&next[i].s)-best,buf); fflush(stdout); }
        continue; }
      Node tmp=next[i]; beam[kept]=tmp; hist_parent[step][kept]=tmp.parent; hist_in[step][kept]=tmp.in; kept++;
    }
    // re-point parents: beam[] now holds this step's nodes; parents refer to previous step's indices (already stored)
    nb=kept;
    if(step%20==0){ int bx=0,bs=0; for(int i=0;i<nb;i++){ if(px(&beam[i].s)>bx)bx=px(&beam[i].s); if(sx(&beam[i].s)>bs)bs=sx(&beam[i].s);} fprintf(stderr,"step %d: beam %d, max X %d, max screen X %d\n",step,nb,bx,bs); }
  }
  printf("best screen X at X>=%d: %d\n",goal,best);
}
