// Exhaustive search for (v,k,lambda) signed difference sets in an abelian group
// G = Z_{a1} x ... x Z_{ar}.
// WLOG (translation) the support contains 0, and (negation D -> -D) the sign at 0 is +1.
// Supports are enumerated by backtracking; for each support S we require
// c_y = |S cap (S - y)| >= |lambda| and c_y = lambda (mod 2) for all y != 0,
// then signs are enumerated by backtracking with pruning on the number of
// sign-agreeing / sign-disagreeing pairs at every shift.
// usage: sds_ex v k lambda a1 ... ar   [prints every solution with |P|-|N| = +s, up to translation]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXV 128
static int v,k,lam,r,fac[8];
static int addt[MAXV][MAXV], negt[MAXV];
static int inS[MAXV], Sl[MAXV], c[MAXV];
static long nsupp=0, nsurv=0, nsol=0;
static int sgn[MAXV]; // 0 = unassigned, +1/-1
static int eqc[MAXV], neqc[MAXV], needeq[MAXV], needneq[MAXV];
static int np_, nn_;
static int maxprint=1000000;

static void decode(int g, int *t){ for(int i=r-1;i>=0;i--){ t[i]=g%fac[i]; g/=fac[i]; } }
static int encode(int *t){ int g=0; for(int i=0;i<r;i++) g=g*fac[i]+t[i]; return g; }

static void printsol(void){
  int t[8]; int P=0,N=0; for(int i=0;i<k;i++){ if(sgn[Sl[i]]>0)P++; else N++; }
  int flip = (P<N) ? -1 : 1;
  printf("SOL P=[");
  int first=1;
  for(int g=0;g<v;g++) if(inS[g] && sgn[g]*flip>0){ decode(g,t); printf("%s",first?"":","); first=0; if(r>1)printf("["); for(int i=0;i<r;i++) printf("%d%s",t[i],i<r-1?",":""); if(r>1)printf("]"); }
  printf("] N=["); first=1;
  for(int g=0;g<v;g++) if(inS[g] && sgn[g]*flip<0){ decode(g,t); printf("%s",first?"":","); first=0; if(r>1)printf("["); for(int i=0;i<r;i++) printf("%d%s",t[i],i<r-1?",":""); if(r>1)printf("]"); }
  printf("]\n");
}

// assign sign to support element index idx
static void signs(int idx){
  if(idx==k){
    // full check
    for(int y=1;y<v;y++){ int s=0; for(int i=0;i<k;i++){ int g=Sl[i]; int h=addt[g][y]; if(inS[h]) s+=sgn[g]*sgn[h]; } if(s!=lam) return; }
    nsol++; if(nsol<=maxprint) printsol();
    return;
  }
  int g=Sl[idx];
  for(int sv=1; sv>=-1; sv-=2){
    if(idx==0 && sv==-1) break; // sign at 0 is +1 WLOG
    // pairs (g, g+y) and (g-y, g) with already-assigned partner
    int ok=1; int y;
    int touched_e[2*MAXV], touched_n[2*MAXV], te=0, tn=0;
    sgn[g]=sv;
    for(int j=0;j<idx && ok;j++){
      int h=Sl[j];
      // pair contributes to shift y1 = h - g (g + y1 = h) and y2 = g - h (h + y2 = g)
      int y1 = addt[h][negt[g]], y2 = addt[g][negt[h]];
      int same = (sgn[h]==sv);
      int ys[2]={y1,y2}; int cnt = (y1==y2)?1:2;
      for(int q=0;q<cnt;q++){
        y=ys[q];
        int mult = (y1==y2)?2:1; // if y1==y2 the ordered pair appears twice for that shift
        if(same){ eqc[y]+=mult; touched_e[te++]=y*4+mult; if(eqc[y]>needeq[y]) ok=0; }
        else { neqc[y]+=mult; touched_n[tn++]=y*4+mult; if(neqc[y]>needneq[y]) ok=0; }
      }
    }
    if(ok) signs(idx+1);
    for(int i=0;i<te;i++) eqc[touched_e[i]/4]-=touched_e[i]%4;
    for(int i=0;i<tn;i++) neqc[touched_n[i]/4]-=touched_n[i]%4;
    sgn[g]=0;
  }
}

static void check_support(void){
  nsupp++;
  for(int y=1;y<v;y++){
    if(c[y] < abs(lam)) return;
    if(((c[y]-lam)%2+2)%2) return;
  }
  nsurv++;
  for(int y=1;y<v;y++){ needeq[y]=(c[y]+lam)/2; needneq[y]=(c[y]-lam)/2; eqc[y]=0; neqc[y]=0; }
  signs(0);
}

// add element g to S, updating c[y] = #{h in S : h+y in S}
static void addel(int g, int d){
  // pairs (g, h) with h in S: shift h-g and g-h
  for(int i=0;i<d;i++){ int h=Sl[i]; c[addt[h][negt[g]]]++; c[addt[g][negt[h]]]++; }
  Sl[d]=g; inS[g]=1;
}
static void remel(int g, int d){
  inS[g]=0;
  for(int i=0;i<d;i++){ int h=Sl[i]; c[addt[h][negt[g]]]--; c[addt[g][negt[h]]]--; }
}

static void supp(int d, int next){
  if(d==k){ check_support(); return; }
  for(int g=next; g<=v-(k-d); g++){
    addel(g,d);
    supp(d+1,g+1);
    remel(g,d);
  }
}

int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage\n");return 1;}
  v=atoi(argv[1]);k=atoi(argv[2]);lam=atoi(argv[3]); r=argc-4; int prod=1;
  for(int i=0;i<r;i++){fac[i]=atoi(argv[4+i]); prod*=fac[i];}
  if(prod!=v||v>MAXV){fprintf(stderr,"bad\n");return 1;}
  if(getenv("MAXPRINT")) maxprint=atoi(getenv("MAXPRINT"));
  int t1[8],t2[8],t3[8];
  for(int g=0;g<v;g++)for(int h=0;h<v;h++){decode(g,t1);decode(h,t2);for(int i=0;i<r;i++)t3[i]=(t1[i]+t2[i])%fac[i];addt[g][h]=encode(t3);}
  for(int g=0;g<v;g++){decode(g,t1);for(int i=0;i<r;i++)t3[i]=(fac[i]-t1[i])%fac[i];negt[g]=encode(t3);}
  memset(c,0,sizeof c);
  // 0 in support
  addel(0,0);
  supp(1,1);
  printf("DONE v=%d k=%d lam=%d supports=%ld surviving=%ld solutions(sign at 0 = +1, support containing 0)=%ld\n",v,k,lam,nsupp,nsurv,nsol);
  return 0;
}
