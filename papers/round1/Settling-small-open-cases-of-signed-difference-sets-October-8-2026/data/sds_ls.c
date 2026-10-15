// Local search (simulated annealing) for signed difference sets in abelian groups.
// usage: sds_ls v k lambda seed seconds a1 a2 ... ar   (invariant factors, product = v)
// Prints "FOUND P=[...] N=[...]" (elements as mixed-radix tuples) if a solution is found.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXV 512
static int v, k, lam, r, fac[8];
static int addt[MAXV][MAXV];
static int a[MAXV];
static long C[MAXV];

static unsigned long long rs;
static inline unsigned long long rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void){ return (rnd() >> 11) * (1.0/9007199254740992.0); }

static void decode(int g, int *t){ for(int i=r-1;i>=0;i--){ t[i]=g%fac[i]; g/=fac[i]; } }
static int encode(int *t){ int g=0; for(int i=0;i<r;i++) g=g*fac[i]+t[i]; return g; }

static long cost_all(void){
  long c=0; for(int y=1;y<v;y++){ long d=C[y]-lam; c+=d*d; } return c;
}
static void recompute(void){
  for(int y=0;y<v;y++){ long s=0; for(int h=0;h<v;h++) s+= a[h]*a[addt[h][y]]; C[y]=s; }
}
static int negt[MAXV];
static inline void change2(int g, int nw){
  int d = nw - a[g];
  if(!d) return;
  for(int y=1;y<v;y++){
    int gp = addt[g][y];
    int gm = addt[g][negt[y]];
    // C[y] = sum_h a_h a_{h+y}; terms with h=g: a_g a_{g+y}; with h+y=g: a_{g-y} a_g
    C[y] += (long)d * (a[gp] + a[gm]);
  }
  a[g]=nw;
}

int main(int argc, char **argv){
  if(argc<7){ fprintf(stderr,"usage\n"); return 1; }
  v=atoi(argv[1]); k=atoi(argv[2]); lam=atoi(argv[3]);
  unsigned long long seed=strtoull(argv[4],0,10); double secs=atof(argv[5]);
  r=argc-6; int prod=1; for(int i=0;i<r;i++){ fac[i]=atoi(argv[6+i]); prod*=fac[i]; }
  if(prod!=v || v>MAXV){ fprintf(stderr,"bad group\n"); return 1; }
  long s2 = (long)lam*(v-1)+k; long s=(long)floor(sqrt((double)s2)+0.5);
  if(s*s!=s2){ fprintf(stderr,"not square\n"); return 1; }
  int np=(k+s)/2, nn=(k-s)/2;
  int t1[8],t2[8],t3[8];
  for(int g=0;g<v;g++) for(int h=0;h<v;h++){ decode(g,t1); decode(h,t2); for(int i=0;i<r;i++) t3[i]=(t1[i]+t2[i])%fac[i]; addt[g][h]=encode(t3); }
  for(int g=0;g<v;g++){ decode(g,t1); for(int i=0;i<r;i++) t3[i]=(fac[i]-t1[i])%fac[i]; negt[g]=encode(t3); }
  rs = seed*2654435761ULL + 88172645463325252ULL;
  clock_t start=clock();
  long best_overall=1L<<60; long restarts=0;
  while((double)(clock()-start)/CLOCKS_PER_SEC < secs){
    restarts++;
    // random init
    int perm[MAXV]; for(int i=0;i<v;i++) perm[i]=i;
    for(int i=v-1;i>0;i--){ int j=rnd()%(i+1); int t=perm[i]; perm[i]=perm[j]; perm[j]=t; }
    for(int i=0;i<v;i++) a[perm[i]] = i<np ? 1 : (i<np+nn ? -1 : 0);
    recompute();
    long cur=cost_all(), best=cur;
    double T=2.0+ (double)lam*0.0;
    long iters = 0, maxit = 200000L + 2000L*v;
    double T0=3.0, T1=0.05;
    for(iters=0; iters<maxit && cur>0; iters++){
      T = T0*pow(T1/T0, (double)iters/maxit);
      int g1, g2;
      do { g1=rnd()%v; g2=rnd()%v; } while(a[g1]==a[g2]);
      int v1=a[g1], v2=a[g2];
      change2(g1, v2); change2(g2, v1);
      long nc=cost_all();
      long dlt=nc-cur;
      if(dlt<=0 || urand() < exp(-(double)dlt/T)){ cur=nc; if(cur<best) best=cur; }
      else { change2(g2, v2); change2(g1, v1); }
    }
    if(best<best_overall) best_overall=best;
    if(cur==0){
      // verify from scratch
      recompute();
      int ok = (C[0]==k); for(int y=1;y<v;y++) if(C[y]!=lam) ok=0;
      if(!ok){ fprintf(stderr,"verify fail\n"); continue; }
      printf("FOUND v=%d k=%d lam=%d G=[",v,k,lam); for(int i=0;i<r;i++) printf("%d%s",fac[i],i<r-1?",":"");
      printf("] P=["); int first=1;
      for(int g=0;g<v;g++) if(a[g]==1){ decode(g,t1); printf("%s",first?"":","); first=0; if(r>1) printf("["); for(int i=0;i<r;i++) printf("%d%s",t1[i],i<r-1?",":""); if(r>1) printf("]"); }
      printf("] N=["); first=1;
      for(int g=0;g<v;g++) if(a[g]==-1){ decode(g,t1); printf("%s",first?"":","); first=0; if(r>1) printf("["); for(int i=0;i<r;i++) printf("%d%s",t1[i],i<r-1?",":""); if(r>1) printf("]"); }
      printf("] restarts=%ld time=%.1f\n", restarts, (double)(clock()-start)/CLOCKS_PER_SEC);
      return 0;
    }
  }
  printf("NOTFOUND v=%d k=%d lam=%d best=%ld restarts=%ld\n", v,k,lam,best_overall,restarts);
  return 0;
}
