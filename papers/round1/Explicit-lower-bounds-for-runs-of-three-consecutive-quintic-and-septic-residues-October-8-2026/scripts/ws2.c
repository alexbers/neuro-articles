// memory-lean WalkSAT for chi: primes<=L -> Z/K, default value DEF on primes, no run of M zeros in [1,L]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int K,M,DEF; static long L;
static unsigned char *g, *val; static int32_t *zpos; static long *zl; static long nz=0, zcap=0;
static int *sp; static int nsp; // primes up to sqrt(L)
static uint64_t rs=0x9E3779B97F4A7C15ULL; static inline uint64_t rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline int wz(long r){ if(r<1||r+M-1>L) return 0; for(int i=0;i<M;i++) if(val[r+i]) return 0; return 1; }
static inline void zadd(long r){ if(zpos[r]>=0) return; if(nz==zcap){zcap=zcap?2*zcap:1024; zl=realloc(zl,zcap*sizeof(long));} zpos[r]=nz; zl[nz++]=r; }
static inline void zdel(long r){ int32_t i=zpos[r]; if(i<0) return; long last=zl[--nz]; zl[i]=last; zpos[last]=i; zpos[r]=-1; }
static inline int vp(long n,long p){ int e=0; while(n%p==0){n/=p;e++;} return e; }
static long delta(long p,int d){
  long before=0,after=0,lastr=0;
  for(long n=p;n<=L;n+=p){ long r0=n-M+1; if(r0<=lastr) r0=lastr+1; for(long r=r0;r<=n;r++) before+=wz(r); lastr=n; }
  for(long n=p;n<=L;n+=p) val[n]=(val[n]+vp(n,p)*d)%K;
  lastr=0; for(long n=p;n<=L;n+=p){ long r0=n-M+1; if(r0<=lastr) r0=lastr+1; for(long r=r0;r<=n;r++) after+=wz(r); lastr=n; }
  for(long n=p;n<=L;n+=p) val[n]=(val[n]+vp(n,p)*(K-d))%K;
  return after-before;
}
static void apply(long p,int d){
  long lastr=0;
  for(long n=p;n<=L;n+=p) val[n]=(val[n]+vp(n,p)*d)%K;
  g[p]=(g[p]+d)%K;
  for(long n=p;n<=L;n+=p){ long r0=n-M+1; if(r0<=lastr) r0=lastr+1; for(long r=r0;r<=n;r++){ if(r<1||r+M-1>L) continue; if(wz(r)) zadd(r); else zdel(r);} lastr=n; }
}
static int factor(long n,long*out){ int c=0; for(int i=0;i<nsp && (long)sp[i]*sp[i]<=n;i++){ int p=sp[i]; if(n%p==0){ out[c++]=p; while(n%p==0) n/=p; } } if(n>1) out[c++]=n; return c; }
int main(int argc,char**argv){
  K=atoi(argv[1]); M=atoi(argv[2]); L=atol(argv[3]); long maxit=atol(argv[4]); rs+=atol(argv[5])*0x2545F4914F6CDD1DULL;
  double noise=atof(argv[6]); long smallcut=atol(argv[7]); DEF=atoi(argv[8]); const char*init=argc>9?argv[9]:0;
  g=calloc(L+1,1); val=calloc(L+1,1); zpos=malloc((L+1)*sizeof(int32_t));
  for(long i=0;i<=L;i++) zpos[i]=-1;
  // primality via sieve on val temporarily (val used as composite flag)
  unsigned char *comp=calloc(L+1,1); long s=1; while((s+1)*(s+1)<=L) s++;
  for(long i=2;i*i<=L;i++) if(!comp[i]) for(long j=i*i;j<=L;j+=i) comp[j]=1;
  nsp=0; sp=malloc(sizeof(int)*(s+2)); for(long i=2;i<=s;i++) if(!comp[i]) sp[nsp++]=i;
  for(long i=2;i<=L;i++) g[i]= comp[i]?0:DEF;   // g defined on primes only
  if(init){ FILE*f=fopen(init,"r"); long p; int v; while(fscanf(f,"%ld %d",&p,&v)==2) if(p<=L && !comp[p]) g[p]=v; fclose(f); }
  // compute val by sieve: val[n] = sum g(p) v_p(n)
  unsigned char *isp=malloc(L+1); for(long i=0;i<=L;i++) isp[i]=(i>=2 && !comp[i]); 
  memset(val,0,L+1);
  for(long p=2;p<=L;p++) if(isp[p] && g[p]){ for(long q=p;q<=L;q*=p){ for(long n=q;n<=L;n+=q) val[n]=(val[n]+g[p])%K; if(q>L/p) break; } }
  free(isp);
  for(long r=1;r+M-1<=L;r++) if(wz(r)) zadd(r);
  printf("init zeros=%ld\n",nz); fflush(stdout);
  long it;
  for(it=0;it<maxit && nz>0;it++){
    long r=zl[rnd()%nz];
    long cand[64]; int nc=0; long f[32];
    for(int i=0;i<M;i++){ int c=factor(r+i,f); for(int j=0;j<c;j++) if(f[j]>=smallcut || rnd()%8==0) cand[nc++]=f[j]; }
    if(nc==0) for(int i=0;i<M;i++){ int c=factor(r+i,f); for(int j=0;j<c;j++) cand[nc++]=f[j]; }
    long bp=-1; int bd=0; long bdel=1L<<60;
    if((double)(rnd()%10000)/10000.0 < noise){ bp=cand[rnd()%nc]; bd=1+rnd()%(K-1); }
    else for(int c=0;c<nc;c++){ long p=cand[c]; for(int d=1;d<K;d++){ long dl=delta(p,d)*64+(long)(rnd()%64); if(dl<bdel){bdel=dl;bp=p;bd=d;} } }
    apply(bp,bd);
    if(it%1000==0){ printf("it=%ld zeros=%ld\n",it,nz); fflush(stdout); }
  }
  printf("K=%d M=%d L=%ld final zeros=%ld iters=%ld\n",K,M,L,nz,it);
  if(nz==0){ char fn[128]; sprintf(fn,"exc_K%d_M%d_L%ld_D%d.txt",K,M,L,DEF); FILE*fo=fopen(fn,"w"); long ne=0;
    for(long i=2;i<=L;i++) if(!comp[i] && g[i]!=DEF){ fprintf(fo,"%ld %d\n",i,g[i]); ne++; } fclose(fo); printf("saved %s (%ld exceptions)\n",fn,ne); }
  return nz==0?0:1;
}
