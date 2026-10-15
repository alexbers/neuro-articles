// Search: does there exist completely multiplicative chi: N -> Z/k with no m consecutive zeros among 1..B ?
// DFS over primes in increasing order with conflict-directed backjumping.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int K,M; static long B;
static int *spf; static unsigned char *chi; static long *primes; static int np;
static int *pidx; // index of prime in primes[]
static long nodes=0; static long bestreach=0; static unsigned char *bestchi;
// conflict sets as bitsets over prime indices would be big; use "max culprit level" backjumping (Gaschnig-like) + set via small arrays
// We'll implement conflict-directed backjumping with sorted vectors of prime indices.
typedef struct { int *a; int n, cap; } vec;
static void vpush(vec*v,int x){ if(v->n==v->cap){v->cap=v->cap?2*v->cap:8; v->a=realloc(v->a,v->cap*sizeof(int));} v->a[v->n++]=x; }
static void vunion(vec*d,const vec*s){ for(int i=0;i<s->n;i++){int x=s->a[i],f=0; for(int j=0;j<d->n;j++) if(d->a[j]==x){f=1;break;} if(!f) vpush(d,x);} }
static void addfactors(vec*v,long n){ while(n>1){ int p=spf[n]; int ix=pidx[p]; int f=0; for(int j=0;j<v->n;j++) if(v->a[j]==ix){f=1;break;} if(!f) vpush(v,ix); while(n%p==0) n/=p; } }
// returns 1 if success (assignment found up to B). else fills conflict set cs (prime indices) 
static int dfs(int level, vec*cs){
  nodes++;
  if(level==np) return 1;
  long p=primes[level]; long nextp = (level+1<np)? primes[level+1] : B+1;
  vec acc={0}; 
  int vals[16]; int nv=0;
  // symmetry: if all previous primes have chi 0, restrict to values {0,1}
  int allzero=1; for(int i=0;i<level;i++) if(chi[primes[i]]){allzero=0;break;}
  // safe-value rule for p > sqrt(B): value avoiding -chi(j) for all j<=B/p
  if(p*p>B){ int forb[64]={0}; for(long j=1;j*p<=B;j++) forb[(K-chi[j])%K]=1; for(int v=0;v<K;v++) if(!forb[v]){ vals[nv++]=v; break;} }
  if(nv==0){ if(allzero){vals[nv++]=1; vals[nv++]=0;} else { vals[nv++]=1; for(int v=2;v<K;v++) vals[nv++]=v; vals[nv++]=0; } }
  for(int t=0;t<nv;t++){
    int v=vals[t]; chi[p]=v;
    // propagate n=p..nextp-1 ; check windows ending at n
    int ok=1; vec conf={0};
    for(long n=p;n<nextp;n++){
      if(n!=p){ long q=spf[n]; chi[n]=(chi[q]+chi[n/q])%K; }
      if(n>=M){ int z=1; for(int i=0;i<M;i++) if(chi[n-i]){z=0;break;}
        if(z){ ok=0; for(int i=0;i<M;i++) addfactors(&conf,n-i); if(n-M+1>bestreach){} break; } }
    }
    if(ok){
      long reach=nextp-1; if(reach>bestreach){bestreach=reach; memcpy(bestchi,chi,B+1);}
      vec sub={0};
      int r=dfs(level+1,&sub);
      if(r){ free(sub.a); free(conf.a); free(acc.a); return 1; }
      // if current prime not in sub conflict set, backjump: propagate sub as our conflict
      int in=0; for(int j=0;j<sub.n;j++) if(sub.a[j]==level){in=1;break;}
      if(!in){ cs->n=0; vunion(cs,&sub); free(sub.a); free(conf.a); free(acc.a); return 0; }
      vunion(&acc,&sub); free(sub.a);
    } else { vunion(&acc,&conf); }
    free(conf.a);
  }
  // all values failed: conflict set = acc minus current level
  cs->n=0; for(int j=0;j<acc.n;j++) if(acc.a[j]!=level) vpush(cs,acc.a[j]);
  // NOTE: when safe-rule restricted values, the failure under the safe value implies failure under all (dominance), fine.
  free(acc.a);
  return 0;
}
int main(int argc,char**argv){
  K=atoi(argv[1]); M=atoi(argv[2]); B=atol(argv[3]);
  spf=calloc(B+2,sizeof(int)); chi=calloc(B+2,1); bestchi=calloc(B+2,1); pidx=calloc(B+2,sizeof(int));
  primes=malloc(sizeof(long)*(B/2+10)); np=0;
  for(long i=2;i<=B+1;i++) if(!spf[i]){ for(long j=i;j<=B+1;j+=i) if(!spf[j]) spf[j]=i; }
  for(long i=2;i<=B;i++) if(spf[i]==i){ pidx[i]=np; primes[np++]=i; }
  chi[1]=0;
  // check windows ending at 1..primes[0]-1 : n=1 only
  vec cs={0};
  int r=dfs(0,&cs);
  printf("K=%d M=%d B=%ld result=%s nodes=%ld bestreach=%ld\n",K,M,B,r?"SAT(avoid)":"UNSAT",nodes,bestreach);
  return 0;
}
