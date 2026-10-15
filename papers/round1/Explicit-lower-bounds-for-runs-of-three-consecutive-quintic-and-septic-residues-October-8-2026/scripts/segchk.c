// segmented verifier: find first run of M consecutive zeros of chi up to L (chi(p)=DEF except listed)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned long long u64;
static long ne=0; static u64 ep[100000]; static int ev[100000];
static int gval(u64 p,int DEF){ for(long i=0;i<ne;i++) if(ep[i]==p) return ev[i]; return DEF; }
int main(int argc,char**argv){ int K=atoi(argv[1]),M=atoi(argv[2]); u64 L=strtoull(argv[3],0,10); int DEF=atoi(argv[4]);
  FILE*f=fopen(argv[5],"r"); u64 p; int v; while(fscanf(f,"%llu %d",&p,&v)==2){ep[ne]=p;ev[ne]=v;ne++;} fclose(f);
  u64 s=1; while((s+1)*(s+1)<=L) s++;
  unsigned char *c=calloc(s+1,1); u64 *pr=malloc(sizeof(u64)*(s/2+10)); long np=0;
  for(u64 i=2;i<=s;i++) if(!c[i]){ pr[np++]=i; for(u64 j=i*i;j<=s;j+=i) c[j]=1; }
  int *gp=malloc(sizeof(int)*np); for(long i=0;i<np;i++) gp[i]=gval(pr[i],DEF);
  // exceptions larger than s need lookup for cofactors; precompute flag
  u64 SEG=1<<24; u64 *rem=malloc(SEG*8); unsigned char *acc=malloc(SEG);
  long run=0; u64 first=0;
  for(u64 a=1;a<=L;a+=SEG){ u64 b=a+SEG; if(b>L+1) b=L+1; u64 n0=a;
    for(u64 n=a;n<b;n++){ rem[n-a]=n; acc[n-a]=0; }
    for(long i=0;i<np;i++){ u64 q=pr[i]; if(q*q>=b && q>b) break; u64 st=((a+q-1)/q)*q; int gq=gp[i];
      for(u64 n=st;n<b;n+=q){ u64 r=rem[n-a]; do{ r/=q; acc[n-a]+=gq; }while(r%q==0); rem[n-a]=r; } }
    for(u64 n=a;n<b;n++){ u64 r=rem[n-a]; int x=acc[n-a]; if(r>1) x+=gval(r,DEF); x%=K;
      if(x==0) run++; else run=0; if(run>=M && !first){ first=n-M+1; printf("first zero run starts at %llu\n",first); fflush(stdout); goto done; } }
  }
  done:
  printf("K=%d M=%d L=%llu exceptions=%ld first=%llu\n",K,M,L,ne,first); return 0; }
