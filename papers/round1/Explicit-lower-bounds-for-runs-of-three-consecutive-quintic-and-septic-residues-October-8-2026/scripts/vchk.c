// independent verifier: chi(p)=DEF except listed; compute chi(n) via smallest-prime-factor recursion; check runs
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){ int K=atoi(argv[1]),M=atoi(argv[2]); long L=atol(argv[3]); int DEF=atoi(argv[4]);
  uint32_t *spf=calloc(L+1,4); unsigned char *v=calloc(L+1,1);
  for(long i=2;i<=L;i++) if(!spf[i]){ spf[i]=i; if(i<=L/i) for(long j=i*i;j<=L;j+=i) if(!spf[j]) spf[j]=i; }
  // exceptions: store in v[p] temporarily as value+1 marker using separate array
  unsigned char *gx=calloc(L+1,1); FILE*f=fopen(argv[5],"r"); long p; int val; long ne=0;
  while(fscanf(f,"%ld %d",&p,&val)==2){ if(spf[p]!=p){printf("NOT PRIME %ld\n",p);return 1;} gx[p]=val+1; ne++; } fclose(f);
  v[1]=0; for(long n=2;n<=L;n++){ long q=spf[n]; int gq= gx[q]? gx[q]-1 : DEF; v[n]=(gq+v[n/q])%K; }
  long run=0, first=-1, cnt=0; for(long n=1;n<=L;n++){ if(v[n]==0) run++; else run=0; if(run>=M){ cnt++; if(first<0) first=n-M+1; } }
  printf("K=%d M=%d L=%ld exceptions=%ld zero-runs=%ld first=%ld\n",K,M,L,ne,cnt,first); return 0; }
