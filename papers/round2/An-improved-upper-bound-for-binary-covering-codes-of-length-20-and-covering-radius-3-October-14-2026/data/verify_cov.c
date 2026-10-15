// verify_cov n R codefile : brute force, for every x in F_2^n, min_c popcount(x^c) <= R ; prints max distance and count
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){ int n=atoi(argv[1]), R=atoi(argv[2]); FILE*f=fopen(argv[3],"r"); static unsigned c[1<<20]; int m=0; long long v;
  while(fscanf(f,"%lld",&v)==1){ if(v<0||v>=(1LL<<n)){printf("out of range %lld\n",v);return 1;} c[m++]=(unsigned)v; }
  int maxd=0; long long bad=0;
  for(unsigned x=0;x<(1u<<n);x++){ int best=99; for(int i=0;i<m && best>R;i++){ int d=__builtin_popcount(x^c[i]); if(d<best) best=d; } if(best>maxd) maxd=best; if(best>R) bad++; }
  // distinctness
  int dup=0; for(int i=0;i<m;i++) for(int j=i+1;j<m;j++) if(c[i]==c[j]) dup++;
  printf("n=%d R=%d |C|=%d duplicates=%d words_beyond_R=%lld (max over x of min dist, capped search)=%d\n",n,R,m,dup,bad,maxd); return 0; }
