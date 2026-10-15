#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){ int K=atoi(argv[1]),M=atoi(argv[2]); long L=atol(argv[3]);
  unsigned char *om=calloc(L+1,1); int *spf=calloc(L+1,sizeof(int));
  for(long i=2;i<=L;i++) if(!spf[i]) for(long j=i;j<=L;j+=i) if(!spf[j]) spf[j]=i;
  for(long n=2;n<=L;n++) om[n]=om[n/spf[n]]+1;
  int run=0; for(long n=1;n<=L;n++){ if(om[n]%K==0) run++; else run=0; if(run>=M && n>M){ printf("K=%d M=%d first run ends at %ld (start %ld)\n",K,M,n,n-M+1); return 0;} }
  printf("none up to %ld\n",L); }
