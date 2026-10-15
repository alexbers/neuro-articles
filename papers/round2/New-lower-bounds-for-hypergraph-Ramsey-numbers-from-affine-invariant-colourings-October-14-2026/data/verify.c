// Verify a 2-colouring of triples of [n]: input file lines "x y z" (red triples). Checks for red K_a and blue K_b (3-uniform).
#include <stdio.h>
#include <stdlib.h>
int n,a,b; unsigned char *R;
#define T(x,y,z) R[((x)*n+(y))*n+(z)]
int main(int argc,char**argv){
  n=atoi(argv[1]); a=atoi(argv[2]); b=atoi(argv[3]); R=calloc(n*n*n,1);
  FILE*f=fopen(argv[4],"r"); int x,y,z,cnt=0; while(fscanf(f,"%d %d %d",&x,&y,&z)==3){ int v[3]={x,y,z}; for(int i=0;i<3;i++)for(int j=0;j<3;j++)for(int k=0;k<3;k++) if(i!=j&&j!=k&&i!=k) T(v[i],v[j],v[k])=1; cnt++; }
  printf("red triples %d of %d\n",cnt,n*(n-1)*(n-2)/6);
  // generic clique search: find set of size k all of whose triples have colour c
  long bad=0;
  for(int c=1;c>=0;c--){ int k= c? a : b; int s[16]; int d=0; s[0]=-1;
    // iterative DFS over increasing sequences with pruning
    int depth=0; s[0]=-1;
    while(depth>=0){
      s[depth]++;
      if(s[depth]>=n){ depth--; continue; }
      int v=s[depth], ok=1;
      for(int i=0;i<depth && ok;i++) for(int j=i+1;j<depth && ok;j++) if(T(s[i],s[j],v)!=c) ok=0;
      if(!ok) continue;
      if(depth==k-1){ bad++; if(bad<5){printf("mono colour %d:",c); for(int i=0;i<k;i++) printf(" %d",s[i]); printf("\n");} continue; }
      depth++; s[depth]=s[depth-1];
    }
  }
  printf("monochromatic forbidden sets: %ld\n",bad);
  return bad?1:0;
}
