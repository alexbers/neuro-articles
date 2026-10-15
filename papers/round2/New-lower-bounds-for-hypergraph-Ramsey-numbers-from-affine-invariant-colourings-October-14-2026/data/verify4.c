// verify 2-colouring of 4-sets of [n] (file: red 4-sets): no red K_a^(4), no blue K_b^(4)
#include <stdio.h>
#include <stdlib.h>
int n,A,B; unsigned char *R;
static long id(int a,int b,int c,int d){int v[4]={a,b,c,d}; for(int i=0;i<4;i++)for(int j=i+1;j<4;j++) if(v[j]<v[i]){int t=v[i];v[i]=v[j];v[j]=t;} return (((long)v[0]*n+v[1])*n+v[2])*n+v[3];}
int main(int argc,char**argv){
  n=atoi(argv[1]);A=atoi(argv[2]);B=atoi(argv[3]); R=calloc((long)n*n*n*n,1);
  FILE*f=fopen(argv[4],"r"); int a,b,c,d,cnt=0; while(fscanf(f,"%d %d %d %d",&a,&b,&c,&d)==4){R[id(a,b,c,d)]=1;cnt++;}
  printf("red 4-sets %d\n",cnt); long bad=0;
  for(int col=1;col>=0;col--){ int k=col?A:B; int s[16]; int depth=0; s[0]=-1;
    while(depth>=0){ s[depth]++; if(s[depth]>=n){depth--;continue;} int v=s[depth],ok=1;
      for(int i=0;i<depth&&ok;i++)for(int j=i+1;j<depth&&ok;j++)for(int l=j+1;l<depth&&ok;l++) if(R[id(s[i],s[j],s[l],v)]!=col) ok=0;
      if(!ok) continue; if(depth==k-1){bad++; continue;} depth++; s[depth]=s[depth-1]; } }
  printf("monochromatic forbidden sets: %ld\n",bad); return bad?1:0; }
