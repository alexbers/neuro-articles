// KMY-style search: cost = sum_w m_w (W(w)^2 - 2^n)^2 (= 2^n * sum of squares of autocorrelation), single-orbit flips,
// steepest descent with tabu; track absolute indicator Delta and Walsh zeros.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int k, N; static int *sz; static int *C;
static unsigned long long rs;
static inline unsigned long long rnd(){ rs ^= rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
int main(int argc,char**argv){
  if(argc<8){fprintf(stderr,"usage: acls4 file n target maxit seed restarts tabu [pw]\n");return 1;}
  FILE*fp=fopen(argv[1],"rb"); int n=atoi(argv[2]); N=1<<n; int T=atoi(argv[3]); long maxit=atol(argv[4]); rs=atoll(argv[5])*0x9E3779B97F4A7C15ULL+5; int restarts=atoi(argv[6]); int tabulen=atoi(argv[7]); double pw = argc>8? atof(argv[8]) : 2.0;
  if(fread(&k,4,1,fp)!=1) return 1; sz=malloc(4*k); C=malloc(4L*k*k); if(fread(sz,4,k,fp)!=(size_t)k) return 1; if(fread(C,4,(size_t)k*k,fp)!=(size_t)k*k) return 1; fclose(fp);
  int *s=malloc(4*k); long *W=malloc(8*k), *Rv=malloc(8*k); long *tabu=malloc(8*k);
  long bestD=1L<<40, bestDz=1L<<40;
  for(int rr=0;rr<restarts;rr++){
    for(int i=0;i<k;i++){ s[i]=(rnd()&1)?1:-1; tabu[i]=-1; }
    for(int j=0;j<k;j++){ long w=0; for(int i=0;i<k;i++) w+=(long)C[i*k+j]*s[i]; W[j]=w; }
    long runbest=1L<<40;
    for(long it=0;it<maxit;it++){
      double bestc=1e300; int bp=-1;
      for(int p=0;p<k;p++){ if(tabu[p]>it) continue;
        int *Cp=C+(long)p*k; double c=0; int sp=s[p];
        for(int j=0;j<k;j++){ long w=W[j]-2L*sp*Cp[j]; double e=fabs((double)(w*w-N)); c+= sz[j]*(pw==2.0? e*e : pow(e,pw)); }
        if(c<bestc || (c==bestc && (rnd()&1))){bestc=c;bp=p;}
      }
      if(bp<0) continue;
      { int *Cp=C+(long)bp*k; for(int j=0;j<k;j++) W[j]-=2L*s[bp]*Cp[j]; }
      s[bp]=-s[bp]; tabu[bp]=it+tabulen+(tabulen? rnd()%3:0);
      for(int j=0;j<k;j++){ long t=0; for(int i=0;i<k;i++) t+=W[i]*W[i]*(long)C[i*k+j]; Rv[j]=t/N; }
      long D=0; for(int j=1;j<k;j++){ long a=labs(Rv[j]); if(a>D) D=a; }
      int hasz=0; long mw=0; for(int j=0;j<k;j++){ if(W[j]==0) hasz=1; if(labs(W[j])>mw) mw=labs(W[j]); }
      if(D<runbest) runbest=D;
      if(D<bestD){ bestD=D; fprintf(stderr,"r%d it%ld Delta=%ld (walsh0=%d maxW=%ld)\n",rr,it,D,hasz,mw); }
      if(hasz && D<bestDz){ bestDz=D; printf("r%d it%ld ZERO Delta=%ld maxW=%ld s=",rr,it,D,mw); for(int i=0;i<k;i++) putchar(s[i]>0?'0':'1'); printf("\n"); fflush(stdout);
        if(D<=T){ printf("FOUND\n"); fflush(stdout); return 0; } }
    }
    fprintf(stderr,"restart %d runbest %ld\n",rr,runbest);
  }
  printf("bestD=%ld bestDz=%ld\n",bestD,bestDz); return 0;
}
