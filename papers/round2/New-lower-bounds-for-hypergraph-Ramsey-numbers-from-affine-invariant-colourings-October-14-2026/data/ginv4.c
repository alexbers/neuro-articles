// CNF for G-invariant 2-colourings of 4-subsets of [n] with no K_{k0}^{(4)} in colour 0 and no K_{k1}^{(4)} in colour 1.
// usage: ginv4 genfile k0 k1 > out.cnf   (G transitive; k-sets through vertex 0 enumerated). env ORB=file writes orbit table.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, m; int **g; int *par;
#define HB 25
static int *arena; static long arenan=0, arenacap=0; static long *htab; static FILE*out; static long ncl=0;
static int cmpint(const void*a,const void*b){return *(int*)a-*(int*)b;}
static void emit(int *lits0,int L){
  int lits[256]; memcpy(lits,lits0,sizeof(int)*L); qsort(lits,L,sizeof(int),cmpint);
  unsigned long long h=1469598103934665603ULL; for(int i=0;i<L;i++){h^=(unsigned)lits[i]; h*=1099511628211ULL;}
  long mask=(1L<<HB)-1; long pos=h&mask;
  while(htab[pos]>=0){ long off=htab[pos]; if(arena[off]==L && !memcmp(arena+off+1,lits,sizeof(int)*L)) return; pos=(pos+1)&mask; }
  if(arenan+L+1>arenacap){arenacap=arenacap*2+(1<<20); arena=realloc(arena,sizeof(int)*arenacap);}
  htab[pos]=arenan; arena[arenan]=L; memcpy(arena+arenan+1,lits,sizeof(int)*L); arenan+=L+1;
  for(int i=0;i<L;i++) fprintf(out,"%d ",lits[i]); fprintf(out,"0\n"); ncl++; }
static long tid(int a,int b,int c,int d){ return (((long)a*n+b)*n+c)*n+d; }
static int find(int x){ while(par[x]!=x){par[x]=par[par[x]];x=par[x];} return x; }
static void sort4(int*v){ for(int i=0;i<4;i++)for(int j=i+1;j<4;j++) if(v[j]<v[i]){int t=v[i];v[i]=v[j];v[j]=t;} }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); if(fscanf(f,"%d %d",&n,&m)!=2) return 1;
  g=malloc(sizeof(int*)*m); for(int i=0;i<m;i++){g[i]=malloc(sizeof(int)*n); for(int j=0;j<n;j++) if(fscanf(f,"%d",&g[i][j])!=1) return 1;}
  fclose(f);
  int kk[2]={atoi(argv[2]),atoi(argv[3])};
  long N4=(long)n*n*n*n; par=malloc(sizeof(int)*N4); for(long i=0;i<N4;i++) par[i]=i;
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++)for(int d=c+1;d<n;d++) for(int i=0;i<m;i++){
    int v[4]={g[i][a],g[i][b],g[i][c],g[i][d]}; sort4(v);
    int p=find(tid(a,b,c,d)), q=find(tid(v[0],v[1],v[2],v[3])); if(p!=q) par[p]=q; }
  int *orb=malloc(sizeof(int)*N4); int *rid=malloc(sizeof(int)*N4); for(long i=0;i<N4;i++) rid[i]=-1;
  int norb=0;
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++)for(int d=c+1;d<n;d++){ int p=find(tid(a,b,c,d)); if(rid[p]<0) rid[p]=norb++; orb[tid(a,b,c,d)]=rid[p]; }
  if(getenv("ORB")){ FILE*o=fopen(getenv("ORB"),"w"); for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++)for(int d=c+1;d<n;d++) fprintf(o,"%d %d %d %d %d\n",a,b,c,d,orb[tid(a,b,c,d)]); fclose(o);}
  char *mbuf=NULL; size_t msz=0; out=open_memstream(&mbuf,&msz);
  htab=malloc(sizeof(long)<<HB); for(long i=0;i<(1L<<HB);i++) htab[i]=-1;
  for(int c=0;c<2;c++){
    int k=kk[c]; int s[16]; s[0]=0; int idx[16]; for(int i=1;i<k;i++) idx[i]=i;
    while(1){
      for(int i=1;i<k;i++) s[i]=idx[i];
      int lits[256], L=0;
      for(int x=0;x<k;x++)for(int y=x+1;y<k;y++)for(int z=y+1;z<k;z++)for(int w=z+1;w<k;w++){
        int o=orb[tid(s[x],s[y],s[z],s[w])]; int lit= c==0 ? -(o+1) : (o+1); int dup=0; for(int t=0;t<L;t++) if(lits[t]==lit){dup=1;break;} if(!dup) lits[L++]=lit; }
      emit(lits,L);
      int i=k-1; while(i>=1 && idx[i]==n-k+i) i--; if(i<1) break; idx[i]++; for(int j=i+1;j<k;j++) idx[j]=idx[j-1]+1;
    }
  }
  fclose(out);
  printf("p cnf %d %ld\n", norb, ncl); fwrite(mbuf,1,msz,stdout);
  fprintf(stderr,"orbits %d clauses %ld\n",norb,ncl);
  return 0;
}
