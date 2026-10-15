// CNF for G-invariant r-colourings of triples of [n] with no K_{k_c}^{(3)} in colour c.
// usage: ginv genfile k_0 k_1 ... k_{r-1} > out.cnf      (genfile: n m, then m lines of n ints)
// Assumes G transitive: only k-sets containing vertex 0 are enumerated (enough up to G).
// Variables: r==2: x_o (true = colour 0... careful): we use one var per orbit o: true=colour 0, false=colour 1.
//            r>=3: x_{o,c} one-hot-at-least.  Writes orbit table to stderr-file "orbits.txt" if env ORB set.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, m; int **g; int *par;
static int tid(int a,int b,int c){ // a<b<c
  return (a*n+b)*n+c; }
static int find(int x){ while(par[x]!=x){par[x]=par[par[x]];x=par[x];} return x; }
static void sort3(int*a,int*b,int*c){int t; if(*a>*b){t=*a;*a=*b;*b=t;} if(*b>*c){t=*b;*b=*c;*c=t;} if(*a>*b){t=*a;*a=*b;*b=t;}}
int r, kk[8]; int *orb; int norb;
long ncl=0; FILE*out;
#define HB 24
static int *arena; static long arenan=0, arenacap=0; static long *htab; 
static int cmpint(const void*a,const void*b){return *(int*)a-*(int*)b;}
static void emit(int *lits0,int L){
  int lits[64]; memcpy(lits,lits0,sizeof(int)*L); qsort(lits,L,sizeof(int),cmpint);
  unsigned long long h=1469598103934665603ULL; for(int i=0;i<L;i++){h^=(unsigned)lits[i]; h*=1099511628211ULL;}
  long mask=(1L<<HB)-1; long pos=h&mask;
  while(htab[pos]>=0){ long off=htab[pos]; if(arena[off]==L && !memcmp(arena+off+1,lits,sizeof(int)*L)) return; pos=(pos+1)&mask; }
  if(arenan+L+1>arenacap){arenacap=arenacap*2+(1<<20); arena=realloc(arena,sizeof(int)*arenacap);}
  htab[pos]=arenan; arena[arenan]=L; memcpy(arena+arenan+1,lits,sizeof(int)*L); arenan+=L+1;
  for(int i=0;i<L;i++) fprintf(out,"%d ",lits[i]); fprintf(out,"0\n"); ncl++; }
static int var(int o,int c){ if(r==2) return (c==0)? (o+1) : -(o+1); return o*r+c+1; }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); if(fscanf(f,"%d %d",&n,&m)!=2) return 1;
  g=malloc(sizeof(int*)*m); for(int i=0;i<m;i++){g[i]=malloc(sizeof(int)*n); for(int j=0;j<n;j++) if(fscanf(f,"%d",&g[i][j])!=1) return 1;}
  fclose(f);
  r=argc-2; for(int i=0;i<r;i++) kk[i]=atoi(argv[2+i]);
  long N3=(long)n*n*n; par=malloc(sizeof(int)*N3);
  for(long i=0;i<N3;i++) par[i]=i;
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++) for(int i=0;i<m;i++){
    int x=g[i][a],y=g[i][b],z=g[i][c]; sort3(&x,&y,&z);
    int p=find(tid(a,b,c)), q=find(tid(x,y,z)); if(p!=q) par[p]=q; }
  orb=malloc(sizeof(int)*N3); for(long i=0;i<N3;i++) orb[i]=-1;
  int *rootid=malloc(sizeof(int)*N3); for(long i=0;i<N3;i++) rootid[i]=-1;
  norb=0;
  for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++){ int p=find(tid(a,b,c)); if(rootid[p]<0) rootid[p]=norb++; orb[tid(a,b,c)]=rootid[p]; }
  if(getenv("ORB")){ FILE*o=fopen(getenv("ORB"),"w"); for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++) fprintf(o,"%d %d %d %d\n",a,b,c,orb[tid(a,b,c)]); fclose(o);}
  char *mbuf=NULL; size_t msz=0; out=open_memstream(&mbuf,&msz);
  htab=malloc(sizeof(long)<<HB); for(long i=0;i<(1L<<HB);i++) htab[i]=-1;
  int lits[64];
  if(r>=3) for(int o=0;o<norb;o++){ for(int c=0;c<r;c++) lits[c]=var(o,c); emit(lits,r); }
  // forbidden cliques through each anchor vertex (default: vertex 0; env ANCHORS="0,37" for intransitive groups)
  int anchors[64], na=0; { char*e=getenv("ANCHORS"); if(e){ char*t=strdup(e); for(char*tok=strtok(t,",");tok;tok=strtok(0,",")) anchors[na++]=atoi(tok);} else anchors[na++]=0; }
  for(int ai=0;ai<na;ai++)
  for(int c=0;c<r;c++){
    int k=kk[c]; int s[16]; int anc=anchors[ai]; s[0]=anc;
    // enumerate (k-1)-subsets of the other n-1 vertices (as indices 1..n-1 mapped past the anchor)
    int idx[16]; for(int i=1;i<k;i++) idx[i]=i;
    while(1){
      for(int i=1;i<k;i++){ int v=idx[i]-1; s[i]= v<anc ? v : v+1; }
      int L=0;
      for(int x=0;x<k;x++)for(int y=x+1;y<k;y++)for(int z=y+1;z<k;z++){
        int a1=s[x],b1=s[y],c1=s[z]; sort3(&a1,&b1,&c1); int o=orb[tid(a1,b1,c1)]; int lit=-var(o,c); int dup=0; for(int t=0;t<L;t++) if(lits[t]==lit){dup=1;break;} if(!dup) lits[L++]=lit; }
      emit(lits,L);
      int i=k-1; while(i>=1 && idx[i]==n-k+i) i--; if(i<1) break; idx[i]++; for(int j=i+1;j<k;j++) idx[j]=idx[j-1]+1;
    }
  }
  printf("p cnf %d %ld\n", r==2? norb : norb*r, ncl);
  fclose(out); fwrite(mbuf,1,msz,stdout);
  fprintf(stderr,"orbits %d clauses %ld\n",norb,ncl);
  return 0;
}
