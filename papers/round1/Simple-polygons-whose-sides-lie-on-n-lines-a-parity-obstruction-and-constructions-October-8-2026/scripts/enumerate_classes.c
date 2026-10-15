// Usage: gcc -O2 -o enumerate_classes enumerate_classes.c && ./enumerate_classes 9   (n odd, n <= 9 in minutes)
// Exhaustive enumeration of commutation classes of reduced words of w0 in S_n (= simple wiring
// diagrams), via lexicographic normal forms; records distribution of #components of the
// alternating 2-factor G and checks the parity of #A-crossings.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 11
static int n, N;
static int perm[MAXN+1];
static int word[64];
static int order[MAXN+1][MAXN];     // order[w][k] = id of k-th crossing of wire w
static int cnt[MAXN+1];
static long long classes=0;
static long long dist[64];
static long long badA=0, badCycle=0;
static int predicted;
static int par[128], pos1[128], pos2[128];
static int find(int x){ while(par[x]!=x){ par[x]=par[par[x]]; x=par[x]; } return x; }
static void leaf(void){
    classes++;
    // vertices: crossing ids 0..N-1 ; union-find over G edges
    for(int c=0;c<N;c++){ par[c]=c; pos1[c]=pos2[c]=0; }
    for(int w=1;w<=n;w++) for(int k=0;k<n-1;k++){ int c=order[w][k]; if(pos1[c]==0) pos1[c]=k+1; else pos2[c]=k+1; }
    for(int w=1;w<=n;w++) for(int k=0;k<n-1;k+=2){ int a=order[w][k], b=order[w][k+1]; int ra=find(a), rb=find(b); if(ra!=rb) par[ra]=rb; }
    int comps=0; static int acount[128];
    for(int c=0;c<N;c++){ acount[c]=0; }
    for(int c=0;c<N;c++){ if(find(c)==c) comps++; }
    int A=0;
    for(int c=0;c<N;c++){ if(pos1[c]%2==0 && pos2[c]%2==0){ A++; acount[find(c)]++; } }
    for(int c=0;c<N;c++){ if(find(c)==c && acount[c]%2==0) badCycle++; }
    if((A&1)!=predicted) badA++;
    dist[comps]++;
}
static int cid[MAXN+1][MAXN+1];
static void dfs(int depth){
    if(depth==N){ leaf(); return; }
    for(int i=0;i<n-1;i++){
        int u=perm[i], v=perm[i+1];
        if(u>v) continue;
        int ok=1;
        for(int t=depth-1;t>=0;t--){ int j=word[t]; if(abs(j-i)>=2){ if(j>i){ ok=0; break; } } else break; }
        if(!ok) continue;
        word[depth]=i; perm[i]=v; perm[i+1]=u;
        int c=cid[u][v]; order[u][cnt[u]++]=c; order[v][cnt[v]++]=c;
        dfs(depth+1);
        cnt[u]--; cnt[v]--; perm[i]=u; perm[i+1]=v;
    }
}
int main(int argc,char**argv){
    n=atoi(argv[1]); N=n*(n-1)/2; int r=(n-1)/2; predicted=(r*(r+1)/2)&1;
    int id=0; for(int u=1;u<=n;u++) for(int v=u+1;v<=n;v++) cid[u][v]=id++;
    for(int i=0;i<n;i++) perm[i]=i+1;
    dfs(0);
    printf("n=%d: commutation classes=%lld; predicted #A parity=%d; words with wrong #A parity=%lld; cycles with even #A=%lld\n", n, classes, predicted, badA, badCycle);
    printf("components distribution:"); for(int k=1;k<64;k++) if(dist[k]) printf(" %d:%lld", k, dist[k]); printf("\n");
    return 0;
}
