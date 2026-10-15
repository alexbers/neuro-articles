// Independent exhaustive search for regular (v,k,lam,mu) partial difference sets (S=-S, 0 not in S) in Z_{a1} x ... x Z_{ar}.
// Backtracking over inverse-pairs {g,-g} (involutions count as singletons), incremental difference counts; pruning: cnt[y] <= lam if y already
// decided to be in S, cnt[y] <= mu if y already decided to be out of S, cnt[y] <= max(lam,mu) if y is undecided (version 2, stronger pruning).
// usage: pds_ex k lam mu a1 ... ar
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXV 128
static int v,k,lam,mu,r,fac[8],addt[MAXV][MAXV],negt[MAXV];
static int orb[MAXV][2], orbsz[MAXV], norb;
static int S[MAXV], ns=0, inS[MAXV], cnt[MAXV]; static long nsol=0, nodes=0; static int cap; static int orbidx[MAXV], cur_oi;
static void decode(int g,int*t){for(int i=r-1;i>=0;i--){t[i]=g%fac[i];g/=fac[i];}}
static int encode(int*t){int g=0;for(int i=0;i<r;i++)g=g*fac[i]+t[i];return g;}
static inline int lim(int d){ return (orbidx[d]<cur_oi) ? (inS[d]?lam:mu) : cap; }
static int addel(int g){ // returns 0 if pruning; inS[g] must already be set by the caller
  int ok=1;
  for(int i=0;i<ns;i++){int h=S[i]; int d1=addt[g][negt[h]], d2=addt[h][negt[g]]; cnt[d1]++; cnt[d2]++; if(cnt[d1]>lim(d1)||cnt[d2]>lim(d2)) ok=0;}
  S[ns++]=g; return ok;
}
static void remel(int g){ ns--; for(int i=0;i<ns;i++){int h=S[i]; cnt[addt[g][negt[h]]]--; cnt[addt[h][negt[g]]]--;} }
static int check_decided(void){ for(int y=1;y<v;y++) if(orbidx[y]<cur_oi && cnt[y]>(inS[y]?lam:mu)) return 0; return 1; }
static void rec(int oi,int remaining){
  nodes++;
  if(remaining==0){
    for(int y=1;y<v;y++){ if(cnt[y]!=(inS[y]?lam:mu)) return; }
    nsol++;
    if(nsol<=3){ printf("SOL:"); for(int i=0;i<ns;i++){int t[8];decode(S[i],t);printf(" (");for(int j=0;j<r;j++)printf("%d%s",t[j],j<r-1?",":"");printf(")");} printf("\n"); }
    return;
  }
  if(oi==norb) return;
  // remaining capacity check
  int avail=0; for(int j=oi;j<norb;j++) avail+=orbsz[j]; if(avail<remaining) return;
  // include orbit oi
  if(orbsz[oi]<=remaining){
    cur_oi=oi+1; inS[orb[oi][0]]=1; if(orbsz[oi]==2) inS[orb[oi][1]]=1;
    int ok=addel(orb[oi][0]); int added=1;
    if(ok && orbsz[oi]==2){ ok=addel(orb[oi][1]); added=2; }
    if(ok) ok=check_decided();
    if(ok) rec(oi+1,remaining-orbsz[oi]);
    if(added==2) remel(orb[oi][1]); remel(orb[oi][0]);
    inS[orb[oi][0]]=0; if(orbsz[oi]==2) inS[orb[oi][1]]=0;
  }
  // exclude orbit oi
  cur_oi=oi+1;
  if(check_decided()) rec(oi+1,remaining);
  cur_oi=oi;
}
int main(int argc,char**argv){
  k=atoi(argv[1]);lam=atoi(argv[2]);mu=atoi(argv[3]); r=argc-4; v=1; for(int i=0;i<r;i++){fac[i]=atoi(argv[4+i]);v*=fac[i];}
  cap=lam>mu?lam:mu;
  int t1[8],t2[8],t3[8];
  for(int g=0;g<v;g++)for(int h=0;h<v;h++){decode(g,t1);decode(h,t2);for(int i=0;i<r;i++)t3[i]=(t1[i]+t2[i])%fac[i];addt[g][h]=encode(t3);}
  for(int g=0;g<v;g++){decode(g,t1);for(int i=0;i<r;i++)t3[i]=(fac[i]-t1[i])%fac[i];negt[g]=encode(t3);}
  int seen[MAXV]={0}; norb=0;
  for(int g=1;g<v;g++){ if(seen[g]) continue; seen[g]=1; orb[norb][0]=g; orbidx[g]=norb; if(negt[g]==g){orbsz[norb]=1;} else {orb[norb][1]=negt[g]; orbidx[negt[g]]=norb; seen[negt[g]]=1; orbsz[norb]=2;} norb++; }
  orbidx[0]=1<<20;
  memset(cnt,0,sizeof cnt); cur_oi=0;
  rec(0,k);
  printf("DONE(v2) k=%d lam=%d mu=%d G=[",k,lam,mu); for(int i=0;i<r;i++)printf("%d%s",fac[i],i<r-1?",":""); printf("] orbits=%d solutions=%ld nodes=%ld\n",norb,nsol,nodes);
  return 0;
}
