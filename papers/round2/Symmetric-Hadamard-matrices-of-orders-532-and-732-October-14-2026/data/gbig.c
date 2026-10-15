// General exhaustive orbit-union MITM search for cyclic propus difference families in Z_v.
// Blocks b (=c), d are unions of H-orbits, a (symmetric) union of <H,-1>-orbits, H = <gens>.
// Condition: PAF_a + 2 PAF_b + PAF_d = 0 off zero.  Table of d (PSD<=4v), lists of a (PSD<=4v), b (PSD<=2v).
// DFT maintained incrementally in the DFS; PAF recovered from PSD (exact rounding).
// usage: gbig v ka kb kd nthreads bucketbits maxsol gen1 [gen2 ...]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
#include <pthread.h>

#define MAXV 256
#define MAXM 128
#define MAXAT 64
static int v, KA, KB, KD, NT, BB; static long long MAXSOL;
static int ngen, gens[8];
static int m, reps[MAXM], csz[MAXM];
static double ICT[MAXM][MAXM];   // PAF(rep_c) = ( PSD0 + sum_k PSD_k * ICT[c][k] ) / v
static double t0;
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
typedef struct { int n; int sz[MAXAT]; int el[MAXAT][64]; double gr[MAXAT][MAXM], gi[MAXAT][MAXM]; } Atoms;
static Atoms ATa, ATb;

static int orbit_of(int i, int *g, int ng, int *out) {
    int n = 0; out[n++] = i;
    for (int k = 0; k < n; k++) for (int t = 0; t < ng; t++) {
        int e = (int)((long long)out[k] * g[t] % v); int dup = 0;
        for (int u = 0; u < n; u++) if (out[u] == e) { dup = 1; break; }
        if (!dup) out[n++] = e;
    }
    return n;
}
static void build_atoms(Atoms *A, int *g, int ng) {
    int seen[MAXV] = {0}; A->n = 0;
    for (int i = 0; i < v; i++) if (!seen[i]) {
        int o[MAXV]; int n = orbit_of(i, g, ng, o);
        if (A->n >= MAXAT || n > 64) { fprintf(stderr, "too many atoms / atom too big\n"); exit(1); }
        A->sz[A->n] = n;
        for (int t = 0; t < n; t++) { A->el[A->n][t] = o[t]; seen[o[t]] = 1; }
        for (int k = 0; k < m; k++) { double re = 0, im = 0; for (int t = 0; t < n; t++) { double ang = 2 * M_PI * (double)((long long)reps[k] * o[t] % v) / v; re += cos(ang); im += sin(ang); } A->gr[A->n][k] = re; A->gi[A->n][k] = im; }
        A->n++;
    }
}
static inline uint64_t hashv(const int16_t *p) {
    uint64_t h = 0x9E3779B97F4A7C15ULL;
    for (int j = 0; j < m; j++) { h ^= (uint16_t)p[j]; h *= 0xff51afd7ed558ccdULL; h ^= h >> 32; }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 29;
    return h;
}
// leaf callback: psd (length m), mask, size k
typedef void (*leaf_fn)(const double *psd, uint64_t mask, int k, void *ctx);
typedef struct { Atoms *A; int k; double bound; leaf_fn f; void *ctx; int tid, nt; long long nodeno; int suffix[MAXAT + 1]; } Enum;
static void dfs(Enum *E, int t, int rem, const double *sr, const double *si, uint64_t mask, int depth) {
    if (depth == 12) { long long id = E->nodeno++; if (id % E->nt != E->tid) return; }
    if (rem == 0) {
        if (depth < 12 && E->tid != 0) return;
        double psd[MAXM];
        for (int k = 0; k < m; k++) { double p = 4 * (sr[k] * sr[k] + si[k] * si[k]); if (p > E->bound + 1e-6) return; psd[k] = p; }
        E->f(psd, mask, E->k, E->ctx); return;
    }
    Atoms *A = E->A;
    if (t == A->n || E->suffix[t] < rem) return;
    if (A->sz[t] <= rem) {
        double nr[MAXM], ni[MAXM];
        for (int k = 0; k < m; k++) { nr[k] = sr[k] + A->gr[t][k]; ni[k] = si[k] + A->gi[t][k]; }
        dfs(E, t + 1, rem - A->sz[t], nr, ni, mask | (1ULL << t), depth + 1);
    }
    dfs(E, t + 1, rem, sr, si, mask, depth + 1);
}
static void *enum_thread(void *arg) {
    Enum *E = arg; E->suffix[E->A->n] = 0;
    for (int t = E->A->n - 1; t >= 0; t--) E->suffix[t] = E->suffix[t + 1] + E->A->sz[t];
    double zr[MAXM] = {0}, zi[MAXM] = {0};
    dfs(E, 0, E->k, zr, zi, 0, 0); return NULL;
}
static void run_enum(Atoms *A, int k, double bound, leaf_fn f, void **ctxs) {
    pthread_t th[16]; Enum *E = calloc(NT, sizeof(Enum));
    for (int i = 0; i < NT; i++) { E[i].A = A; E[i].k = k; E[i].bound = bound; E[i].f = f; E[i].ctx = ctxs[i]; E[i].tid = i; E[i].nt = NT; pthread_create(&th[i], NULL, enum_thread, &E[i]); }
    for (int i = 0; i < NT; i++) pthread_join(th[i], NULL);
    free(E);
}
static inline void psd2paf(const double *psd, int k, int16_t *paf) {
    double p0 = (double)(v - 2 * k) * (v - 2 * k);
    for (int c = 0; c < m; c++) { double s = p0; for (int q = 0; q < m; q++) s += psd[q] * ICT[c][q]; paf[c] = (int16_t)lround(s / v); }
}
// d table
static uint32_t *bcount, *bstart; static uint64_t *tabk, *tabm;
typedef struct { int pass; uint64_t cnt; } DCtx;
static void d_leaf(const double *psd, uint64_t mask, int k, void *vc) {
    DCtx *c = vc; int16_t p[MAXM]; psd2paf(psd, k, p);
    uint64_t h = hashv(p), b = h >> (64 - BB);
    if (c->pass == 0) { __atomic_fetch_add(&bcount[b], 1, __ATOMIC_RELAXED); c->cnt++; }
    else { uint32_t pos = __atomic_fetch_add(&bcount[b], 1, __ATOMIC_RELAXED); tabk[bstart[b] + pos] = h; tabm[bstart[b] + pos] = mask; }
}
typedef struct { int cnt, cap; int16_t *paf; float *psd; uint64_t *mask; } List;
static void l_leaf(const double *psd, uint64_t mask, int k, void *vc) {
    List *l = vc;
    if (l->cnt == l->cap) { l->cap = l->cap ? 2 * l->cap : 4096; l->paf = realloc(l->paf, 2 * m * (size_t)l->cap); l->psd = realloc(l->psd, 4 * m * (size_t)l->cap); l->mask = realloc(l->mask, 8 * (size_t)l->cap); }
    psd2paf(psd, k, l->paf + (size_t)m * l->cnt);
    for (int q = 0; q < m; q++) l->psd[(size_t)m * l->cnt + q] = (float)psd[q];
    l->mask[l->cnt++] = mask;
}
static List LA, LB;
static void merge(List *dst, List *src) {
    for (int i = 0; i < NT; i++) for (int j = 0; j < src[i].cnt; j++) {
        List *l = dst;
        if (l->cnt == l->cap) { l->cap = l->cap ? 2 * l->cap : 4096; l->paf = realloc(l->paf, 2 * m * (size_t)l->cap); l->psd = realloc(l->psd, 4 * m * (size_t)l->cap); l->mask = realloc(l->mask, 8 * (size_t)l->cap); }
        memcpy(l->paf + (size_t)m * l->cnt, src[i].paf + (size_t)m * j, 2 * m); memcpy(l->psd + (size_t)m * l->cnt, src[i].psd + (size_t)m * j, 4 * m); l->mask[l->cnt++] = src[i].mask[j];
    }
}
static void seq_of(Atoms *A, uint64_t mask, int *x) { for (int i = 0; i < v; i++) x[i] = 1; for (int t = 0; t < A->n; t++) if (mask >> t & 1) for (int e = 0; e < A->sz[t]; e++) x[A->el[t][e]] = -1; }
static pthread_mutex_t mtx = PTHREAD_MUTEX_INITIALIZER;
static long long nsol = 0, nlook = 0; static int a_next = 0, a_done = 0; static FILE *solf;
static void report(uint64_t am, uint64_t bm, uint64_t dm) {
    int a[MAXV], b[MAXV], d[MAXV]; seq_of(&ATa, am, a); seq_of(&ATb, bm, b); seq_of(&ATb, dm, d);
    for (int s = 1; s < v; s++) { int y = 0; for (int i = 0; i < v; i++) { int j = (i + s) % v; y += a[i] * a[j] + 2 * b[i] * b[j] + d[i] * d[j]; } if (y) return; }
    for (int i = 1; i < v; i++) if (a[i] != a[v - i]) return;
    pthread_mutex_lock(&mtx); nsol++;
    fprintf(solf, "SOLUTION v=%d ka=%d kb=%d kd=%d gens", v, KA, KB, KD); for (int g = 0; g < ngen; g++) fprintf(solf, " %d", gens[g]);
    fprintf(solf, "\nX1(sym):"); for (int i = 0; i < v; i++) if (a[i] < 0) fprintf(solf, " %d", i);
    fprintf(solf, "\nX2=X3:"); for (int i = 0; i < v; i++) if (b[i] < 0) fprintf(solf, " %d", i);
    fprintf(solf, "\nX4:"); for (int i = 0; i < v; i++) if (d[i] < 0) fprintf(solf, " %d", i);
    fprintf(solf, "\n"); fflush(solf);
    if (nsol <= 3) { printf("FOUND #%lld at %.0f s\n", nsol, now() - t0); fflush(stdout); }
    if (MAXSOL && nsol >= MAXSOL) { printf("MAXSOL reached\n"); fflush(stdout); exit(0); }
    pthread_mutex_unlock(&mtx);
}
static void *worker(void *arg) {
    (void)arg; int16_t tg[MAXM];
    for (;;) {
        pthread_mutex_lock(&mtx); int ia = a_next < LA.cnt ? a_next++ : -1; pthread_mutex_unlock(&mtx);
        if (ia < 0) break;
        const int16_t *pa = LA.paf + (size_t)m * ia; const float *qa = LA.psd + (size_t)m * ia;
        float lim[MAXM]; for (int k = 0; k < m; k++) lim[k] = (float)((4.0 * v - qa[k]) / 2 + 1e-3);
        long long nl = 0;
        for (int ib = 0; ib < LB.cnt; ib++) {
            const float *qb = LB.psd + (size_t)m * ib; int ok = 1;
            for (int k = 0; k < m; k++) if (qb[k] > lim[k]) { ok = 0; break; }
            if (!ok) continue;
            nl++;
            const int16_t *pb = LB.paf + (size_t)m * ib;
            for (int c = 0; c < m; c++) tg[c] = (int16_t)(-(pa[c] + 2 * pb[c]));
            uint64_t h = hashv(tg), b = h >> (64 - BB);
            for (uint32_t e = bstart[b]; e < bstart[b + 1]; e++) if (tabk[e] == h) report(LA.mask[ia], LB.mask[ib], tabm[e]);
        }
        pthread_mutex_lock(&mtx); nlook += nl; a_done++;
        if (a_done % 1000 == 0) { printf("a %d/%d lookups %lld sols %lld t=%.0f\n", a_done, LA.cnt, nlook, nsol, now() - t0); fflush(stdout); }
        pthread_mutex_unlock(&mtx);
    }
    return NULL;
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: v ka kb kd nthreads bucketbits maxsol gen...\n"); return 1; }
    v = atoi(argv[1]); KA = atoi(argv[2]); KB = atoi(argv[3]); KD = atoi(argv[4]); NT = atoi(argv[5]); BB = atoi(argv[6]); MAXSOL = atoll(argv[7]);
    ngen = argc - 8; for (int i = 0; i < ngen; i++) gens[i] = atoi(argv[8 + i]);
    t0 = now();
    int ga[9]; for (int i = 0; i < ngen; i++) ga[i] = gens[i]; ga[ngen] = v - 1;
    { int seen[MAXV] = {0}; m = 0;
      for (int i = 1; i < v; i++) if (!seen[i]) { int o[MAXV]; int n = orbit_of(i, ga, ngen + 1, o); for (int t = 0; t < n; t++) seen[o[t]] = 1; reps[m] = i; csz[m] = n; m++; } }
    for (int c = 0; c < m; c++) for (int q = 0; q < m; q++) {
        int o[MAXV]; int n = orbit_of(reps[q], ga, ngen + 1, o); double acc = 0;
        for (int t = 0; t < n; t++) acc += cos(2 * M_PI * (double)((long long)reps[c] * o[t] % v) / v);
        ICT[c][q] = acc;
    }
    build_atoms(&ATb, gens, ngen); build_atoms(&ATa, ga, ngen + 1);
    printf("v=%d gens", v); for (int i = 0; i < ngen; i++) printf(" %d", gens[i]);
    printf(" atoms a=%d b/d=%d classes=%d sizes (%d,%d,%d,%d)\n", ATa.n, ATb.n, m, KA, KB, KB, KD); fflush(stdout);
    void *ctx[16]; DCtx dc[16];
    bcount = calloc((1ULL << BB) + 1, 4);
    for (int i = 0; i < NT; i++) { dc[i].pass = 0; dc[i].cnt = 0; ctx[i] = &dc[i]; }
    run_enum(&ATb, KD, 4.0 * v, d_leaf, ctx);
    uint64_t tot = 0; for (int i = 0; i < NT; i++) tot += dc[i].cnt;
    printf("d admissible %llu (%.0f s)\n", (unsigned long long)tot, now() - t0); fflush(stdout);
    if (tot > 3500000000ULL) { printf("too many d\n"); return 1; }
    bstart = malloc(((1ULL << BB) + 1) * 4); uint64_t acc = 0;
    for (uint64_t b = 0; b < (1ULL << BB); b++) { bstart[b] = (uint32_t)acc; acc += bcount[b]; bcount[b] = 0; } bstart[1ULL << BB] = (uint32_t)acc;
    tabk = malloc((acc + 1) * 8); tabm = malloc((acc + 1) * 8);
    for (int i = 0; i < NT; i++) dc[i].pass = 1;
    run_enum(&ATb, KD, 4.0 * v, d_leaf, ctx);
    free(bcount);
    List la[16], lb[16]; memset(la, 0, sizeof la); memset(lb, 0, sizeof lb);
    for (int i = 0; i < NT; i++) ctx[i] = &la[i];
    run_enum(&ATa, KA, 4.0 * v, l_leaf, ctx);
    for (int i = 0; i < NT; i++) ctx[i] = &lb[i];
    run_enum(&ATb, KB, 2.0 * v, l_leaf, ctx);
    merge(&LA, la); merge(&LB, lb);
    printf("tables: d %llu, a %d, b %d (%.0f s)\n", (unsigned long long)acc, LA.cnt, LB.cnt, now() - t0); fflush(stdout);
    char fn[256]; sprintf(fn, "gsol_v%d_%d_%d_%d_g%d.txt", v, KA, KB, KD, gens[0]); solf = fopen(fn, "a");
    pthread_t th[16]; for (int i = 0; i < NT; i++) pthread_create(&th[i], NULL, worker, NULL);
    for (int i = 0; i < NT; i++) pthread_join(th[i], NULL);
    printf("DONE lookups=%lld sols=%lld time=%.0f\n", nlook, nsol, now() - t0);
    return 0;
}
