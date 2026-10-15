// Memory-efficient compression-guided search for cyclic propus difference families in Z_v, v = p*q,
// blocks invariant under H = <h> acting on the Z_q coordinate only (h = 1 mod p).
// usage: cpq2 v p q h ka kb kd [maxsol]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
#include <complex.h>

#define MAXV 512
#define MAXO 64
#define MAXF 64
static int v, p, q, h, KA, KB, KD; static long long MAXSOL = 0;
static int nO, orbOf[MAXV], osz[MAXO], oel[MAXO][64], negO[MAXO];
static int revp[1024], plist[16][1024], np[16];
static int mF, frep[MAXV]; static double ICT[MAXF][MAXF];
static int mC, crep[MAXV]; static double cC[MAXF][MAXV], sC[MAXF][MAXV];
static double t0;
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static int md(int a, int n) { a %= n; return a < 0 ? a + n : a; }
static uint64_t hkey(const int16_t *k, int n) { uint64_t hh = 1469598103934665603ULL; for (int j = 0; j < n; j++) { hh ^= (uint16_t)k[j]; hh *= 0x100000001b3ULL; hh ^= hh >> 31; } hh *= 0x9E3779B97F4A7C15ULL; hh ^= hh >> 29; return hh; }

// ---------- compressed level ----------
typedef struct { int8_t c[MAXO]; int16_t key[16]; float psd[MAXF]; } Comp;
typedef struct { Comp *v; int n, cap; } CList;
static void cpush(CList *L, Comp *c) { if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 1024; L->v = realloc(L->v, sizeof(Comp) * L->cap); } L->v[L->n++] = *c; }
static int comp_eval(const int8_t *co, int S, double bound, Comp *out) {
    int cy[MAXV]; int sum = 0, en = 0;
    for (int y = 0; y < q; y++) { cy[y] = co[orbOf[y]]; sum += cy[y]; en += cy[y] * cy[y]; }
    if (sum != S) return 0;
    for (int k = 0; k < mC; k++) { double re = 0, im = 0; for (int y = 0; y < q; y++) { re += cy[y] * cC[k][y]; im += cy[y] * sC[k][y]; } double ps = re * re + im * im; if (ps > bound + 1e-6) return 0; out->psd[k] = (float)ps; }
    for (int k = 0; k < mC; k++) { int acc = 0, s = crep[k]; for (int y = 0; y < q; y++) acc += cy[y] * cy[(y + s) % q]; out->key[k] = (int16_t)acc; }
    out->key[mC] = (int16_t)en; memcpy(out->c, co, nO); return 1;
}
static int vals[16], nvals;
static void enum_comp(int sym, int S, double bound, CList *L) {
    int fr[MAXO], nf = 0, done[MAXO] = {0};
    for (int o = 0; o < nO; o++) { if (done[o]) continue; fr[nf++] = o; done[o] = 1; if (sym) done[negO[o]] = 1; }
    long long total = 1; for (int t = 0; t < nf; t++) total *= nvals;
    int8_t co[MAXO]; Comp c;
    for (long long code = 0; code < total; code++) {
        long long r = code;
        for (int t = 0; t < nf; t++) { int val = vals[r % nvals]; r /= nvals; co[fr[t]] = (int8_t)val; if (sym) co[negO[fr[t]]] = (int8_t)val; }
        if (comp_eval(co, S, bound, &c)) cpush(L, &c);
    }
}

// ---------- full level: incremental DFT over orbit patterns ----------
static double complex *G;   // G[(o*(1<<p) + P)*mF + k]
#define GI(o, P, k) G[((size_t)(o) * (1 << p) + (P)) * mF + (k)]
typedef void (*leaf_fn)(const int *pat, const double *psd, void *ctx);
typedef struct { const int8_t *co; int sym; double bound; leaf_fn f; void *ctx; int order[MAXO], nord; } UEnum;
static void udfs(UEnum *E, int t, int *pat, const double complex *acc) {
    if (t == E->nord) {
        double ps[MAXF];
        for (int k = 0; k < mF; k++) { double x = creal(acc[k]), y = cimag(acc[k]); ps[k] = x * x + y * y; if (ps[k] > E->bound + 1e-6) return; }
        E->f(pat, ps, E->ctx); return;
    }
    int o = E->order[t]; int k = (p - E->co[o]) / 2; double complex nacc[MAXF];
    for (int j = 0; j < np[k]; j++) {
        int P = plist[k][j];
        if (E->sym) {
            int no = negO[o];
            if (no == o) { if (revp[P] != P) continue; pat[o] = P; for (int f = 0; f < mF; f++) nacc[f] = acc[f] + GI(o, P, f); }
            else { pat[o] = P; pat[no] = revp[P]; for (int f = 0; f < mF; f++) nacc[f] = acc[f] + GI(o, P, f) + GI(no, revp[P], f); }
        } else { pat[o] = P; for (int f = 0; f < mF; f++) nacc[f] = acc[f] + GI(o, P, f); }
        udfs(E, t + 1, pat, nacc);
    }
}
static void uncompress(const int8_t *co, int sym, double bound, leaf_fn f, void *ctx) {
    UEnum E; E.co = co; E.sym = sym; E.bound = bound; E.f = f; E.ctx = ctx; E.nord = 0;
    int done[MAXO] = {0};
    for (int o = 0; o < nO; o++) { if (done[o]) continue; E.order[E.nord++] = o; done[o] = 1; if (sym) done[negO[o]] = 1; }
    int pat[MAXO]; double complex acc[MAXF]; for (int k = 0; k < mF; k++) acc[k] = 0;
    udfs(&E, 0, pat, acc);
}
static inline void psd2paf(const double *ps, int S, int16_t *paf) {
    double p0 = (double)S * S;
    for (int c = 0; c < mF; c++) { double s = p0; for (int k = 0; k < mF; k++) s += ps[k] * ICT[c][k]; paf[c] = (int16_t)lround(s / v); }
}
static uint64_t packpat(const int *pat) { uint64_t r = 0; for (int o = nO - 1; o >= 0; o--) r = (r << p) | (uint64_t)pat[o]; return r; }
static void unpackpat(uint64_t r, int *pat) { for (int o = 0; o < nO; o++) { pat[o] = (int)(r & ((1u << p) - 1)); r >>= p; } }

// d table entries: (hash, packed pattern)
typedef struct { uint64_t h, pat; } DEnt;
static DEnt *DT; static size_t nD = 0, capD = 0; static int SDG;
static int dcount_only = 0;
static void d_leaf(const int *pat, const double *ps, void *ctx) {
    (void)ctx; if (dcount_only) { nD++; return; }
    int16_t paf[MAXF]; psd2paf(ps, SDG, paf);
    if (nD == capD) { capD = capD ? capD * 2 : (1 << 20); DT = realloc(DT, sizeof(DEnt) * capD); if (!DT) { printf("OOM\n"); exit(1); } }
    DT[nD].h = hkey(paf, mF); DT[nD].pat = packpat(pat); nD++;
}
static int cmpD(const void *a, const void *b) { uint64_t x = ((const DEnt *)a)->h, y = ((const DEnt *)b)->h; return (x > y) - (x < y); }
// lists for a and b
typedef struct { int n, cap; int16_t *paf; float *psd; uint64_t *pat; int S; } FList;
static void l_leaf(const int *pat, const double *ps, void *ctx) {
    FList *L = ctx;
    if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 256; L->paf = realloc(L->paf, 2 * mF * (size_t)L->cap); L->psd = realloc(L->psd, 4 * mF * (size_t)L->cap); L->pat = realloc(L->pat, 8 * (size_t)L->cap); }
    psd2paf(ps, L->S, L->paf + (size_t)mF * L->n);
    for (int k = 0; k < mF; k++) L->psd[(size_t)mF * L->n + k] = (float)ps[k];
    L->pat[L->n] = packpat(pat); L->n++;
}
static void build_seq(const int *pat, int8_t *s) { for (int i = 0; i < v; i++) { int P = pat[orbOf[i % q]]; s[i] = (P >> (i % p) & 1) ? -1 : 1; } }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: v p q h ka kb kd [maxsol]\n"); return 1; }
    v = atoi(argv[1]); p = atoi(argv[2]); q = atoi(argv[3]); h = atoi(argv[4]); KA = atoi(argv[5]); KB = atoi(argv[6]); KD = atoi(argv[7]);
    MAXSOL = argc > 8 ? atoll(argv[8]) : 0;
    t0 = now();
    int hq = h % q; int seen[MAXV] = {0}; nO = 0;
    for (int y = 0; y < q; y++) if (!seen[y]) { int z = y; osz[nO] = 0; do { seen[z] = 1; orbOf[z] = nO; oel[nO][osz[nO]++] = z; z = (int)((long long)z * hq % q); } while (z != y); nO++; }
    for (int o = 0; o < nO; o++) negO[o] = orbOf[md(-oel[o][0], q)];
    for (int k = 0; k <= p; k++) np[k] = 0;
    for (int P = 0; P < (1 << p); P++) { int r = 0; for (int x = 0; x < p; x++) if (P >> x & 1) r |= 1 << md(-x, p); revp[P] = r; int k = __builtin_popcount(P); plist[k][np[k]++] = P; }
    nvals = 0; for (int k = 0; k <= p; k++) vals[nvals++] = p - 2 * k;
    { int sn[MAXV] = {0}; mC = 0; for (int y = 1; y < q; y++) if (!sn[y]) { crep[mC++] = y; int z = y; do { sn[z] = 1; sn[md(-z, q)] = 1; z = (int)((long long)z * hq % q); } while (z != y); } }
    for (int k = 0; k < mC; k++) for (int y = 0; y < q; y++) { double ang = 2 * M_PI * (double)((long long)crep[k] * y % q) / q; cC[k][y] = cos(ang); sC[k][y] = sin(ang); }
    { int sn[MAXV] = {0}; mF = 0; for (int i = 1; i < v; i++) if (!sn[i]) { frep[mF++] = i; int z = i; do { sn[z] = 1; sn[md(-z, v)] = 1; z = (int)((long long)z * h % v); } while (z != i); } }
    for (int k = 0; k < mF; k++) for (int c = 0; c < mF; c++) {
        int sn[MAXV] = {0}; double acc = 0; int z = frep[c];
        do { if (!sn[z]) { sn[z] = 1; acc += cos(2 * M_PI * (double)((long long)frep[k] * z % v) / v); } int nz = md(-z, v); if (!sn[nz]) { sn[nz] = 1; acc += cos(2 * M_PI * (double)((long long)frep[k] * nz % v) / v); } z = (int)((long long)z * h % v); } while (z != frep[c]);
        ICT[k][c] = acc;   // symmetric in (k,c) up to class sizes; used as PAF(rep_c) = (S^2 + sum_k PSD_k * ICT[c][k]) / v
    }
    // NB: PAF(rep_c) = (1/v) sum_{all freq} PSD(f) cos(2 pi f rep_c / v) = (1/v)(S^2 + sum_k PSD(rep_k) * sum_{f in class k} cos(2 pi f rep_c / v))
    {   double tmp[MAXF][MAXF];
        for (int c = 0; c < mF; c++) for (int k = 0; k < mF; k++) {
            int sn[MAXV] = {0}; double acc = 0; int z = frep[k];
            do { if (!sn[z]) { sn[z] = 1; acc += cos(2 * M_PI * (double)((long long)frep[c] * z % v) / v); } int nz = md(-z, v); if (!sn[nz]) { sn[nz] = 1; acc += cos(2 * M_PI * (double)((long long)frep[c] * nz % v) / v); } z = (int)((long long)z * h % v); } while (z != frep[k]);
            tmp[c][k] = acc; }
        memcpy(ICT, tmp, sizeof tmp); }
    G = malloc(sizeof(double complex) * nO * (1 << p) * mF);
    for (int o = 0; o < nO; o++) for (int P = 0; P < (1 << p); P++) for (int k = 0; k < mF; k++) {
        double complex acc = 0;
        for (int e = 0; e < osz[o]; e++) for (int x = 0; x < p; x++) if (P >> x & 1) {
            // position i with i%p = x, i%q = oel[o][e]
            int i; for (i = 0; i < v; i++) if (i % p == x && i % q == oel[o][e]) break;
            acc += -2.0 * cexp(I * 2 * M_PI * (double)((long long)frep[k] * i % v) / v);
        }
        GI(o, P, k) = acc;
    }
    int SA = v - 2 * KA, SB = v - 2 * KB, SD = v - 2 * KD;
    printf("v=%d p=%d q=%d h=%d orbits=%d cclasses=%d fclasses=%d sizes (%d,%d,%d,%d)\n", v, p, q, h, nO, mC, mF, KA, KB, KB, KD); fflush(stdout);
    CList CA = {0}, CB = {0}, CD = {0};
    enum_comp(1, SA, 4.0 * v, &CA); enum_comp(0, SB, 2.0 * v, &CB); enum_comp(0, SD, 4.0 * v, &CD);
    printf("compressed candidates a=%d b=%d d=%d (%.0f s)\n", CA.n, CB.n, CD.n, now() - t0); fflush(stdout);
    uint64_t hs = 1; while (hs < 4 * (uint64_t)CD.n + 16) hs <<= 1;
    int *cht = malloc(sizeof(int) * hs); for (uint64_t i = 0; i < hs; i++) cht[i] = -1;
    for (int i = 0; i < CD.n; i++) { uint64_t hh = hkey(CD.v[i].key, mC + 1) & (hs - 1); while (cht[hh] >= 0) hh = (hh + 1) & (hs - 1); cht[hh] = i; }
    char *needD = calloc(CD.n, 1);
    typedef struct { int a, b; } Pair; Pair *pairs = NULL; long long npairs = 0, cap = 0;
    for (int ia = 0; ia < CA.n; ia++) for (int ib = 0; ib < CB.n; ib++) {
        int ok = 1; for (int k = 0; k < mC; k++) if (CA.v[ia].psd[k] + 2 * CB.v[ib].psd[k] > 4.0 * v + 1e-3) { ok = 0; break; }
        if (!ok) continue;
        int16_t tk[16]; for (int k = 0; k < mC; k++) tk[k] = (int16_t)(-(CA.v[ia].key[k] + 2 * CB.v[ib].key[k]));
        tk[mC] = (int16_t)(4 * v - CA.v[ia].key[mC] - 2 * CB.v[ib].key[mC]); if (tk[mC] < 0) continue;
        uint64_t hh = hkey(tk, mC + 1) & (hs - 1); int found = 0;
        while (cht[hh] >= 0) { int id = cht[hh]; if (memcmp(CD.v[id].key, tk, 2 * (mC + 1)) == 0) { needD[id] = 1; found = 1; } hh = (hh + 1) & (hs - 1); }
        if (found) { if (npairs == cap) { cap = cap ? 2 * cap : 1024; pairs = realloc(pairs, sizeof(Pair) * cap); } pairs[npairs].a = ia; pairs[npairs].b = ib; npairs++; }
    }
    printf("compressed (a,b) pairs %lld (%.0f s)\n", npairs, now() - t0); fflush(stdout);
    if (!npairs) { printf("DONE lookups=0 sols=0\n"); return 0; }
    SDG = SD;
    dcount_only = 1; nD = 0;
    for (int i = 0; i < CD.n; i++) if (needD[i]) uncompress(CD.v[i].c, 0, 4.0 * v, d_leaf, NULL);
    capD = nD + 1; DT = malloc(sizeof(DEnt) * capD); if (!DT) { printf("OOM %zu\n", capD); return 1; }
    printf("d count %zu -> %.1f GB (%.0f s)\n", nD, nD * 16.0 / 1e9, now() - t0); fflush(stdout);
    if (getenv("DMAXGB") && nD * 16.0 / 1e9 > atof(getenv("DMAXGB"))) { printf("too big, abort\n"); return 2; }
    dcount_only = 0; nD = 0;
    for (int i = 0; i < CD.n; i++) if (needD[i]) uncompress(CD.v[i].c, 0, 4.0 * v, d_leaf, NULL);
    qsort(DT, nD, sizeof(DEnt), cmpD);
    printf("d table %zu entries (%.0f s)\n", nD, now() - t0); fflush(stdout);
    // a lists for all a-compressions in pairs
    FList *UA = calloc(CA.n, sizeof(FList)); char *useA = calloc(CA.n, 1);
    for (long long t = 0; t < npairs; t++) useA[pairs[t].a] = 1;
    long long totA = 0;
    for (int i = 0; i < CA.n; i++) if (useA[i]) { UA[i].S = SA; uncompress(CA.v[i].c, 1, 4.0 * v, l_leaf, &UA[i]); totA += UA[i].n; }
    printf("a uncompressed %lld (%.0f s)\n", totA, now() - t0); fflush(stdout);
    // group pairs by b
    int *pcnt = calloc(CB.n + 1, sizeof(int)); for (long long t = 0; t < npairs; t++) pcnt[pairs[t].b + 1]++;
    for (int i = 0; i < CB.n; i++) pcnt[i + 1] += pcnt[i];
    int *pa = malloc(sizeof(int) * npairs); int *fill = calloc(CB.n, sizeof(int));
    for (long long t = 0; t < npairs; t++) pa[pcnt[pairs[t].b] + fill[pairs[t].b]++] = pairs[t].a;
    long long nlook = 0, nsol = 0, nbtot = 0; char fn[256]; sprintf(fn, "csol_v%d_%d_%d_%d_h%d.txt", v, KA, KB, KD, h); FILE *sf = fopen(fn, "a");
    FList UB = {0}; int done_b = 0, nbgroups = 0;
    for (int ib = 0; ib < CB.n; ib++) if (pcnt[ib + 1] > pcnt[ib]) nbgroups++;
    for (int ib = 0; ib < CB.n; ib++) {
        if (pcnt[ib + 1] == pcnt[ib]) continue;
        UB.n = 0; UB.S = SB; uncompress(CB.v[ib].c, 0, 2.0 * v, l_leaf, &UB); nbtot += UB.n;
        for (int r = pcnt[ib]; r < pcnt[ib + 1]; r++) {
            FList *LA = &UA[pa[r]];
            for (int x = 0; x < LA->n; x++) {
                const int16_t *paf_a = LA->paf + (size_t)mF * x; const float *qa = LA->psd + (size_t)mF * x;
                float lim[MAXF]; for (int k = 0; k < mF; k++) lim[k] = (float)((4.0 * v - qa[k]) / 2 + 1e-3);
                for (int y = 0; y < UB.n; y++) {
                    const float *qb = UB.psd + (size_t)mF * y; int ok = 1;
                    for (int k = 0; k < mF; k++) if (qb[k] > lim[k]) { ok = 0; break; }
                    if (!ok) continue;
                    nlook++;
                    const int16_t *paf_b = UB.paf + (size_t)mF * y; int16_t tg[MAXF];
                    for (int k = 0; k < mF; k++) tg[k] = (int16_t)(-(paf_a[k] + 2 * paf_b[k]));
                    uint64_t hh = hkey(tg, mF);
                    // binary search
                    size_t lo = 0, hi = nD;
                    while (lo < hi) { size_t mid = (lo + hi) / 2; if (DT[mid].h < hh) lo = mid + 1; else hi = mid; }
                    for (size_t e = lo; e < nD && DT[e].h == hh; e++) {
                        int pA[MAXO], pB[MAXO], pD[MAXO]; int8_t sa[MAXV], sb[MAXV], sd[MAXV];
                        unpackpat(LA->pat[x], pA); unpackpat(UB.pat[y], pB); unpackpat(DT[e].pat, pD);
                        build_seq(pA, sa); build_seq(pB, sb); build_seq(pD, sd);
                        int good = 1;
                        for (int s = 1; s < v && good; s++) { int acc = 0; for (int i = 0; i < v; i++) { int j = (i + s) % v; acc += sa[i] * sa[j] + 2 * sb[i] * sb[j] + sd[i] * sd[j]; } if (acc) good = 0; }
                        for (int i = 1; i < v; i++) if (sa[i] != sa[v - i]) good = 0;
                        if (!good) continue;
                        nsol++;
                        fprintf(sf, "SOLUTION v=%d ka=%d kb=%d kd=%d H=<%d>\nX1(sym):", v, KA, KB, KD, h);
                        for (int i = 0; i < v; i++) if (sa[i] < 0) fprintf(sf, " %d", i);
                        fprintf(sf, "\nX2=X3:"); for (int i = 0; i < v; i++) if (sb[i] < 0) fprintf(sf, " %d", i);
                        fprintf(sf, "\nX4:"); for (int i = 0; i < v; i++) if (sd[i] < 0) fprintf(sf, " %d", i);
                        fprintf(sf, "\n"); fflush(sf);
                        if (nsol <= 5) { printf("FOUND #%lld (%.0f s)\n", nsol, now() - t0); fflush(stdout); }
                        if (MAXSOL && nsol >= MAXSOL) { printf("MAXSOL\n"); return 0; }
                    }
                }
            }
        }
        done_b++;
        if (done_b % 2000 == 0) { printf("b-groups %d/%d  b-uncomp %lld lookups %lld sols %lld (%.0f s)\n", done_b, nbgroups, nbtot, nlook, nsol, now() - t0); fflush(stdout); }
    }
    printf("DONE lookups=%lld sols=%lld b-uncomp=%lld time=%.0f\n", nlook, nsol, nbtot, now() - t0);
    return 0;
}
