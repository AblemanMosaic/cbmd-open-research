/* Faster exact checker for forest negative correlation on simple graphs (graph6 input).
 *
 * Same quantity as fnc.c:  P(lambda) = Z_{G/e} Z_{G/f} - Z_G Z_{G/e/f}  for e < f.
 * Speed-up: for fixed e, with H = G/e, the forests of H containing an edge f = uv decompose by the
 * vertex set B of the tree containing f:
 *     lambda Z_{H/f} = sum_{B : u,v in B} tau_f(H[B]) lambda^{|B|-1} g_H[V(H) \ B],
 * where g_H[S] is the forest polynomial of H[S] (already tabulated by the subset DP for Z_H) and
 * tau_f(H[B]) is the number of spanning trees of H[B] containing (one copy of) f, obtained from the
 * adjugate of the reduced Laplacian:  tau_f = adj[u][u] + adj[v][v] - 2 adj[u][v]  (root r removed;
 * terms with r omitted).  One adjugate per B serves every f.
 * Output format identical to fnc.c (SUMMARY line; -v prints PAIR lines).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef __int128 i128;
#define MAXN 11
#define MAXF (1 << MAXN)

static int64_t taub[MAXF];
static int64_t gtab[MAXF][MAXN];        /* forest polys of induced subgraphs of the current graph */
static int64_t adjt[MAXF][MAXN][MAXN];  /* adjugate of reduced Laplacian of H[B], local indices */
static int conn_ok[MAXF];
#define MAXE 45
static int64_t gE[MAXE][1 << (MAXN - 1)][MAXN];          /* per-edge copies of gtab for G/e */
static int64_t adjE[MAXE][1 << (MAXN - 1)][MAXN - 1][MAXN - 1];
static char connE[MAXE][1 << (MAXN - 1)];

static int64_t det_bareiss(int64_t a[MAXN][MAXN], int m) {
    if (m == 0) return 1;
    int64_t prev = 1; int sign = 1;
    for (int k = 0; k < m - 1; k++) {
        if (a[k][k] == 0) {
            int p = -1;
            for (int i = k + 1; i < m; i++) if (a[i][k] != 0) { p = i; break; }
            if (p < 0) return 0;
            for (int j = 0; j < m; j++) { int64_t t = a[k][j]; a[k][j] = a[p][j]; a[p][j] = t; }
            sign = -sign;
        }
        for (int i = k + 1; i < m; i++)
            for (int j = k + 1; j < m; j++) {
                i128 v = (i128)a[i][j] * a[k][k] - (i128)a[i][k] * a[k][j];
                a[i][j] = (int64_t)(v / prev);
            }
        prev = a[k][k];
    }
    return sign * a[m - 1][m - 1];
}

/* fraction-free Gauss-Jordan on [M | I] for a positive definite M (no pivoting needed);
   returns det, writes adj */
static int64_t adjugate_pd(int64_t M[MAXN][MAXN], int k, int64_t adj[MAXN][MAXN]) {
    static int64_t a[MAXN][2 * MAXN];
    if (k == 0) return 1;
    for (int i = 0; i < k; i++) {
        for (int j = 0; j < k; j++) { a[i][j] = M[i][j]; a[i][k + j] = (i == j); }
    }
    int64_t prev = 1;
    for (int p = 0; p < k; p++) {
        int64_t piv = a[p][p];
        for (int i = 0; i < k; i++) {
            if (i == p) continue;
            int64_t aip = a[i][p];
            for (int j = 0; j < 2 * k; j++) {
                i128 v = (i128)piv * a[i][j] - (i128)aip * a[p][j];
                a[i][j] = (int64_t)(v / prev);
            }
        }
        prev = piv;
    }
    /* now left block = det * I; rows were scaled consistently: row p holds the pivot row of step p
       (not updated after its own step); bring row p up to date by the formula below */
    int64_t det = a[k - 1][k - 1];
    for (int i = 0; i < k; i++) {
        /* row i was last updated at step k-1 unless i == k-1; its diagonal equals det */
        for (int j = 0; j < k; j++) adj[i][j] = a[i][k + j];
    }
    return det;
}

#include <math.h>
/* determinant (and optionally adjugate) of a symmetric positive semidefinite integer matrix via
   double-precision Gauss-Jordan with partial pivoting; results are rounded to integers and the
   rounding error is checked (abort if any value is not within 1e-6 of an integer).  Exact for the
   magnitudes here (|values| < 2^40). */
static int64_t det_and_adj_double(int64_t M[MAXN][MAXN], int k, int64_t adj[MAXN][MAXN]) {
    if (k == 0) return 1;
    double a[MAXN][2 * MAXN];
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { a[i][j] = (double)M[i][j]; a[i][k + j] = (i == j); }
    double det = 1.0;
    for (int p = 0; p < k; p++) {
        int best = p;
        for (int i = p + 1; i < k; i++) if (fabs(a[i][p]) > fabs(a[best][p])) best = i;
        if (fabs(a[best][p]) < 1e-9) return 0;  /* singular: disconnected induced subgraph */
        if (best != p) { for (int j = 0; j < 2 * k; j++) { double t = a[p][j]; a[p][j] = a[best][j]; a[best][j] = t; } det = -det; }
        double piv = a[p][p]; det *= piv;
        for (int j = 0; j < 2 * k; j++) a[p][j] /= piv;
        for (int i = 0; i < k; i++) if (i != p && a[i][p] != 0.0) {
            double f = a[i][p];
            for (int j = 0; j < 2 * k; j++) a[i][j] -= f * a[p][j];
        }
    }
    double rd = nearbyint(det);
    if (fabs(det - rd) > 1e-6 || rd < 0) { fprintf(stderr, "DET_ROUNDING %g\n", det); exit(5); }
    if (adj) for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        double v = a[i][k + j] * rd, r = nearbyint(v);
        if (fabs(v - r) > 1e-6) { fprintf(stderr, "ADJ_ROUNDING %g\n", v); exit(5); }
        adj[i][j] = (int64_t)r;
    }
    return (int64_t)rd;
}

/* forest polynomial of multigraph A on m vertices; fills gtab[S] for all S and, if want_adj,
   adjt[B] / conn_ok[B] for all B */
static void forest_tables(int A[MAXN][MAXN], int m, int want_adj) {
    int full = (1 << m) - 1;
    static int vs[MAXN];
    static int64_t L[MAXN][MAXN], L2[MAXN][MAXN];
    for (int B = 1; B <= full; B++) {
        int c = 0;
        for (int v = 0; v < m; v++) if (B >> v & 1) vs[c++] = v;
        if (c == 1) { taub[B] = 1; conn_ok[B] = 1; continue; }
        for (int i = 1; i < c; i++)
            for (int j = 1; j < c; j++) {
                if (i == j) {
                    int64_t d = 0;
                    for (int q = 0; q < c; q++) if (q != i) d += A[vs[i]][vs[q]];
                    L[i - 1][j - 1] = d;
                } else L[i - 1][j - 1] = -A[vs[i]][vs[j]];
            }
        taub[B] = det_and_adj_double(L, c - 1, want_adj ? adjt[B] : NULL);
        conn_ok[B] = taub[B] != 0;
    }
    memset(gtab[0], 0, sizeof(gtab[0])); gtab[0][0] = 1;
    for (int S = 1; S <= full; S++) {
        memset(gtab[S], 0, sizeof(int64_t) * MAXN);
        int low = S & -S, rest = S ^ low;
        for (int sub = rest;; sub = (sub - 1) & rest) {
            int B = low | sub;
            int64_t t = taub[B];
            if (t) {
                int e = __builtin_popcount(B) - 1;
                int64_t *h = gtab[S ^ B];
                for (int k = 0; k + e < m; k++) if (h[k]) gtab[S][k + e] += t * h[k];
            }
            if (sub == 0) break;
        }
    }
}

static void contract(int A[MAXN][MAXN], int m, int u, int v, int B[MAXN][MAXN], int *map) {
    int idx = 0;
    for (int x = 0; x < m; x++) if (x != v) map[x] = idx++;
    map[v] = map[u];
    for (int i = 0; i < m - 1; i++) for (int j = 0; j < m - 1; j++) B[i][j] = 0;
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) {
        if (map[x] == map[y]) continue;
        B[map[x]][map[y]] += A[x][y];
    }
}

int main(int argc, char **argv) {
    int verbose = argc > 1 && strcmp(argv[1], "-v") == 0;
    char line[256];
    long long graphs = 0, pairs = 0, p1neg = 0, coefneg = 0, zero = 0;
    long double minratio = 1e30L; char minratio_g[300] = "";
    static int A[MAXN][MAXN], H[MAXN][MAXN], Gf[MAXN][MAXN];
    int map[MAXN], map2[MAXN];
    static int64_t F[MAXN], Fe[64][MAXN], Fef[MAXN];
    int eu[64], ev[64];
    while (fgets(line, sizeof line, stdin)) {
        int len = strlen(line); while (len && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
        if (!len) continue;
        int n = line[0] - 63, m = 0;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) A[i][j] = 0;
        int bit = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
            int byte = line[1 + bit / 6] - 63;
            if (byte >> (5 - bit % 6) & 1) { A[i][j] = A[j][i] = 1; eu[m] = i; ev[m] = j; m++; }
            bit++;
        }
        graphs++;
        forest_tables(A, n, 0);
        for (int k = 0; k < n; k++) F[k] = gtab[(1 << n) - 1][k];
        if (m > MAXE || n > MAXN - 1 + 1) { fprintf(stderr, "TOO_BIG\n"); return 6; }
        int hn = n - 1, full = (1 << hn) - 1;
        static int mapE[MAXE][MAXN];
        for (int e = 0; e < m; e++) {
            contract(A, n, eu[e], ev[e], H, mapE[e]);
            forest_tables(H, hn, 1);
            for (int k = 0; k < n - 1; k++) Fe[e][k] = gtab[full][k];
            memcpy(gE[e], gtab, sizeof(int64_t) * MAXN * (full + 1));
            for (int B = 0; B <= full; B++) {
                connE[e][B] = (char)conn_ok[B];
                if (conn_ok[B]) for (int i = 0; i < hn; i++) for (int j = 0; j < hn; j++) adjE[e][B][i][j] = adjt[B][i][j];
            }
        }
        for (int e = 0; e < m; e++) {
            int *mp = mapE[e];
            for (int f = e + 1; f < m; f++) {
                int u = mp[eu[f]], v = mp[ev[f]];
                for (int k = 0; k < MAXN; k++) Fef[k] = 0;
                int need = (1 << u) | (1 << v);
                for (int B = need; B <= full; B = (B + 1) | need) {
                    if (connE[e][B]) {
                        int r = __builtin_ctz(B);
                        int lu = -1, lv = -1, idx = 0;
                        for (int x = 0; x < hn; x++) if (B >> x & 1) { if (x != r) { if (x == u) lu = idx; if (x == v) lv = idx; idx++; } }
                        int64_t tf = 0;
                        if (lu >= 0) tf += adjE[e][B][lu][lu];
                        if (lv >= 0) tf += adjE[e][B][lv][lv];
                        if (lu >= 0 && lv >= 0) tf -= 2 * adjE[e][B][lu][lv];
                        if (tf) {
                            int e2 = __builtin_popcount(B) - 2;
                            int64_t *h = gE[e][full ^ B];
                            for (int k = 0; k + e2 < MAXN; k++) if (h[k]) Fef[k + e2] += tf * h[k];
                        }
                    }
                    if (B == full) break;
                }
                int deg = 2 * n - 4;
                i128 P[2 * MAXN];
                for (int k = 0; k <= deg; k++) P[k] = 0;
                for (int i = 0; i < n - 1; i++) for (int j = 0; j < n - 1; j++) P[i + j] += (i128)Fe[e][i] * Fe[f][j];
                for (int i = 0; i < n; i++) for (int j = 0; j < n - 2; j++) P[i + j] -= (i128)F[i] * Fef[j];
                for (int j = n - 2; j < MAXN; j++) if (Fef[j]) { fprintf(stderr, "DEGREE_OVERFLOW\n"); return 4; }
                int anyneg = 0, allzero = 1; i128 val1 = 0;
                for (int k = 0; k <= deg; k++) { val1 += P[k]; if (P[k] < 0) anyneg = 1; if (P[k] != 0) allzero = 0; }
                pairs++;
                if (verbose) { printf("PAIR %s %d %d %d %d", line, eu[e], ev[e], eu[f], ev[f]); for (int k = 0; k <= deg; k++) printf(" %lld", (long long)P[k]); printf("\n"); }
                if (allzero) { zero++; continue; }
                i128 ze = 0, zf = 0; for (int k = 0; k < n - 1; k++) { ze += Fe[e][k]; zf += Fe[f][k]; }
                long double rr = (long double)val1 / ((long double)ze * (long double)zf);
                if (rr < minratio) { minratio = rr; snprintf(minratio_g, sizeof minratio_g, "%s e=%d-%d f=%d-%d", line, eu[e], ev[e], eu[f], ev[f]); }
                if (val1 < 0) { p1neg++; printf("P1NEG %s e=%d-%d f=%d-%d\n", line, eu[e], ev[e], eu[f], ev[f]); }
                if (anyneg) {
                    coefneg++;
                    printf("COEFNEG %s e=%d-%d f=%d-%d coeffs", line, eu[e], ev[e], eu[f], ev[f]);
                    for (int k = 0; k <= deg; k++) printf(" %lld", (long long)P[k]);
                    printf("\n");
                }
            }
        }
    }
    printf("SUMMARY parallel_pairs=0 graphs=%lld pairs=%lld zero=%lld p1neg=%lld coefneg=%lld posneg=0 min_ratio=%.12Lg at %s\n",
           graphs, pairs, zero, p1neg, coefneg, minratio, minratio_g);
    return 0;
}
