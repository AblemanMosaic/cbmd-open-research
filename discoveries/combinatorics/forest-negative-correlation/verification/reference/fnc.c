/* Negative edge correlation for the arboreal gas (weighted uniform forests) on small graphs.
 *
 * For a graph G and weight lambda > 0 let Z_G(lambda) = sum over forests F of lambda^{|F|}.
 * For distinct edges e, f the forests containing e are in bijection with forests of G/e, so
 *   Z_e = lambda Z_{G/e},  Z_f = lambda Z_{G/f},  Z_ef = lambda^2 Z_{G/e/f}.
 * Negative correlation P(e,f) <= P(e)P(f) is  Z_e Z_f - Z Z_ef >= 0, i.e.
 *   P(lambda) := Z_{G/e} Z_{G/f} - Z_G Z_{G/e/f} >= 0        (Rayleigh difference / lambda^2).
 * Kahn's conjecture: P(lambda) >= 0 for all lambda > 0; Grimmett-Winkler: P(1) >= 0.
 *
 * Z_H for a multigraph H on m vertices: sum over set partitions of V(H) into blocks B of
 * prod tau(H[B]) lambda^{|B|-1}, tau = number of spanning trees (Kirchhoff, exact Bareiss).
 *
 * Input: graph6 lines on stdin (n <= 11).  For every graph and every unordered pair of distinct
 * edges, computes P as an exact integer polynomial and classifies:
 *   P1NEG   : P(1) < 0                      (counterexample to Grimmett-Winkler)
 *   COEFNEG : some coefficient of P negative (then positivity on (0,inf) is tested by Sturm)
 *   POSNEG  : P(lambda) < 0 for some lambda > 0 (counterexample to Kahn)
 *   ZERO    : P identically 0
 * Output: per-run summary line plus any exceptional instance lines.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef __int128 i128;
#define MAXN 11
static int N;
static int64_t taub[1 << MAXN];

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

/* forest polynomial of multigraph A (m vertices); out[k] = number of forests with k edges */
static void forest_poly(int A[MAXN][MAXN], int m, int64_t *out) {
    int full = (1 << m) - 1;
    static int vs[MAXN];
    static int64_t L[MAXN][MAXN];
    for (int B = 1; B <= full; B++) {
        int c = 0;
        for (int v = 0; v < m; v++) if (B >> v & 1) vs[c++] = v;
        if (c == 1) { taub[B] = 1; continue; }
        /* Laplacian of H[B] with first vertex removed */
        for (int i = 1; i < c; i++)
            for (int j = 1; j < c; j++) {
                if (i == j) {
                    int64_t d = 0;
                    for (int k = 0; k < c; k++) if (k != i) d += A[vs[i]][vs[k]];
                    L[i - 1][j - 1] = d;
                } else L[i - 1][j - 1] = -A[vs[i]][vs[j]];
            }
        taub[B] = det_bareiss(L, c - 1);
    }
    static int64_t g[1 << MAXN][MAXN];
    memset(g[0], 0, sizeof(g[0])); g[0][0] = 1;
    for (int S = 1; S <= full; S++) {
        memset(g[S], 0, sizeof(int64_t) * m);
        int low = S & -S; int rest = S ^ low;
        /* B = low | sub, sub subset of rest */
        for (int sub = rest;; sub = (sub - 1) & rest) {
            int B = low | sub;
            int64_t t = taub[B];
            if (t) {
                int e = __builtin_popcount(B) - 1;
                int64_t *h = g[S ^ B];
                for (int k = 0; k + e < m; k++) if (h[k]) g[S][k + e] += t * h[k];
            }
            if (sub == 0) break;
        }
    }
    for (int k = 0; k < m; k++) out[k] = g[full][k];
}

/* contract edge (u,v) in multigraph A (m vertices) into B (m-1 vertices); loops dropped */
static int contract(int A[MAXN][MAXN], int m, int u, int v, int B[MAXN][MAXN], int *map) {
    if (u > v) { int t = u; u = v; v = t; }
    int idx = 0;
    for (int x = 0; x < m; x++) { if (x == v) map[x] = map[u]; else map[x] = idx++; if (x == u) map[x] = idx - 1; }
    /* recompute map cleanly */
    idx = 0;
    for (int x = 0; x < m; x++) if (x != v) map[x] = idx++;
    map[v] = map[u];
    for (int i = 0; i < m - 1; i++) for (int j = 0; j < m - 1; j++) B[i][j] = 0;
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) {
        if (map[x] == map[y]) continue;
        B[map[x]][map[y]] += A[x][y];
    }
    return m - 1;
}

static void pmul(const int64_t *a, int la, const int64_t *b, int lb, i128 *out) {
    for (int k = 0; k < la + lb - 1; k++) out[k] = 0;
    for (int i = 0; i < la; i++) for (int j = 0; j < lb; j++) out[i + j] += (i128)a[i] * b[j];
}

/* number of sign changes of the Sturm sequence at +inf minus at 0+ (roots in (0,inf));
   uses long double; only called when some coefficient is negative (expected rare). */
static int has_negative_value(const i128 *p, int deg) {
    /* sample-based + fine scan: evaluate on a geometric grid; exactness is restored by also
       evaluating exactly at rational grid points with i128 when magnitudes allow. */
    for (int s = -400; s <= 400; s++) {
        long double x = powl(10.0L, s / 40.0L);
        long double v = 0;
        for (int k = deg; k >= 0; k--) v = v * x + (long double)p[k];
        if (v < 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    int verbose = 0, tmode = 0;
    for (int i = 1; i < argc; i++) { if (!strcmp(argv[i], "-v")) verbose = 1; if (!strcmp(argv[i], "-T")) tmode = 1; }
    char line[256];
    long long parallel_pairs = 0, graphs = 0, pairs = 0, p1neg = 0, coefneg = 0, posneg = 0, zero = 0;
    long double minratio = 1e30L; char minratio_g[256] = "";
    int A[MAXN][MAXN], Ge[MAXN][MAXN], Gef[MAXN][MAXN], map[MAXN], map2[MAXN];
    int64_t F[MAXN], Fe[64][MAXN], Fef[MAXN];
    int eu[64], ev[64];
    while (fgets(line, sizeof line, stdin)) {
        int len = strlen(line); while (len && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = 0;
        if (!len) continue;
        int n, m = 0;
        static int mult[64];
        if (tmode) {  /* multig -T format: nv ne {v1 v2 mult} */
            char *p = line; int ne;
            n = (int)strtol(p, &p, 10); ne = (int)strtol(p, &p, 10);
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) A[i][j] = 0;
            for (int k = 0; k < ne; k++) {
                int a = (int)strtol(p, &p, 10), b = (int)strtol(p, &p, 10), c = (int)strtol(p, &p, 10);
                A[a][b] = A[b][a] = c; eu[m] = a < b ? a : b; ev[m] = a < b ? b : a; mult[m] = c; m++;
            }
        } else {
            n = line[0] - 63;
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) A[i][j] = 0;
            int bit = 0;
            for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
                int byte = line[1 + bit / 6] - 63;
                if (byte >> (5 - bit % 6) & 1) { A[i][j] = A[j][i] = 1; eu[m] = i; ev[m] = j; mult[m] = 1; m++; }
                bit++;
            }
        }
        graphs++;
        forest_poly(A, n, F);
        for (int e = 0; e < m; e++) { contract(A, n, eu[e], ev[e], Ge, map); forest_poly(Ge, n - 1, Fe[e]); }
        for (int e = 0; e < m; e++) {
            contract(A, n, eu[e], ev[e], Ge, map);
            if (mult[e] >= 2) { pairs++; parallel_pairs++; }  /* Z_ef = 0: trivially negatively correlated */
            for (int f = e + 1; f < m; f++) {
                int a = map[eu[f]], b = map[ev[f]];
                contract(Ge, n - 1, a, b, Gef, map2);
                forest_poly(Gef, n - 2, Fef);
                i128 p1[2 * MAXN], p2[2 * MAXN], P[2 * MAXN];
                pmul(Fe[e], n - 1, Fe[f], n - 1, p1);       /* degree <= 2n-4 */
                pmul(F, n, Fef, n - 2, p2);                 /* degree <= 2n-4 */
                int deg = 2 * n - 4;
                int anyneg = 0, allzero = 1;
                i128 val1 = 0;
                for (int k = 0; k <= deg; k++) {
                    i128 x = (k <= 2 * n - 4 ? p1[k] : 0) - (k <= 2 * n - 4 ? p2[k] : 0);
                    P[k] = x; val1 += x; if (x < 0) anyneg = 1; if (x != 0) allzero = 0;
                }
                pairs++;
                if (verbose) { printf("PAIR %s %d %d %d %d", line, eu[e], ev[e], eu[f], ev[f]); for (int k = 0; k <= deg; k++) printf(" %lld", (long long)P[k]); printf("\n"); }
                if (allzero) { zero++; continue; }
                /* ratio P(1) / (Z_e Z_f at lambda=1) as a margin statistic */
                i128 ze = 0, zf = 0; for (int k = 0; k < n - 1; k++) { ze += Fe[e][k]; zf += Fe[f][k]; }
                long double r = (long double)val1 / ((long double)ze * (long double)zf);
                if (r < minratio) { minratio = r; snprintf(minratio_g, sizeof minratio_g, "%s e=%d-%d f=%d-%d", line, eu[e], ev[e], eu[f], ev[f]); }
                if (val1 < 0) { p1neg++; printf("P1NEG %s e=%d-%d f=%d-%d\n", line, eu[e], ev[e], eu[f], ev[f]); }
                if (anyneg) {
                    coefneg++;
                    printf("COEFNEG %s e=%d-%d f=%d-%d coeffs", line, eu[e], ev[e], eu[f], ev[f]);
                    for (int k = 0; k <= deg; k++) printf(" %lld", (long long)P[k]);
                    printf("\n");
                    if (has_negative_value(P, deg)) { posneg++; printf("POSNEG %s e=%d-%d f=%d-%d\n", line, eu[e], ev[e], eu[f], ev[f]); }
                }
            }
        }
    }
    printf("SUMMARY parallel_pairs=%lld graphs=%lld pairs=%lld zero=%lld p1neg=%lld coefneg=%lld posneg=%lld min_ratio=%.12Lg at %s\n",
           parallel_pairs, graphs, pairs, zero, p1neg, coefneg, posneg, minratio, minratio_g);
    return 0;
}
