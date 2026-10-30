/* Negative edge correlation for weighted connected spanning subgraphs (random-cluster q -> 0).
 *
 * For a graph G and lambda > 0, C_G(lambda) = sum over connected spanning subgraphs A of
 * lambda^{|A|}.  Connected spanning subgraphs containing e correspond to those of G/e (loops
 * kept: a loop may be included freely), so C_e = lambda C_{G/e}, C_ef = lambda^2 C_{G/e/f} and
 * negative correlation is
 *   P(lambda) := C_{G/e} C_{G/f} - C_G C_{G/e/f} >= 0.
 * Grimmett-Winkler conjecture (connected-subgraph analogue): P(1) >= 0; the q -> 0 limit of
 * their random-cluster conjecture asks P(lambda) >= 0 for all lambda > 0.
 *
 * C_H by subset recursion: conn(S) = all(S) - sum_{low(S) in B, B proper subset of S}
 * conn(B) all(S \ B), all(S) = (1 + lambda)^{e(S)}, e(S) counting loops inside S.
 * Input graph6 on stdin; output SUMMARY and exceptional lines as in fnc.c.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef __int128 i128;
#define MAXN 11
#define MAXE 64
static int64_t binom[MAXE + 1][MAXE + 1];

static int conn_poly(int A[MAXN][MAXN], int m, int64_t *out) {
    int full = (1 << m) - 1;
    static int64_t allp[1 << MAXN][MAXE + 1], conn[1 << MAXN][MAXE + 1];
    static int ec[1 << MAXN];
    ec[0] = 0;
    for (int S = 1; S <= full; S++) {
        int c = 0;
        for (int u = 0; u < m; u++) if (S >> u & 1) {
            c += A[u][u];
            for (int v = u + 1; v < m; v++) if (S >> v & 1) c += A[u][v];
        }
        ec[S] = c;
        for (int k = 0; k <= c; k++) allp[S][k] = binom[c][k];
    }
    for (int S = 1; S <= full; S++) {
        int low = S & -S, rest = S ^ low;
        for (int k = 0; k <= ec[S]; k++) conn[S][k] = allp[S][k];
        for (int sub = rest;; sub = (sub - 1) & rest) {
            if (sub != rest) {
                int B = low | sub, R = S ^ B;
                for (int i = 0; i <= ec[B]; i++) if (conn[B][i])
                    for (int j = 0; j <= ec[R]; j++) conn[S][i + j] -= conn[B][i] * allp[R][j];
            }
            if (sub == 0) break;
        }
    }
    for (int k = 0; k <= ec[full]; k++) out[k] = conn[full][k];
    return ec[full];  /* degree bound */
}

/* contract one copy of edge (u,v) (u != v, A[u][v] >= 1); other parallel copies become loops */
static void contract(int A[MAXN][MAXN], int m, int u, int v, int B[MAXN][MAXN], int *map) {
    int idx = 0;
    for (int x = 0; x < m; x++) if (x != v) map[x] = idx++;
    map[v] = map[u];
    for (int i = 0; i < m - 1; i++) for (int j = 0; j < m - 1; j++) B[i][j] = 0;
    for (int x = 0; x < m; x++) {
        B[map[x]][map[x]] += A[x][x];
        for (int y = x + 1; y < m; y++) {
            int c = A[x][y];
            if (!c) continue;
            if ((x == u && y == v) || (x == v && y == u)) c -= 1;  /* the contracted copy */
            if (!c) continue;
            if (map[x] == map[y]) B[map[x]][map[x]] += c;
            else { B[map[x]][map[y]] += c; B[map[y]][map[x]] += c; }
        }
    }
}

int main(int argc, char **argv) {
    int verbose = 0, tmode = 0;
    for (int i = 1; i < argc; i++) { if (!strcmp(argv[i], "-v")) verbose = 1; if (!strcmp(argv[i], "-T")) tmode = 1; }
    for (int i = 0; i <= MAXE; i++) { binom[i][0] = 1; for (int j = 1; j <= i; j++) binom[i][j] = binom[i - 1][j - 1] + (j <= i - 1 ? binom[i - 1][j] : 0); }
    char line[256];
    long long graphs = 0, pairs = 0, p1neg = 0, coefneg = 0, posneg = 0, zero = 0;
    long double minratio = 1e30L; char minratio_g[300] = "";
    static int A[MAXN][MAXN], Ge[MAXN][MAXN], Gef[MAXN][MAXN];
    int map[MAXN], map2[MAXN];
    static int64_t C[MAXE + 1], Ce[64][MAXE + 1], Cef[MAXE + 1];
    int dC, dCe[64], dCef;
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
        memset(C, 0, sizeof C); dC = conn_poly(A, n, C);
        for (int e = 0; e < m; e++) { contract(A, n, eu[e], ev[e], Ge, map); memset(Ce[e], 0, sizeof Ce[e]); dCe[e] = conn_poly(Ge, n - 1, Ce[e]); }
        for (int e = 0; e < m; e++) {
            contract(A, n, eu[e], ev[e], Ge, map);
            for (int f = e; f < m; f++) {
                if (f == e) {
                    if (mult[e] < 2) continue;
                    /* two parallel copies of the same edge: in G/e the second copy is a loop that
                       must be included; C_ef = lambda^2 C(G/e minus that loop) */
                    for (int i = 0; i < n - 1; i++) for (int j = 0; j < n - 1; j++) Gef[i][j] = Ge[i][j];
                    Gef[map[eu[e]]][map[eu[e]]] -= 1;
                    memset(Cef, 0, sizeof Cef); dCef = conn_poly(Gef, n - 1, Cef);
                } else {
                    contract(Ge, n - 1, map[eu[f]], map[ev[f]], Gef, map2);
                    memset(Cef, 0, sizeof Cef); dCef = conn_poly(Gef, n - 2, Cef);
                }
                int deg = dCe[e] + dCe[f];
                if (dC + dCef > deg) deg = dC + dCef;
                static i128 P[2 * MAXE + 2];
                for (int k = 0; k <= deg; k++) P[k] = 0;
                for (int i = 0; i <= dCe[e]; i++) for (int j = 0; j <= dCe[f]; j++) P[i + j] += (i128)Ce[e][i] * Ce[f][j];
                for (int i = 0; i <= dC; i++) for (int j = 0; j <= dCef; j++) P[i + j] -= (i128)C[i] * Cef[j];
                int anyneg = 0, allzero = 1; i128 val1 = 0;
                for (int k = 0; k <= deg; k++) { val1 += P[k]; if (P[k] < 0) anyneg = 1; if (P[k] != 0) allzero = 0; }
                pairs++;
                if (verbose) { printf("PAIR %s %d %d %d %d", line, eu[e], ev[e], eu[f], ev[f]); for (int k = 0; k <= deg; k++) printf(" %lld", (long long)P[k]); printf("\n"); }
                if (allzero) { zero++; continue; }
                i128 ze = 0, zf = 0; for (int k = 0; k <= dCe[e]; k++) ze += Ce[e][k]; for (int k = 0; k <= dCe[f]; k++) zf += Ce[f][k];
                long double r = (long double)val1 / ((long double)ze * (long double)zf);
                if (r < minratio) { minratio = r; snprintf(minratio_g, sizeof minratio_g, "%s e=%d-%d f=%d-%d", line, eu[e], ev[e], eu[f], ev[f]); }
                if (val1 < 0) { p1neg++; printf("P1NEG %s e=%d-%d f=%d-%d\n", line, eu[e], ev[e], eu[f], ev[f]); }
                if (anyneg) {
                    coefneg++;
                    printf("COEFNEG %s e=%d-%d f=%d-%d", line, eu[e], ev[e], eu[f], ev[f]);
                    for (int k = 0; k <= deg; k++) printf(" %lld", (long long)P[k]);
                    printf("\n");
                    int neg = 0;
                    for (int s = -400; s <= 400 && !neg; s++) {
                        long double x = powl(10.0L, s / 40.0L), v = 0;
                        for (int k = deg; k >= 0; k--) v = v * x + (long double)P[k];
                        if (v < 0) neg = 1;
                    }
                    if (neg) { posneg++; printf("POSNEG_NUMERIC %s e=%d-%d f=%d-%d\n", line, eu[e], ev[e], eu[f], ev[f]); }
                }
            }
        }
    }
    printf("SUMMARY graphs=%lld pairs=%lld zero=%lld p1neg=%lld coefneg=%lld posneg_numeric=%lld min_ratio=%.12Lg at %s\n",
           graphs, pairs, zero, p1neg, coefneg, posneg, minratio, minratio_g);
    return 0;
}
