// Two-colour exhaustive test of HMP Conjecture 21 instances on Z<S> (loops at S).
// Usage: zsr r n s1 s2 ...  (graph r(Z<S>): every edge and loop replaced by r parallel copies)   (S given as integers; may be empty)
// Output: one line "t=<t> states=<k> sorted=<0|1>" per t in 1..n-1, then "RESULT ok|FAIL".
// A colour state assigns (red,blue) counts to each site of a window of W sites; red = labels <= t.
// Firing a site with d = 2 + [site in S] chips, choosing r red: lowest goes left (red iff r>=1),
// highest goes right (red iff r==d), middle stays if loop (red iff r>=2).
// Sound for "sorts": every labeled run projects to a colour run for every t, and a labeled
// stable state is sorted iff all its threshold projections have no blue strictly left of a red.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <unordered_set>
#include <set>
using namespace std;
const int W = 48, O = W / 2;
int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage\n"); return 2; }
    int r = atoi(argv[1]); int n = atoi(argv[2]);
    bool loop[W] = {false};
    for (int i = 3; i < argc; i++) { int s = atoi(argv[i]); loop[O + s] = true; }
    bool all_ok = true;
    bool early = getenv("ZS_EARLY") != nullptr;  // stop at the first unsorted stable state (for FAIL-expected scans)
    for (int t = 1; t < n; t++) {
        string start(2 * W, '\0');
        start[2 * O] = (char)t; start[2 * O + 1] = (char)(n - t);
        unordered_set<string> seen; vector<string> stack;
        seen.insert(start); stack.push_back(start);
        bool sorted_all = true;
        while (!stack.empty()) {
            string s = stack.back(); stack.pop_back();
            bool any = false;
            for (int v = 0; v < W; v++) {
                int R = s[2 * v], B = s[2 * v + 1], m = loop[v] ? r : 0, d = 2 * r + m;
                if (R + B < d) continue;
                if (v == 0 || v == W - 1) { fprintf(stderr, "WINDOW_EXCEEDED\n"); return 3; }
                any = true;
                int klo = d - B > 0 ? d - B : 0, khi = R < d ? R : d;
                for (int k = klo; k <= khi; k++) {
                    string u = s;
                    u[2 * v] -= k; u[2 * v + 1] -= (d - k);
                    int kl = k < r ? k : r;                       // reds among the r smallest -> left
                    int km = k - r > 0 ? (k - r < m ? k - r : m) : 0; // reds among the m middle -> stay
                    int kr = k - r - m > 0 ? k - r - m : 0;        // reds among the r largest -> right
                    u[2 * (v - 1)] += kl; u[2 * (v - 1) + 1] += r - kl;
                    u[2 * v] += km;       u[2 * v + 1] += m - km;
                    u[2 * (v + 1)] += kr; u[2 * (v + 1) + 1] += r - kr;
                    if (seen.insert(u).second) stack.push_back(u);
                }
            }
            if (!any) {
                bool blue = false;
                for (int v = 0; v < W; v++) {
                    if (s[2 * v] && blue) { sorted_all = false; if (early) { printf("t=%d early_unsorted\nRESULT FAIL\n", t); return 0; } break; }
                    if (s[2 * v + 1]) blue = true;
                }
            }
        }
        printf("t=%d states=%zu sorted=%d\n", t, seen.size(), sorted_all ? 1 : 0);
        if (!sorted_all) all_ok = false;
    }
    printf("RESULT %s\n", all_ok ? "ok" : "FAIL");
    return 0;
}
