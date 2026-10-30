// Two-colour exhaustive test of HMP Conjecture 21 instances on Z<S> (loops at S).
// Usage: zs n s1 s2 ...   (S given as integers; may be empty)
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
    int n = atoi(argv[1]);
    bool loop[W] = {false};
    for (int i = 2; i < argc; i++) { int s = atoi(argv[i]); loop[O + s] = true; }
    bool all_ok = true;
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
                int R = s[2 * v], B = s[2 * v + 1], m = loop[v] ? 1 : 0, d = 2 + m;
                if (R + B < d) continue;
                if (v == 0 || v == W - 1) { fprintf(stderr, "WINDOW_EXCEEDED\n"); return 3; }
                any = true;
                int rlo = d - B > 0 ? d - B : 0, rhi = R < d ? R : d;
                for (int r = rlo; r <= rhi; r++) {
                    string u = s;
                    u[2 * v] -= r; u[2 * v + 1] -= (d - r);
                    u[2 * (v - 1) + (r >= 1 ? 0 : 1)]++;
                    u[2 * (v + 1) + (r == d ? 0 : 1)]++;
                    if (m) u[2 * v + (r >= 2 ? 0 : 1)]++;
                    if (seen.insert(u).second) stack.push_back(u);
                }
            }
            if (!any) {
                bool blue = false;
                for (int v = 0; v < W; v++) {
                    if (s[2 * v] && blue) { sorted_all = false; break; }
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
