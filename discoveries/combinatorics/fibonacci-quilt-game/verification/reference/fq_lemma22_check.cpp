// Lemma 2.2 check (written by the independent reviewer): for every position where rule 2(a) is the only move (other indices <= KMAX), the maximal number of 2(a) uses in any continuation.
// Lemma 2.2 probe: enumerate every position P containing q1,q5 in which rule 2(a) is the only move
// (P = {1,5} + multiset S, S indices <= KMAX), and compute the max number of 2(a) uses on any game from P.
// usage: lemma22 KMAX variant(0: 3f={q2q8,q5q7}; 1: 3f={q2q8}; 2: 3f={q2q8,q3q7 printed, non value-preserving})
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
#include <unordered_map>
using namespace std;
const int S = 64;
struct Rule { vector<int> rem, add; };
vector<Rule> rules; int variant;
unordered_map<string, int> memo;
bool canr(const string &k, const vector<int> &rem) {
  int need[S] = {0}; for (int i : rem) need[i]++;
  for (int i : rem) if ((unsigned char)k[i] < need[i]) return false; return true;
}
string app(string k, const vector<int> &r, const vector<int> &a) { for (int i : r) k[i]--; for (int i : a) { if (i >= S) { fprintf(stderr, "overflow\n"); exit(2);} k[i]++; } return k; }
bool anyOther(const string &k) { for (auto &r : rules) if (canr(k, r.rem)) return true; return false; }
int solve(const string &k) {
  auto it = memo.find(k); if (it != memo.end()) return it->second;
  int best = 0; bool any = false;
  for (auto &r : rules) if (canr(k, r.rem)) { any = true; int v = solve(app(k, r.rem, r.add)); if (v > best) best = v; }
  if (!any && k[1] && k[5]) best = 1 + solve(app(k, {1, 5}, {2, 4}));
  memo[k] = best; return best;
}
int main(int argc, char **argv) {
  int KMAX = atoi(argv[1]); variant = atoi(argv[2]);
  int top = S - 6;
  rules.push_back({{1,2},{3}});
  for (int i=2;i<top;i++) rules.push_back({{i,i+1},{i+3}});
  for (int i=2;i<top-1;i++) rules.push_back({{i,i+4},{i+5}});
  rules.push_back({{1,1},{2}}); rules.push_back({{2,2},{4}}); rules.push_back({{3,3},{2,4}});
  rules.push_back({{4,4},{1,6}}); rules.push_back({{4,4},{3,5}}); rules.push_back({{5,5},{1,7}});
  rules.push_back({{6,6},{2,8}});
  if (variant == 0) rules.push_back({{6,6},{5,7}});
  if (variant == 2) rules.push_back({{6,6},{3,7}});
  for (int i=7;i<top;i++) rules.push_back({{i,i},{i-5,i+2}});
  rules.push_back({{1,4},{5}}); rules.push_back({{2,5},{6}}); rules.push_back({{3,6},{1,7}});
  rules.push_back({{4,7},{1,8}}); rules.push_back({{5,8},{1,9}}); rules.push_back({{6,9},{2,10}});
  for (int i=7;i<top-1;i++) rules.push_back({{i,i+3},{i-5,i+4}});
  rules.push_back({{1,3},{4}});
  // any position with no other move has no duplicates, so S is a set; enumerate subsets of {2..KMAX}
  // by DFS with pruning on pairwise forbidden differences (0,1,3,4) and {1,3}.
  long cnt = 0; int worst = 0;
  vector<int> cur;
  // recursive lambda via std::function-free approach
  struct D { static void go(int from, int KMAX, vector<int> &cur, long &cnt, int &worst) {
      // evaluate current
      string k(S, 0); k[1]++; k[5]++; for (int i : cur) k[i]++;
      if (!anyOther(k)) { cnt++; int v = solve(k); if (v > worst) worst = v; if (v > 1) { printf("VIOLATION:"); for (int i:cur) printf(" %d", i); printf(" -> %d\n", v);} }
      for (int j = from; j <= KMAX; j++) {
        bool ok = true; int all[3] = {1, 5};
        for (int a : {1, 5}) { int d = abs(j - a); if (d == 0 || d == 1 || d == 3 || d == 4) ok = false; }
        if (j == 3) ok = false;
        for (int i : cur) { int d = j - i; if (d == 0 || d == 1 || d == 3 || d == 4) ok = false; }
        if (!ok) continue;
        cur.push_back(j); go(j + 1, KMAX, cur, cnt, worst); cur.pop_back();
      }
  }};
  D::go(2, KMAX, cur, cnt, worst);
  printf("KMAX %d variant %d: 2a-positions %ld, max #2a from them %d, states %zu\n", KMAX, variant, cnt, worst, memo.size());
}
