// Exhaustive labeled chip-firing on Z from n chips at 0: number of reachable states, stable outcomes (permutations) and their maximal inversion number. DUMP=1 lists outcomes.
#include <bits/stdc++.h>
using namespace std;
// Labeled chip-firing on Z: n chips at 0; a site with >=2 chips fires two chosen chips: smaller to left, larger to right.
// Exhaustive: set of final permutations (read left to right). Report max inversions and the set size.
int n; int OFF;
typedef vector<signed char> St; // position of chip i (offset)
struct H{ size_t operator()(const St&s)const{ size_t h=1469598103934665603ULL; for(auto x:s){h^=(unsigned char)x;h*=1099511628211ULL;} return h; } };
unordered_set<St,H> seen; set<vector<int>> finals;
void dfs(const St&s){
  if(!seen.insert(s).second) return;
  // group chips by position
  map<int,vector<int>> at; for(int i=0;i<n;i++) at[s[i]].push_back(i);
  bool any=false;
  for(auto&[p,v]:at) if(v.size()>=2){ any=true;
    for(size_t a=0;a<v.size();a++) for(size_t b=a+1;b<v.size();b++){ St t=s; t[v[a]]=p-1; t[v[b]]=p+1; dfs(t); } }
  if(!any){ vector<pair<int,int>> pc; for(int i=0;i<n;i++) pc.push_back({s[i],i}); sort(pc.begin(),pc.end()); vector<int> perm; for(auto&x:pc) perm.push_back(x.second+1); finals.insert(perm); }
}
int main(int argc,char**argv){ n=atoi(argv[1]); St s(n,0); dfs(s);
  int mx=0; vector<int> arg; for(auto&p:finals){ int inv=0; for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(p[i]>p[j]) inv++; if(inv>mx){mx=inv;arg=p;} }
  printf("n=%d states=%zu finals=%zu maxinv=%d example:",n,seen.size(),finals.size(),mx); for(int x:arg) printf(" %d",x); printf("\n"); if(getenv("DUMP")) for(auto&p:finals){ for(int x:p) printf("%d ",x); printf("\n"); } }
