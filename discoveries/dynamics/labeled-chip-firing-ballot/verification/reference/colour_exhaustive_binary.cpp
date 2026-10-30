// Exhaustive two-colour check of the ballot property on the binary tree, all thresholds t (used for l = 5, t = 1..12; killed by memory beyond).
#include <bits/stdc++.h>
using namespace std;
// Two-colour projection of labeled chip-firing on the undirected binary tree (root self-loop).
// Chips <= t red. Firing at v takes 3 chips with r reds: left gets red iff r>=1, right red iff r==3, up (root: stays) red iff r>=2.
// Exhaustive over all firing choices (vertex, r); check ballot (#red left subtree >= #red right subtree at every vertex) at every stable state.
int L,N,NV; // NV = number of vertex slots used
typedef vector<unsigned char> St; // [2*v]=red,[2*v+1]=blue for v in 1..NV-1
struct H{ size_t operator()(const St&s)const{ size_t h=1469598103934665603ULL; for(auto x:s){h^=x;h*=1099511628211ULL;} return h; } };
unordered_set<St,H> seen; long stableCount=0, bad=0; vector<int> badT;
int curT;
bool ballot(const St& s){
  // subtree red counts
  vector<int> sub(NV+2,0);
  for(int v=NV-1; v>=1; v--){ sub[v]=s[2*v]+(2*v<NV?sub[2*v]:0)+(2*v+1<NV?sub[2*v+1]:0); }
  for(int v=1; 2*v+1<NV; v++) if(sub[2*v]<sub[2*v+1]) return false;
  return true;
}
void dfs(const St& s){
  if(!seen.insert(s).second) return;
  bool any=false;
  for(int v=1; v<NV; v++){
    int r=s[2*v], b=s[2*v+1]; if(r+b<3) continue;
    if(2*v+1>=NV){ fprintf(stderr,"tree too small\n"); exit(2); }
    any=true;
    for(int k=max(0,3-b); k<=min(3,r); k++){
      St t=s; t[2*v]-=k; t[2*v+1]-=3-k;
      int L_red=k>=1, R_red=k==3, U_red=k>=2;
      t[2*(2*v)+ (L_red?0:1)]++;
      t[2*(2*v+1)+ (R_red?0:1)]++;
      int p=(v==1?1:v/2); t[2*p+(U_red?0:1)]++;
      dfs(t);
    }
  }
  if(!any){ stableCount++; if(!ballot(s)) bad++; }
}
int main(int argc,char**argv){
  L=atoi(argv[1]); N=(1<<L)-1; NV=1<<(L+1); // allow one extra level as guard
  for(int t=1;t<N;t++){
    seen.clear(); stableCount=0; bad=0; curT=t;
    St s(2*NV,0); s[2*1]=t; s[2*1+1]=N-t;
    dfs(s);
    printf("t=%d states=%zu stable=%ld ballot_fail=%ld\n",t,seen.size(),stableCount,bad); fflush(stdout);
  }
}
