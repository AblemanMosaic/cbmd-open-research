// Per-threshold census of stable two-colour states (hash-only visited set, 128-bit) and the forced order relations chip(u) < chip(w), binary tree, heap indexing (root 1).
#include <bits/stdc++.h>
using namespace std;
// For each threshold t, collect all reachable stable two-colour states of labeled chip-firing on the binary tree
// (hash-only visited set), and derive: forced order relations chip(u) < chip(w) in every stable configuration,
// and the per-threshold count of ballot-violating stable colour states.
int L,N,NV;
typedef vector<unsigned char> St;
int main(int argc,char**argv){
  L=atoi(argv[1]); N=(1<<L)-1; NV=1<<(L+1);
  int tlo=argc>2?atoi(argv[2]):1, thi=argc>3?atoi(argv[3]):N-1;
  // canRB[u][w] = exists t and stable state with u blue and w red  (then "chip(u) < chip(w)" is NOT forced)
  vector<vector<char>> canBR(N+1, vector<char>(N+1,0));
  struct PH{ size_t operator()(const pair<uint64_t,uint64_t>&p)const{ return p.first^(p.second*0x9e3779b97f4a7c15ULL);} };
  auto hsh=[&](const St&t){ uint64_t a=1469598103934665603ULL,b=0x84222325cbf29ce4ULL; for(unsigned char c:t){ a^=c; a*=1099511628211ULL; b+=c+1; b*=0x100000001b3ULL; b^=b>>29; } return make_pair(a,b); };
  for(int t=tlo;t<=thi;t++){
    unordered_set<pair<uint64_t,uint64_t>,PH> seen; vector<St> stk; long nstable=0, bad=0;
    St s(2*NV,0); s[2]=t; s[3]=N-t; seen.insert(hsh(s)); stk.push_back(s);
    while(!stk.empty()){
      St c=stk.back(); stk.pop_back(); bool any=false;
      for(int v=1;v<NV;v++){ int r=c[2*v],b=c[2*v+1]; if(r+b<3) continue; any=true;
        if(2*v+1>=NV){ fprintf(stderr,"overflow\n"); return 2; }
        for(int k=max(0,3-b);k<=min(3,r);k++){ St d=c; d[2*v]-=k; d[2*v+1]-=3-k;
          d[2*(2*v)+(k>=1?0:1)]++; d[2*(2*v+1)+(k==3?0:1)]++; int p=v==1?1:v/2; d[2*p+(k>=2?0:1)]++;
          if(seen.insert(hsh(d)).second) stk.push_back(d); } }
      if(!any){ nstable++;
        for(int u=1;u<=N;u++) for(int w=1;w<=N;w++) if(c[2*u+1] && c[2*w]) canBR[u][w]=1;
        vector<int> sub(NV,0); for(int v=NV-1;v>=1;v--) sub[v]=c[2*v]+(2*v<NV?sub[2*v]:0)+(2*v+1<NV?sub[2*v+1]:0);
        bool ok=true; for(int v=1;2*v+1<NV;v++) if(sub[2*v]<sub[2*v+1]) ok=false; if(!ok) bad++; }
    }
    printf("t=%d states=%zu stable=%ld ballot_violating=%ld\n",t,seen.size(),nstable,bad); fflush(stdout);
  }
  printf("FORCED (u,w) meaning chip(u) < chip(w) always:\n");
  long cntf=0;
  for(int u=1;u<=N;u++) for(int w=1;w<=N;w++) if(u!=w && !canBR[u][w]){ printf("%d<%d ",u,w); cntf++; }
  printf("\ncount %ld\n",cntf);
}
