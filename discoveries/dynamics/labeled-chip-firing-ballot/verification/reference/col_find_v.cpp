#include <bits/stdc++.h>
using namespace std;
// Find a two-colour run violating the ballot property for given L, t; print the move sequence (vertex, reds) .
int L,N,NV,T;
typedef vector<unsigned char> St;
struct H{ size_t operator()(const St&s)const{ size_t h=1469598103934665603ULL; for(auto x:s){h^=x;h*=1099511628211ULL;} return h; } };
unordered_map<St,pair<St,pair<int,int>>,H> par; // state -> (prev, (v,k))
bool ballot(const St& s){
  vector<int> sub(NV+2,0);
  for(int v=NV-1; v>=1; v--) sub[v]=s[2*v]+(2*v<NV?sub[2*v]:0)+(2*v+1<NV?sub[2*v+1]:0);
  int v0=atoi(getenv("V0")); if(sub[2*v0]<sub[2*v0+1]) return false;
  return true;
}
int main(int argc,char**argv){
  L=atoi(argv[1]); T=atoi(argv[2]); N=(1<<L)-1; NV=1<<(L+1);
  St s0(2*NV,0); s0[2]=T; s0[3]=N-T;
  par[s0]={St(),{0,0}};
  vector<St> stack={s0}; St found;
  while(!stack.empty()){
    St s=stack.back(); stack.pop_back(); bool any=false;
    for(int v=1; v<NV; v++){
      int r=s[2*v], b=s[2*v+1]; if(r+b<3) continue; any=true;
      for(int k=max(0,3-b); k<=min(3,r); k++){
        St t=s; t[2*v]-=k; t[2*v+1]-=3-k;
        t[2*(2*v)+((k>=1)?0:1)]++; t[2*(2*v+1)+((k==3)?0:1)]++; int p=(v==1?1:v/2); t[2*p+((k>=2)?0:1)]++;
        if(par.find(t)==par.end()){ par[t]={s,{v,k}}; stack.push_back(t); }
      }
    }
    if(!any && !ballot(s)){ found=s; break; }
  }
  if(found.empty()){ printf("none\n"); return 0; }
  vector<pair<int,int>> mv; St cur=found;
  while(true){ auto& pr=par[cur]; if(pr.first.empty()) break; mv.push_back(pr.second); cur=pr.first; }
  reverse(mv.begin(),mv.end());
  printf("%zu\n",mv.size()); for(auto&m:mv) printf("%d %d\n",m.first,m.second);
}
