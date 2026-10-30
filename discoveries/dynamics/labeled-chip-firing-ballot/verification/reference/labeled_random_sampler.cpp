// Uniformly random labeled chip-firing on the binary tree (random unstable vertex, random 3 chips); counts ballot violations. Run: ./a.out 5 200000 3 (levels, samples, seed).
#include <bits/stdc++.h>
using namespace std;
// Labeled chip-firing on undirected binary tree with root self-loop. Vertices 1..: children 2v,2v+1, parent v/2 (root: stays).
// Random firing: pick random unstable vertex, random 3 chips; smallest->left, largest->right, middle->parent (root keeps).
int L; mt19937_64 rng;
vector<vector<int>> chips;
bool ballotOK(){
  int nv=(1<<L)-1;
  // each vertex 1..nv has exactly 1 chip (stable config from 2^L-1 chips)
  for(int v=1; 2*v+1<=nv; v++){
    vector<int> Ls, Rs;
    function<void(int,vector<int>&)> col=[&](int u, vector<int>& out){ if(u>nv) return; for(int x:chips[u]) out.push_back(x); col(2*u,out); col(2*u+1,out); };
    col(2*v,Ls); col(2*v+1,Rs); sort(Ls.begin(),Ls.end()); sort(Rs.begin(),Rs.end());
    if(Ls.size()!=Rs.size()) return false;
    for(size_t i=0;i<Ls.size();i++) if(Ls[i]>Rs[i]) return false;
  }
  return true;
}
int main(int argc,char**argv){
  L=atoi(argv[1]); long samples=atol(argv[2]); rng.seed(atol(argv[3]));
  int N=(1<<L)-1; long bad=0; set<vector<int>> seen;
  for(long s=0;s<samples;s++){
    chips.assign(1<<(L+3),{}); for(int i=1;i<=N;i++) chips[1].push_back(i);
    vector<int> unstable={1};
    while(true){
      vector<int> U; for(int v=1;v<(int)chips.size();v++) if(chips[v].size()>=3) U.push_back(v);
      if(U.empty()) break;
      int v=U[rng()%U.size()];
      auto& c=chips[v]; shuffle(c.begin(),c.end(),rng);
      int a=c.back(); c.pop_back(); int b=c.back(); c.pop_back(); int d=c.back(); c.pop_back();
      int t[3]={a,b,d}; sort(t,t+3);
      chips[2*v].push_back(t[0]); chips[2*v+1].push_back(t[2]);
      if(v==1) chips[1].push_back(t[1]); else chips[v/2].push_back(t[1]);
    }
    vector<int> conf; for(int v=1;v<=N;v++){ if(chips[v].size()!=1){ printf("unexpected shape\n"); return 1;} conf.push_back(chips[v][0]); }
    seen.insert(conf);
    if(!ballotOK()){ bad++; if(bad<=3){ printf("BALLOT FAIL:"); for(int x:conf) printf(" %d",x); printf("\n"); } }
  }
  printf("L=%d samples=%ld distinct=%zu ballot_fail=%ld\n",L,samples,seen.size(),bad);
}
