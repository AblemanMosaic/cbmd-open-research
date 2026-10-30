#include <bits/stdc++.h>
using namespace std;
// Random-restart greedy search in the 2-colour process for a ballot violation at vertex V0 (L, t given).
int L,N,NV,T,V0; mt19937_64 rng;
int main(int argc,char**argv){
  L=atoi(argv[1]); T=atoi(argv[2]); V0=atoi(argv[3]); long tries=atol(argv[4]); rng.seed(atol(argv[5]));
  N=(1<<L)-1; NV=1<<(L+1);
  for(long it=0; it<tries; it++){
    vector<int> R(NV,0),B(NV,0); R[1]=T; B[1]=N-T; vector<pair<int,int>> mv;
    // bias: prefer choices that send blue left/red right in subtree of V0's left/right child
    double bias = (rng()%1000)/1000.0;
    while(true){
      vector<int> U; for(int v=1;v<NV;v++) if(R[v]+B[v]>=3) U.push_back(v);
      if(U.empty()) break;
      int v=U[rng()%U.size()];
      int lo=max(0,3-B[v]), hi=min(3,R[v]);
      int k = (rng()%1000 < bias*1000) ? lo + (int)(rng()%(hi-lo+1)) : (rng()%2? lo: hi);
      R[v]-=k; B[v]-=3-k; if(k>=1) R[2*v]++; else B[2*v]++; if(k==3) R[2*v+1]++; else B[2*v+1]++;
      int p=v==1?1:v/2; if(k>=2) R[p]++; else B[p]++; mv.push_back({v,k});
    }
    // subtree reds
    vector<int> sub(NV+1,0); for(int v=NV-1;v>=1;v--) sub[v]=R[v]+(2*v<NV?sub[2*v]:0)+(2*v+1<NV?sub[2*v+1]:0);
    bool bad=false; int where=-1;
    for(int v=1;2*v+1<NV;v++) if((V0==0||v==V0) && sub[2*v]<sub[2*v+1]){bad=true;where=v;break;}
    if(bad){ fprintf(stderr,"found at try %ld vertex %d\n",it,where); printf("%zu\n",mv.size()); for(auto&m:mv) printf("%d %d\n",m.first,m.second); return 0; }
  }
  fprintf(stderr,"none\n"); return 1;
}
