#include <bits/stdc++.h>
using namespace std;
// k-ary undirected labeled chip-firing (Inagaki-Lin): root self-loop; vertex v children k*v+1..k*v+k (0-indexed root 0), parent (v-1)/k.
// Fires with >= k+1 chips: sorted s1<..<s_{k+1}; s_p (p=ceil((k+1)/2)) -> parent; remaining in order -> children 1..k.
// Two-colour projection with r reds; random search for generalized-ballot violation:
// for vertex v and children a<b: #reds in subtree(a) >= #reds in subtree(b) must hold (equal sizes at the end).
int k,L,N,NV; mt19937_64 rng;
int main(int argc,char**argv){
  k=atoi(argv[1]); L=atoi(argv[2]); int T=atoi(argv[3]); long tries=atol(argv[4]); rng.seed(atol(argv[5]));
  N=1; {long p=1; N=0; for(int i=0;i<L;i++){N+=p;p*=k;}}
  long tot=0,p=1; for(int i=0;i<L+1;i++){tot+=p;p*=k;} NV=tot;
  int P=(k+2)/2; // ceil((k+1)/2)
  for(long it=0;it<tries;it++){
    vector<int> R(NV,0),B(NV,0); R[0]=T; B[0]=N-T; vector<pair<int,int>> mv;
    while(true){
      vector<int> U; for(int v=0;v<NV;v++) if(R[v]+B[v]>=k+1) U.push_back(v);
      if(U.empty()) break;
      int v=U[rng()%U.size()];
      if(k*v+k>=NV){ fprintf(stderr,"overflow\n"); return 2; }
      int lo=max(0,k+1-B[v]), hi=min(k+1,R[v]);
      int r = (rng()%3==0)? lo+(int)(rng()%(hi-lo+1)) : (rng()%2?lo:hi);
      R[v]-=r; B[v]-=k+1-r;
      // sorted positions 1..k+1, red iff pos<=r
      int child=0;
      for(int pos=1;pos<=k+1;pos++){
        bool red=pos<=r;
        int dest; if(pos==P) dest=(v==0?0:(v-1)/k); else { child++; dest=k*v+child; }
        if(red) R[dest]++; else B[dest]++;
      }
      mv.push_back({v,r});
    }
    vector<int> sub(NV,0); for(int v=NV-1;v>=0;v--){ sub[v]=R[v]; for(int c=1;c<=k;c++){ long w=(long)k*v+c; if(w<NV) sub[v]+=sub[w]; } }
    for(int v=0;(long)k*v+k<NV;v++) for(int a=1;a<=k;a++) for(int b=a+1;b<=k;b++)
      if(sub[k*v+a]<sub[k*v+b]){ fprintf(stderr,"found try %ld at vertex %d children %d<%d\n",it,v,a,b); printf("%zu\n",mv.size()); for(auto&m:mv) printf("%d %d\n",m.first,m.second); return 0; }
  }
  fprintf(stderr,"none\n"); return 1;
}
