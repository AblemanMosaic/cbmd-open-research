// Monte Carlo estimate of P(sorted) for n = 2m+1 chips; usage: mc m protocol runs seed.
#include <bits/stdc++.h>
using namespace std;
// Monte Carlo: probability that labeled chip-firing on Z from n = 2m+1 chips at 0 ends sorted.
// protocol 1: uniform over all moves (site v, unordered pair at v): weight C(c_v,2). protocol 2: uniform unstable site, then uniform pair.
int main(int argc,char**argv){
  int m=atoi(argv[1]); int proto=atoi(argv[2]); long runs=atol(argv[3]); mt19937_64 rng(atol(argv[4]));
  int n=2*m+1, R=m+3, W=2*R+1; long sorted_=0;
  for(long r=0;r<runs;r++){
    vector<vector<int>> site(W); for(int i=1;i<=n;i++) site[R].push_back(i);
    vector<int> uns; // maintain list lazily
    while(true){
      int v=-1;
      if(proto==2){ uns.clear(); for(int x=0;x<W;x++) if(site[x].size()>=2) uns.push_back(x); if(uns.empty()) break; v=uns[rng()%uns.size()]; }
      else { long tot=0; for(int x=0;x<W;x++){ long c=site[x].size(); tot+=c*(c-1)/2; } if(tot==0) break; long pick=rng()%tot; for(int x=0;x<W;x++){ long c=site[x].size(); long w=c*(c-1)/2; if(pick<w){v=x;break;} pick-=w; } }
      auto& s=site[v]; int c=s.size(); int a=rng()%c, b=rng()%(c-1); if(b>=a) b++;
      int x=s[a], y=s[b]; if(a<b) swap(a,b); s.erase(s.begin()+a); s.erase(s.begin()+b);
      site[v-1].push_back(min(x,y)); site[v+1].push_back(max(x,y));
    }
    bool ok=true; for(int k=1;k<=n;k++){ int pos=R-m+k-1; if(site[pos].size()!=1||site[pos][0]!=k){ok=false;break;} }
    sorted_+=ok;
  }
  printf("m=%d proto=%d runs=%ld p_sorted=%.4f +- %.4f\n",m,proto,runs,(double)sorted_/runs, sqrt((double)sorted_/runs*(1-(double)sorted_/runs)/runs));
}
