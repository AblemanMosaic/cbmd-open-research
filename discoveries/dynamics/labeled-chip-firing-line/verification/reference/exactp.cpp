// Exact probability of the sorted outcome, labeled chip-firing on Z from n chips at 0; protocol 1 (uniform move) or 2 (uniform unstable site, then uniform pair). Layered by firing count (fixed by confluence of the unlabeled process).
#include <bits/stdc++.h>
using namespace std;
// Exact probability of sorted outcome under protocol 2 (uniform unstable site, uniform pair), labeled chips on Z.
int n;
typedef vector<signed char> St;
struct H{ size_t operator()(const St&s)const{ size_t h=1469598103934665603ULL; for(auto x:s){h^=(unsigned char)x;h*=1099511628211ULL;} return h; } };
int main(int argc,char**argv){ n=atoi(argv[1]); int proto=argc>2?atoi(argv[2]):2;
  unordered_map<St,double,H> cur; cur[St(n,0)]=1.0; double psorted=0, pend=0;
  while(!cur.empty()){
    unordered_map<St,double,H> nxt;
    for(auto&[s,p]:cur){
      map<int,vector<int>> at; for(int i=0;i<n;i++) at[s[i]].push_back(i);
      vector<int> U; long tot=0; for(auto&[q,v]:at) if(v.size()>=2){ U.push_back(q); tot+= (long)v.size()*(v.size()-1)/2; }
      if(U.empty()){ pend+=p; bool ok=true; for(int i=0;i<n;i++) if(s[i]!=i-(n-1)/2) ok=false; if(ok) psorted+=p; continue; }
      for(int q:U){ auto&v=at[q]; long pairs=(long)v.size()*(v.size()-1)/2;
        double w = proto==2 ? p/U.size()/pairs : p/tot;
        for(size_t a=0;a<v.size();a++) for(size_t b=a+1;b<v.size();b++){ St t=s; t[v[a]]=q-1; t[v[b]]=q+1; nxt[t]+=w; } }
    }
    cur.swap(nxt);
  }
  printf("n=%d proto=%d P(sorted)=%.10f total=%.6f\n",n,proto,psorted,pend);
}
