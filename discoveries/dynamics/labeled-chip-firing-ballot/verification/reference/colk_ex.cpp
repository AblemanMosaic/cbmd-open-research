#include <bits/stdc++.h>
using namespace std;
// Exhaustive two-colour check of the generalized ballot property for k-ary trees, all thresholds t.
int k,L,N,NV,P;
typedef vector<unsigned char> St;
struct H{ size_t operator()(const St&s)const{ size_t h=1469598103934665603ULL; for(auto x:s){h^=x;h*=1099511628211ULL;} return h; } };
unordered_set<St,H> seen; long stab=0,bad=0;
bool ok(const St&s){ vector<int> sub(NV,0); for(int v=NV-1;v>=0;v--){ sub[v]=s[2*v]; for(int c=1;c<=k;c++){ long w=(long)k*v+c; if(w<NV) sub[v]+=sub[w]; } }
  for(int v=0;(long)k*v+k<NV;v++) for(int a=1;a<=k;a++) for(int b=a+1;b<=k;b++) if(sub[k*v+a]<sub[k*v+b]) return false; return true; }
void dfs(const St&s){
  if(!seen.insert(s).second) return; bool any=false;
  for(int v=0;v<NV;v++){ int R=s[2*v],B=s[2*v+1]; if(R+B<k+1) continue; any=true;
    if((long)k*v+k>=NV){ fprintf(stderr,"overflow\n"); exit(2);}
    for(int r=max(0,k+1-B); r<=min(k+1,R); r++){ St t=s; t[2*v]-=r; t[2*v+1]-=k+1-r; int child=0;
      for(int pos=1;pos<=k+1;pos++){ bool red=pos<=r; int d; if(pos==P) d=(v==0?0:(v-1)/k); else { child++; d=k*v+child; } t[2*d+(red?0:1)]++; }
      dfs(t); } }
  if(!any){ stab++; if(!ok(s)) bad++; }
}
int main(int argc,char**argv){ k=atoi(argv[1]); L=atoi(argv[2]); P=(k+2)/2;
  long p=1; N=0; for(int i=0;i<L;i++){N+=p;p*=k;} long tot=0; p=1; for(int i=0;i<L+1;i++){tot+=p;p*=k;} NV=tot;
  long tb=0; for(int t=1;t<N;t++){ seen.clear(); stab=0; bad=0; St s(2*NV,0); s[0]=t; s[1]=N-t; dfs(s); tb+=bad; printf("t=%d states=%zu stable=%ld fail=%ld\n",t,seen.size(),stab,bad); fflush(stdout);} 
  printf("k=%d L=%d total_fail=%ld\n",k,L,tb); }
