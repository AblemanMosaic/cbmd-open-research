// Fibonacci Quilt game: length of a fixed priority strategy (move classes = rule kind x index 1..7, >=8; ties by index, dir=1 largest first).
#include <bits/stdc++.h>
using namespace std;
// Priority strategies for the Fibonacci Quilt game. A move class = (kind, idx) where idx<=7 means exact index, 8 means ">=8".
// kinds: 0 rule1, 1 rule2b, 2 rule3 opt A, 3 rule3 opt B (only i=4,6), 4 rule4, 5 rule5
const int K=60;
struct Mv{int kind,i; vector<int> rem,add;};
vector<Mv> allMoves(){
  vector<Mv> v;
  for(int i=1;i<=K-6;i++){
    v.push_back({0,i,{i,i+1},{i==1?3:i+3}});
    if(i>=2) v.push_back({1,i,{i,i+4},{i+5}});
    if(i==1) v.push_back({2,i,{1,1},{2}});
    else if(i==2) v.push_back({2,i,{2,2},{4}});
    else if(i==3) v.push_back({2,i,{3,3},{2,4}});
    else if(i==4){ v.push_back({2,i,{4,4},{1,6}}); v.push_back({3,i,{4,4},{3,5}}); }
    else if(i==5) v.push_back({2,i,{5,5},{1,7}});
    else if(i==6){ v.push_back({2,i,{6,6},{2,8}}); v.push_back({3,i,{6,6},{5,7}}); }
    else v.push_back({2,i,{i,i},{i-5,i+2}});
    if(i<=2) v.push_back({4,i,{i,i+3},{i+4}});
    else if(i==3) v.push_back({4,i,{3,6},{1,7}});
    else if(i<=5) v.push_back({4,i,{i,i+3},{1,i+4}});
    else if(i==6) v.push_back({4,i,{6,9},{2,10}});
    else v.push_back({4,i,{i,i+3},{i-5,i+4}});
  }
  v.push_back({5,1,{1,3},{4}});
  return v;
}
vector<Mv> MV;
int cls(const Mv&m){ return m.kind*9+min(m.i,8); }
long long play(long n, const vector<int>& prio /*rank per class*/, int dir){
  vector<long> c(K+10,0); c[1]=n; long long L=0;
  while(true){
    int best=-1, br=INT_MAX, bi=0;
    for(int t=0;t<(int)MV.size();t++){
      auto&m=MV[t]; bool ok=true;
      if(m.rem[0]==m.rem[1]){ if(c[m.rem[0]]<2) ok=false; }
      else for(int x:m.rem) if(c[x]<1) ok=false;
      if(!ok) continue;
      int r=prio[cls(m)]; int key=dir? -m.i : m.i;
      if(r<br || (r==br && key<bi)){br=r;bi=key;best=t;}
    }
    if(best<0){ if(c[1]&&c[5]){c[1]--;c[5]--;c[2]++;c[4]++;L++;continue;} break; }
    for(int x:MV[best].rem) c[x]--; for(int x:MV[best].add) c[x]++; L++;
  }
  return L;
}
int main(int argc,char**argv){
  // usage: fq_strategy N dir p0 p1 ... p53  (priority rank of each move class; lower = preferred)
  MV=allMoves(); int NC=54; long n=atol(argv[1]); int dir=atoi(argv[2]);
  vector<int> prio(NC); for(int i=0;i<NC;i++) prio[i]=atoi(argv[3+i]);
  long long L=play(n,prio,dir); printf("%ld %lld %.6f\n",n,L,(double)L/n);
}
