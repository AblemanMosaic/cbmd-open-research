// Exhaustive longest Fibonacci Quilt game: prints "n max max/n memo_size" for n = 1..N (argument N). Rule 3(f) uses q5,q7 (value-preserving reading of the paper's q3,q7).
#include <bits/stdc++.h>
using namespace std;
// longest Fibonacci Quilt game, state = counts c[1..K]
const int K=24;
typedef array<unsigned char,K+8> St;
struct H{ size_t operator()(const St&s)const{ size_t h=0; for(auto x:s) h=h*131+x; return h; } };
unordered_map<St,int,H> memo;
int q[K+10];
int best(const St& c);
static inline void tryMove(const St& c, initializer_list<int> rem, initializer_list<int> add, int& b, bool& any){
  St d=c; for(int i:rem){ if(d[i]==0) return; d[i]--; } for(int i:add) d[i]++;
  any=true; int v=best(d)+1; if(v>b) b=v;
}
int best(const St& c){
  auto it=memo.find(c); if(it!=memo.end()) return it->second;
  int b=0; bool any=false;
  for(int i=1;i<=K-6;i++){
    if(c[i]&&c[i+1]) { if(i==1) tryMove(c,{1,2},{3},b,any); else tryMove(c,{i,i+1},{i+3},b,any); }
    if(i>=2&&c[i]&&c[i+4]) tryMove(c,{i,i+4},{i+5},b,any);
    if(c[i]>=2){
      if(i==1) tryMove(c,{1,1},{2},b,any);
      else if(i==2) tryMove(c,{2,2},{4},b,any);
      else if(i==3) tryMove(c,{3,3},{2,4},b,any);
      else if(i==4){ tryMove(c,{4,4},{1,6},b,any); tryMove(c,{4,4},{3,5},b,any); }
      else if(i==5) tryMove(c,{5,5},{1,7},b,any);
      else if(i==6){ tryMove(c,{6,6},{2,8},b,any); tryMove(c,{6,6},{5,7},b,any); }
      else tryMove(c,{i,i},{i-5,i+2},b,any);
    }
    if(c[i]&&c[i+3]){
      if(i<=2) tryMove(c,{i,i+3},{i+4},b,any);
      else if(i==3) tryMove(c,{3,6},{1,7},b,any);
      else if(i<=5) tryMove(c,{i,i+3},{1,i+4},b,any);
      else if(i==6) tryMove(c,{6,9},{2,10},b,any);
      else tryMove(c,{i,i+3},{i-5,i+4},b,any);
    }
  }
  if(c[1]&&c[3]) tryMove(c,{1,3},{4},b,any);
  if(!any && c[1]&&c[5]) tryMove(c,{1,5},{2,4},b,any);
  memo[c]=b; return b;
}
int main(int argc,char**argv){
  int N=atoi(argv[1]);
  for(int n=1;n<=N;n++){ St s{}; s[1]=n; int v=best(s); printf("%d %d %.4f %zu\n",n,v,(double)v/n,memo.size()); fflush(stdout); }
}
