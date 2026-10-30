// Exhaustive longest ordered Zeckendorf game M(n): prints "n M(n) memo_size" for n = 1..N (argument N).
#include <bits/stdc++.h>
using namespace std;
// exhaustive longest ordered Zeckendorf game; state = string of small ints (indices)
unordered_map<string,int> memo;
int M(const string& a){
  auto it=memo.find(a); if(it!=memo.end()) return it->second;
  int best=0; bool any=false; int n=a.size();
  for(int p=0;p+1<n;p++){
    char x=a[p],y=a[p+1];
    auto go=[&](const string& b){ any=true; int v=M(b); if(v+1>best) best=v+1; };
    if(x>y){ string b=a; swap(b[p],b[p+1]); go(b); }
    if(x==1&&y==1){ string b=a.substr(0,p)+string(1,2)+a.substr(p+2); go(b); }
    if(x==y&&x>=2){ string b=a.substr(0,p)+(x==2?string{1,3}:string{(char)(x-2),(char)(x+1)})+a.substr(p+2); go(b); }
    if(y==x+1){ string b=a.substr(0,p)+string(1,(char)(x+2))+a.substr(p+2); go(b); }
  }
  memo[a]=best; return best;
}
int main(int argc,char**argv){
  int N=atoi(argv[1]);
  for(int n=1;n<=N;n++){ string s(n,1); printf("%d %d %zu\n",n,M(s),memo.size()); fflush(stdout);}
}
