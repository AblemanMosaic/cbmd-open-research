// Bin-run conjecture checker (optional; needs a C compiler).
// Exhaustive and random search for counterexamples to the residue-witness
// conjecture on the star.  The state of a bin run is its fired mask alone:
// by `fill_eq_mod` (Stuck.lean) a fill below B equals sum(mask) mod B, and a
// fill of exactly B behaves like 0 (nothing fits; the receiver resets).
// Build: cc -O2 -o bin_runs_exhaustive bin_runs_exhaustive.c
// Recorded output: evidence/bin_runs_exhaustive.txt
// State = fired mask; fill = sum(mask) mod B (fill B is reset immediately, nothing fits at B).
// reach[mask] if exists i in mask with reach[mask^i] and (sum(mask^i) mod B) + a_i <= B.
// blocked(mask): mask != full and for all i not in mask: (sum mod B) + a_i > B.
// Conjecture: exists blocked mask  =>  exists reachable blocked mask.
// Usage: ./bins exh Bmax kmax      (exhaustive over all multisets, values 1..B)
//        ./bins rand Bmin Bmax kmin kmax iters seed
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXK 18
static int sum[1<<MAXK];
static unsigned char reach[1<<MAXK];
static long long ninst=0, nwit=0, ncex=0;

static uint64_t rs;
static uint64_t rnd(void){ rs ^= rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }

// returns 1 if counterexample
static int check(int B, int k, const int *a){
  int full=(1<<k)-1;
  sum[0]=0;
  for(int m=1;m<=full;m++){ int i=__builtin_ctz(m); sum[m]=sum[m&(m-1)]+a[i]; }
  int wit=0, stuck=0;
  reach[0]=1;
  for(int m=0;m<=full;m++){
    if(m){
      reach[m]=0;
      for(int t=m;t;t&=t-1){ int i=__builtin_ctz(t); int p=m^(1<<i);
        if(reach[p] && (sum[p]%B)+a[i]<=B){reach[m]=1;break;} }
    }
    if(m==full) continue;
    int f=sum[m]%B; int bl=1;
    for(int i=0;i<k;i++) if(!(m>>i&1) && f+a[i]<=B){bl=0;break;}
    if(bl){ wit=1; if(reach[m]){stuck=1;break;} }
  }
  ninst++;
  if(wit) nwit++;
  if(wit && !stuck){
    ncex++;
    printf("COUNTEREXAMPLE B=%d a=",B); for(int i=0;i<k;i++) printf("%d ",a[i]); printf("\n"); fflush(stdout);
    return 1;
  }
  return 0;
}

static int a[MAXK];
static void rec(int B,int k,int pos,int minv){
  if(pos==k){ check(B,k,a); return; }
  for(int v=minv;v<=B;v++){ a[pos]=v; rec(B,k,pos+1,v); }
}

int main(int argc,char**argv){
  if(!strcmp(argv[1],"exh")){
    int Bmax=atoi(argv[2]), kmax=atoi(argv[3]);
    int Bmin = argc>4?atoi(argv[4]):1;
    for(int B=Bmin;B<=Bmax;B++){ for(int k=1;k<=kmax;k++) rec(B,k,0,1);
      printf("B=%d done inst=%lld wit=%lld cex=%lld\n",B,ninst,nwit,ncex); fflush(stdout);}
  } else {
    int Bmin=atoi(argv[2]),Bmax=atoi(argv[3]),kmin=atoi(argv[4]),kmax=atoi(argv[5]);
    long long it=atoll(argv[6]); rs=atoll(argv[7])*2654435761ULL+12345;
    for(long long t=0;t<it;t++){
      int B=Bmin+rnd()%(Bmax-Bmin+1); int k=kmin+rnd()%(kmax-kmin+1);
      int mode=rnd()%4;
      // value distributions: uniform; few distinct values; values near B/2,B/3; small+large mix
      int nd=1+rnd()%4; int vals[4]; for(int j=0;j<4;j++) vals[j]=1+rnd()%B;
      for(int i=0;i<k;i++){
        int v;
        if(mode==0) v=1+rnd()%B;
        else if(mode==1) v=vals[rnd()%nd];
        else if(mode==2){ int d=2+rnd()%4; v=B/d + (int)(rnd()%5) -2; }
        else { v = (rnd()%2)? 1+rnd()%(B/3+1) : B/2+rnd()%(B-B/2); }
        if(v<1)v=1; if(v>B)v=B; a[i]=v;
      }
      check(B,k,a);
    }
    printf("rand done inst=%lld wit=%lld cex=%lld\n",ninst,nwit,ncex);
  }
}
