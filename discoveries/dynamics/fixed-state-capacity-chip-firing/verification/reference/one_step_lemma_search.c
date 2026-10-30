// One-step lemma search (optional; needs a C compiler).
// Lemma: if every maximal one-bin packing is exact and a residue witness exists,
// some exact block can be closed so that a witness survives (U disjoint from the
// block, or the block a proper subset of U, keeps a witness).  Instances counted
// below satisfy a weakening of the hypothesis (only witnesses' fired totals are
// required to reach B) and violate the conclusion, so finding none covers every
// true violation in range.
// Build: cc -O2 -o one_step_lemma_search one_step_lemma_search.c
// Run:   ./one_step_lemma_search Bmax kmax      (recorded in evidence/bin_runs_exhaustive.txt)
// Level-1 test: search multisets A (values 1..B) such that
//  (P1) every inclusion-maximal subset with sum<=B has sum exactly B (equivalently no witness has fired total < B),
//  (W)  A has a witness, and
//  (X)  for every witness (fired F, unfired U) and every exact block E: E is not inside F, and E is not a proper subset of U.
// If none exist, the conjecture follows from Lemma X by induction on |A|.
#include <stdio.h>
#include <stdlib.h>
#define MAXK 14
static int s[1<<MAXK], mn[1<<MAXK]; static int a[MAXK]; static long long cnt=0, tested=0;
static int exactL[1<<MAXK];
static void check(int B,int k){
  int full=(1<<k)-1; s[0]=0; mn[0]=1<<30;
  for(int m=1;m<=full;m++){int i=__builtin_ctz(m); s[m]=s[m&(m-1)]+a[i]; mn[m]=mn[m&(m-1)]<a[i]?mn[m&(m-1)]:a[i];}
  if(s[full]<=B) return;
  int T=s[full]%B; int nw=0;
  int ne=0; for(int E=1;E<=full;E++) if(s[E]==B) exactL[ne++]=E;
  for(int U=1;U<full;U++){ int j=((s[U]-T)%B+B)%B; if(j>=1 && j<=mn[U]-1){
      nw++; int F=full^U; if(s[F]<B) return; // violates P1
      for(int e=0;e<ne;e++){int E=exactL[e]; if((E&U)==0) return; if((E&F)==0 && E!=U) return;}
  }}
  tested++;
  if(nw==0) return;
  cnt++; if(cnt<=20){printf("B=%d A=",B); for(int i=0;i<k;i++) printf("%d ",a[i]); printf("\n");}
}
static void rec(int B,int k,int pos,int minv){ if(pos==k){check(B,k);return;} for(int v=minv;v<=B;v++){a[pos]=v;rec(B,k,pos+1,v);} }
int main(int argc,char**argv){int Bmax=atoi(argv[1]),kmax=atoi(argv[2]);
  for(int B=2;B<=Bmax;B++){for(int k=1;k<=kmax;k++) rec(B,k,0,1); fprintf(stderr,"B=%d cnt=%lld\n",B,cnt);}
  printf("level1 instances found: %lld\n",cnt);}
