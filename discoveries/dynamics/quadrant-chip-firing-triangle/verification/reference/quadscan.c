/* For every N in [A,B]: stabilize N chips at the origin of the quadrant (row recursion
   F'(x) = floor(F(x-1)/2) + floor(F(x)/2) on antidiagonals) and test the generalized IKL
   Conjecture 7.3: with len(i) = number of nonzero entries of row i, the maximal tail of rows with
   consecutive -1 steps has exactly (max len) - 1 rows.  Also checks Prop 6.2 (|len step| = 1) and
   that rows have no interior zeros.  Prints failures and a summary. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  unsigned long long A=strtoull(argv[1],0,10),B=strtoull(argv[2],0,10);
  size_t cap=1<<16; uint64_t *cur=malloc(cap*8),*nxt=malloc(cap*8);
  int *lens=malloc(sizeof(int)*(1<<24)); char *thin=malloc(1<<24); long fails=0, step_viol=0, gap_viol=0, thin_fail=0;
  for(unsigned long long N=A;N<=B;N++){
    long lo=1,hi=1; cur[0]=0; cur[1]=N; size_t nrows=0;
    while(1){
      { int th=1; long L=hi-lo+1; for(long k=0;k<L;k++){ long d=k<L-1-k?k:L-1-k; if(cur[lo+k]>(uint64_t)(2*d+1)) {th=0;break;} } thin[nrows]=th; }
      lens[nrows++]=hi-lo+1;
      for(long x=lo;x<=hi;x++) if(cur[x]==0) gap_viol++;
      if((size_t)hi+3>=cap){ fprintf(stderr,"cap\n"); return 1; }
      long nlo=lo,nhi=hi+1;
      for(long x=nlo;x<=nhi;x++){ uint64_t a=(x-1>=lo)?cur[x-1]/2:0, b=(x<=hi)?cur[x]/2:0; nxt[x]=a+b; }
      while(nlo<=nhi&&nxt[nlo]==0) nlo++;
      while(nhi>=nlo&&nxt[nhi]==0) nhi--;
      if(nlo>nhi) break;
      uint64_t*t=cur;cur=nxt;nxt=t; /* re-anchor the window at index 1 (translation invariance) */
      memmove(cur+1,cur+nlo,(nhi-nlo+1)*8); hi=nhi-nlo+1; lo=1; cur[0]=0;
    }
    int longest=0; for(size_t r=0;r<nrows;r++){ if(lens[r]>longest) longest=lens[r]; if(r&&abs(lens[r]-lens[r-1])!=1) step_viol++; }
    size_t r=nrows-1; while(r>0&&lens[r-1]==lens[r]+1) r--;
    long tail=nrows-r;
    { size_t t=0; while(t<nrows && !thin[t]) t++;
      int ok = t<nrows && lens[t]==longest && (t==0 || lens[t-1]==longest-1);
      for(size_t q=t;q<nrows;q++) if(!thin[q]) ok=0;
      if(N>=4 && !ok){ thin_fail++; if(thin_fail<10) printf("THINFAIL N=%llu t=%zu len=%d longest=%d\n",N,t,t<nrows?lens[t]:-1,longest);} }
    if(A==B) printf("N=%llu rows=%zu longest=%d tail=%ld\n",N,nrows,longest,tail);
    if(N>=2 && tail!=longest-1){ fails++; if(fails<20) printf("FAIL N=%llu longest=%d tail=%ld\n",N,longest,tail); }
  }
  printf("SUMMARY N=%llu..%llu fails=%ld step_violations=%ld interior_zero=%ld thin_structure_fails=%ld\n",A,B,fails,step_viol,gap_viol,thin_fail);
  return 0;
}
