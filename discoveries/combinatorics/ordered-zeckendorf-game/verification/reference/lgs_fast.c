/* Long Game Strategy of the ordered Zeckendorf game on counts: prints n, L, switches, merges, splits. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
/* Long Game Strategy of the ordered Zeckendorf game, tracked on counts; switches = inversions created. */
#define M 64
int main(int argc,char**argv){
  for(int a=1;a<argc;a++){
    long n=atol(argv[a]); long c[M]; memset(c,0,sizeof c); c[1]=n;
    long long L=0, sw=0, merges=0, splits=0;
    while(1){
      if(c[1]>=2){ sw+=c[1]-2; c[1]-=2; c[2]++; merges++; continue; }
      int j=-1; for(int i=M-2;i>=2;i--) if(c[i]>=2){ j=i; break; }
      if(j>0){ /* split rightmost duplicate */
        if(j==2){ sw+=c[2]-2; c[2]-=2; c[1]++; c[3]++; }
        else { sw+=c[j-1]+c[j]-2; c[j]-=2; c[j-2]++; c[j+1]++; }
        splits++; continue; }
      int i0=-1; for(int i=1;i<M-2;i++) if(c[i]>0&&c[i+1]>0){ i0=i; break; }
      if(i0>0){ sw+=c[i0+1]-1; c[i0]--; c[i0+1]--; c[i0+2]++; merges++; continue; }
      break;
    }
    L=sw+merges+splits;
    double phi=(1+sqrt(5))/2;
    printf("%ld L=%lld sw=%lld merges=%lld splits=%lld kappa=%.6f\n",n,L,sw,merges,splits,((double)n*n/2-L)/(n*log(n)/log(phi)));
  }
}
