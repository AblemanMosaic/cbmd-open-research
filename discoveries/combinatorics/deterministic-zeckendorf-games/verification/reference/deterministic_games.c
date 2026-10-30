#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* deterministic Zeckendorf games; counts c[0..] for F1=1,F2=2,... */
#define M 64
static long c[M];
static int top;
static int stepSS(void){ /* split smallest (i>=2 idx1..), then ones, then add smallest */
  for(int i=1;i<=top;i++) if(c[i]>=2){ c[i]-=2; c[i+1]++; if(i==1) c[0]++; else c[i-2]++; if(i+1>top) top=i+1; return 1; }
  if(c[0]>=2){ c[0]-=2; c[1]++; if(top<1) top=1; return 1; }
  for(int i=1;i<=top;i++) if(c[i-1]>0&&c[i]>0){ c[i-1]--; c[i]--; c[i+1]++; if(i+1>top) top=i+1; return 1; }
  return 0;
}
static int stepCS(void){ /* ones, add smallest, split smallest */
  if(c[0]>=2){ c[0]-=2; c[1]++; if(top<1) top=1; return 1; }
  for(int i=1;i<=top;i++) if(c[i-1]>0&&c[i]>0){ c[i-1]--; c[i]--; c[i+1]++; if(i+1>top) top=i+1; return 1; }
  for(int i=1;i<=top;i++) if(c[i]>=2){ c[i]-=2; c[i+1]++; if(i==1) c[0]++; else c[i-2]++; if(i+1>top) top=i+1; return 1; }
  return 0;
}
int main(int argc,char**argv){
  int N=atoi(argv[1]); int which=argv[2][0]=='S';
  for(int n=1;n<=N;n++){
    memset(c,0,sizeof c); c[0]=n; top=0; long L=0;
    if(which) while(stepSS()) L++; else while(stepCS()) L++;
    printf("%d %ld\n",n,L);
  }
}
