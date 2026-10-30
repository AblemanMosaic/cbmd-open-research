/* Combine Smallest length for single n: prints "n L L/n" per argument. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define M 128
static long c[M]; static int top;
static int stepCS(void){
  if(c[0]>=2){ c[0]-=2; c[1]++; if(top<1) top=1; return 1; }
  for(int i=1;i<=top;i++) if(c[i-1]>0&&c[i]>0){ c[i-1]--; c[i]--; c[i+1]++; if(i+1>top) top=i+1; return 1; }
  for(int i=1;i<=top;i++) if(c[i]>=2){ c[i]-=2; c[i+1]++; if(i==1) c[0]++; else c[i-2]++; if(i+1>top) top=i+1; return 1; }
  return 0;
}
int main(int argc,char**argv){ for(int a=1;a<argc;a++){ long n=atol(argv[a]); memset(c,0,sizeof c); c[0]=n; top=0; long L=0; while(stepCS()) L++; printf("%ld %ld %.6f\n",n,L,(double)L/n);} }
