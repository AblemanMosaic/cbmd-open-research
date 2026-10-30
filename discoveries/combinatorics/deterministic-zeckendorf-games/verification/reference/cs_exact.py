"""Exact Combine Smallest length in polylog time, from the lemmas of §5.

L_CS(n) = n - Z(n) + S, and S is assembled level by level (P = 2, 4, ...):
  * the rounds of level P are K feeds of the counter Q_{P-2}; K is the first k
    with p - 3k - 2 C(k) < 5, where C(k) = floor((v + k F_s) / F_{s+1}) counts
    carries from counter value v (s = P - 2);
  * the counter's splits over k feeds are #B + (splits of Q_{s-2} over #B
    feeds), and #B is a floor sum (feeds landing in [F_s, F_{s+1}));
  * the tail is one more pile split, one feed, and the table of §5.3;
  * once the output would drop below 12 pieces the remaining configuration
    (O(log n) pieces) is rebuilt and simulated directly.
Every step is exact, so this computes L_CS(n) exactly; it is checked against
direct simulation (gate EXACT_n_le_N) and against the C simulator in
check_cs_large.py. Usage: cs_exact.py [N_MAX]  (prints JSON).
"""
import json

import sys
sys.setrecursionlimit(10000)
F=[1,1,2]
while len(F)<2000: F.append(F[-1]+F[-2])

def floor_sum(n,m,a,b):
    # sum_{i=0}^{n-1} floor((a*i+b)/m), a,b >= 0
    ans=0
    while True:
        if a>=m: ans+=(n-1)*n//2*(a//m); a%=m
        if b>=m: ans+=n*(b//m); b%=m
        y_max=a*n+b
        if y_max<m: return ans
        n,b,m,a = y_max//m, y_max%m, a, m

def count_B(s,v,k):
    # feeds j<k with (v+j F_s) mod F_{s+1} >= F_s
    M=F[s+1]
    return floor_sum(k,M,F[s],v+F[s-1]) - floor_sum(k,M,F[s],v)

def splits(s,v,k):
    """splits made by Q_s over k feeds from normal value v (on indices <= s)."""
    if k==0 or s<=1: return 0
    b=count_B(s,v,k)
    if s==2: return b
    if v>=F[s]: vs=v-F[s]
    elif v>=F[s-1]: vs=v-F[s-1]
    else: vs=v
    return b+splits(s-2,vs,b)

def carries(s,v,k):
    if s==0: return k
    return (v+k*F[s])//F[s+1]

def cs_step(c):
    if c[1]>=2: c[1]-=2; c[2]+=1; return 'm'
    for j in range(2,len(c)-1):
        if c[j-1] and c[j]: c[j-1]-=1; c[j]-=1; c[j+1]+=1; return 'm'
    for j in range(2,len(c)-1):
        if c[j]>=2:
            c[j]-=2; c[j+1]+=1; c[j-2 if j>=3 else 1]+=1; return 's'
    return None

def zeck_digits(v,upto):
    d=[0]*(upto+1)
    for i in range(upto,0,-1):
        if F[i]<=v: d[i]=1; v-=F[i]
    assert v==0
    return d

def simulate_splits(c):
    S=0
    while True:
        m=cs_step(c)
        if m is None: return S,c
        S+= m=='s'

def Z(n):
    z=0
    for i in range(len(F)-1,0,-1):
        if F[i]<=n: n-=F[i]; z+=1
    return z

def direct(n):
    c=[0]*120; c[1]=n; L=0
    while cs_step(c): L+=1
    return L

def fast(n):
    if n<200: return direct(n)
    S=0
    p=n//2
    out=0
    if n%2: p-=2; out=1
    P=2; v=0
    while True:
        s=P-2
        # rounds
        def pile_after(k): return p-3*k-2*carries(s,v,k)
        lo,hi=0,p+1   # find K = min k with pile_after(k) < 5 (pile before round k+1 must be >=5)
        while lo<hi:
            mid=(lo+hi)//2
            if pile_after(mid)<5: hi=mid
            else: lo=mid+1
        K=lo
        # rounds 1..K happen iff pile before each >=5: pile_after(K-1)>=5 holds by minimality
        q=out+K+carries(s,v,K)
        p2=pile_after(K)
        if q<12:
            # fallback: rebuild the configuration at level start and simulate directly
            c=[0]*(P+80)
            d=zeck_digits(v,max(s,1)) if s>=1 else [0]
            for i in range(1,len(d)):
                c[i]+=d[i]
            c[P]+=p; c[P+2]+=out
            s2,_=simulate_splits(c)
            return n-Z(n)+S+s2
        S+=K+splits(s,v,K)
        v=(v+K*F[s])%F[s+1] if s>=1 else 0
        p=p2
        if p<=1:
            vnew=v+p*F[P]; newp=q; newout=0
        else:
            S+=1   # pile split
            if s==0: typ='C'
            elif v>=F[s]: typ='B'
            elif v>=F[s-1]: typ='C'
            else: typ='A'
            S+=splits(s,v,1)
            carry= carries(s,v,1)>0
            v=(v+F[s])%F[s+1] if s>=1 else 0
            if p==2:
                vnew=v+(F[P-1] if carry else 0); newp=q-2; newout=1
            elif p==3:
                if typ=='A': vnew=v; newp=q+1; newout=0
                elif typ=='B': vnew=v+F[P-1]; newp=q+1; newout=0
                else: vnew=v; newp=q-4; newout=2
            else:
                if typ=='A': vnew=v+F[P]; newp=q+1; newout=0
                else: vnew=v; newp=q-1; newout=1
        P+=2; v=vnew; p=newp; out=newout


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 3000
    bad = [n for n in range(1, n_max + 1) if fast(n) != direct(n)]
    out = {
        "schema": "cbmd.deterministic-zeckendorf.cs-exact.v1",
        "n_max": n_max,
        "gates": {"EXACT_n_le_N_matches_direct_simulation": not bad},
        "mismatches": bad[:10],
        "L_CS_10_pow_30": fast(10 ** 30),
        "status": "PASS" if not bad else "FAIL",
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
