"""Exact check on cyclic A = Z_n: n*kappa = prod_{d | n, d > 1} N(lambda_d), with
lambda_d = sum_{x in S} (1 - zeta_d^x); p^2 | N(lambda_d) when d = p^k; and when s >= 3,
N(lambda_n) >= (3/2)^phi(n) * (p^2 if n = p^e else 1)."""
import itertools, sys
from sympy import cyclotomic_poly, resultant, symbols, divisors, factorint, totient
from cayley_jac import jac
z=symbols('z')
def N(d,S):
    f=sum(1-z**(x%d) for x in S)
    return abs(int(resultant(cyclotomic_poly(d,z),f,z)))
maxn,maxs=int(sys.argv[1]),int(sys.argv[2]); cnt=bad=0
from math import gcd
for n in range(2,maxn+1):
    for s in range(2,maxs+1):
        for S in itertools.combinations_with_replacement(range(1,n),s):
            if sum(S)%n: continue
            g=0
            for x in S: g=gcd(g,x)
            if gcd(g,n)!=1: continue
            k=1
            for d in jac((n,),[(x,) for x in S]): k*=d
            prod=1; ok=True
            for d in divisors(n)[1:]:
                Nd=N(d,S); prod*=Nd
                f=factorint(d)
                if len(f)==1:
                    p=list(f)[0]
                    if Nd%(p*p): ok=False
            if prod!=n*k: ok=False
            if s>=3:
                f=factorint(n); base=(list(f)[0]**2 if len(f)==1 else 1)
                if N(n,S) < (1.5**int(totient(n)))*base*(1-1e-12): ok=False
            cnt+=1
            if not ok: bad+=1; print('FAIL',n,S)
print('checked',cnt,'failures',bad)
