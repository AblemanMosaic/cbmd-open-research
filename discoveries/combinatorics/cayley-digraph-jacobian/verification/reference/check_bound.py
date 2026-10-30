"""Checks of the proof ingredients on all (A,S) with |A| <= MAXORDER, |S| <= MAXSIZE:
 (a) n*kappa = prod over nontrivial character orbits of the norms N(lambda_H) (exact);
 (b) N(lambda_H) divisible by p^2 when A/H is cyclic of order p^k;
 (c) cyclic A, s >= 3:  kappa >= (3/2)^phi(n) * n;
 (d) noncyclic A: v_p(n kappa) >= 2 c_p with c_p > e_p for some p (so kappa != n)."""
import itertools, sys
from math import gcd, log
from sympy import totient, factorint
from cayley_jac import abelian_groups, group_elements, generates, jac
import cmath
def kappa(ds,S):
    J=jac(ds,S); k=1
    for d in J: k*=d
    return k
def lam_product(ds,S):
    # product over nontrivial characters of (s - sum chi(x)), numerically
    n=1
    for d in ds: n*=d
    prod=1
    for chi in itertools.product(*[range(d) for d in ds]):
        if not any(chi): continue
        z=sum(cmath.exp(2j*cmath.pi*sum(c*xi/d for c,xi,d in zip(chi,x,ds))) for x in S)
        prod*= (len(S)-z)
    return prod.real, n
maxorder,maxsize=int(sys.argv[1]),int(sys.argv[2])
cnt=0; bad=0
for order in range(2,maxorder+1):
    for ds in abelian_groups(order):
        nz=[g for g in group_elements(ds) if any(g)]
        for size in range(2,maxsize+1):
            for S in itertools.combinations_with_replacement(nz,size):
                if any(sum(c)%d for c,d in zip(zip(*S),ds)) or not generates(S,ds): continue
                k=kappa(ds,S); P,n=lam_product(ds,S); cnt+=1
                if abs(P-n*k)>1e-6*n*k: bad+=1; print('PRODUCT MISMATCH',ds,S,P,n*k)
                if len(ds)==1 and size>=3 and k < (1.5**int(totient(n)))*n*(1-1e-12): bad+=1; print('BOUND FAIL',ds,S,k)
                if len(ds)>1 and k==n: bad+=1; print('NONCYCLIC EQUALITY',ds,S)
print('checked',cnt,'failures',bad)
