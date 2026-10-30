"""For q = p^k and multisets T of nonzero residues mod q with sum 0 mod q, compute
N_{Q(zeta_q)/Q}( sum_{x in T} (1 - zeta_q^x) ) exactly (resultant) and report cases with norm p^2
and |T| >= 3."""
import itertools, sys
from sympy import cyclotomic_poly, resultant, symbols, Poly
z=symbols('z')
def norm(q, T):
    f = sum(1 - z**x for x in T)
    return abs(int(resultant(cyclotomic_poly(q, z), Poly(f, z).as_expr(), z)))
for q in [int(a) for a in sys.argv[2:]]:
    p = next(d for d in range(2, q+1) if q % d == 0)
    hits=[]; tested=0
    for t in range(2, int(sys.argv[1])+1):
        for T in itertools.combinations_with_replacement(range(1, q), t):
            if sum(T) % q: continue
            tested += 1
            N = norm(q, T)
            if N == p*p and t >= 3: hits.append(T)
    print('q',q,'tested',tested,'norm p^2 with |T|>=3:',len(hits), hits[:8])
