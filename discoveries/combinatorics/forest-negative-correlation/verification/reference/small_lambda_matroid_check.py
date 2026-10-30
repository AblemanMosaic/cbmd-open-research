"""Small-lambda law for matroids: for distinct non-loop elements e,f of a matroid M with
independence polynomial Z(lambda) = sum_{I indep} lambda^{|I|}, the Rayleigh difference
R = Z_e Z_f - Z Z_ef equals N_c lambda^c + O(lambda^{c+1}), c = min size of a circuit containing
e and f, N_c = number of such circuits; R == 0 if no circuit contains both.  Checked on random
binary and ternary matroids (subset enumeration)."""
import itertools, random
def rank_mod(vectors, q):
    rows=[list(v) for v in vectors]; r=0; ncol=len(rows[0]) if rows else 0
    for c in range(ncol):
        piv=next((i for i in range(r,len(rows)) if rows[i][c]%q),None)
        if piv is None: continue
        rows[r],rows[piv]=rows[piv],rows[r]
        inv=pow(rows[r][c],q-2,q)
        rows[r]=[x*inv%q for x in rows[r]]
        for i in range(len(rows)):
            if i!=r and rows[i][c]%q:
                fac=rows[i][c]; rows[i]=[(a-fac*b)%q for a,b in zip(rows[i],rows[r])]
        r+=1
    return r
def check(cols,q):
    m=len(cols); indep={}
    for mask in range(1<<m):
        S=[cols[i] for i in range(m) if mask>>i&1]
        indep[mask]= (rank_mod(S,q)==len(S)) if S else True
    circuits=[mask for mask in range(1,1<<m) if not indep[mask] and all(indep[mask&~(1<<i)] for i in range(m) if mask>>i&1)]
    loops={i for i in range(m) if not indep[1<<i]}
    res=[]
    for e,f in itertools.combinations(range(m),2):
        if e in loops or f in loops: continue
        Z=[0]*(m+1);Ze=[0]*(m+1);Zf=[0]*(m+1);Zef=[0]*(m+1)
        for mask,ok in indep.items():
            if not ok: continue
            k=bin(mask).count('1'); Z[k]+=1
            if mask>>e&1: Ze[k]+=1
            if mask>>f&1: Zf[k]+=1
            if mask>>e&1 and mask>>f&1: Zef[k]+=1
        R=[0]*(2*m+2)
        for i in range(m+1):
            for j in range(m+1): R[i+j]+=Ze[i]*Zf[j]-Z[i]*Zef[j]
        cs=[bin(C).count('1') for C in circuits if C>>e&1 and C>>f&1]
        nz=[i for i,x in enumerate(R) if x]
        if not cs: res.append(not nz)
        else:
            c=min(cs); res.append(bool(nz) and nz[0]==c and R[c]==cs.count(c))
    return res
rng=random.Random(7); tot=bad=0
for trial in range(300):
    q=rng.choice([2,3]); r=rng.randint(2,5); m=rng.randint(r+1,min(9,r+5))
    cols=[tuple(rng.randrange(q) for _ in range(r)) for _ in range(m)]
    out=check(cols,q); tot+=len(out); bad+=out.count(False)
# uniform matroids U_{k,n} over GF(7) via Vandermonde-like columns
for k in range(1,5):
    for n in range(k+1,8):
        cols=[tuple(pow(x,i,7) for i in range(k)) for x in range(1,n+1)]
        out=check(cols,7); tot+=len(out); bad+=out.count(False)
print('pairs',tot,'bad',bad)
