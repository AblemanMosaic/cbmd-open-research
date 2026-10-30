import itertools, random, sys
sys.path.insert(0,'.')
from small_lambda_matroid_check import rank_mod
def polys(cols,q):
    m=len(cols); indep={}
    for mask in range(1<<m):
        S=[cols[i] for i in range(m) if mask>>i&1]
        indep[mask]=(rank_mod(S,q)==len(S)) if S else True
    return indep
def R_of(indep,m,e,f):
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
    return R
# all binary matroids given by [I_r | A] with r=4, m=8 (A 4x4 over GF(2)): 65536 matrices
best=None; cnt_coefneg=0; cnt_p1neg=0
r=4
for bits in range(1<<16):
    A=[[(bits>>(4*i+j))&1 for j in range(4)] for i in range(4)]
    cols=[tuple(1 if i==k else 0 for i in range(4)) for k in range(4)]+[tuple(A[i][j] for i in range(4)) for j in range(4)]
    if any(all(x==0 for x in c) for c in cols): continue
    indep=polys(cols,2)
    for e,f in itertools.combinations(range(8),2):
        R=R_of(indep,8,e,f)
        if min(R)<0:
            cnt_coefneg+=1
            if sum(R)<0: cnt_p1neg+=1
            if best is None: best=(bits,e,f,R)
print('coefneg pairs',cnt_coefneg,'R(1)<0 pairs',cnt_p1neg,'example',best)
