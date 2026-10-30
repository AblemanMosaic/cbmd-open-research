"""Optional (needs numpy and scipy): the LP that produced fq_potential.json (alpha = 23/10, LP window 40, slack 1e-4, rounded to 1e-6, then re-verified exactly). The minimal-slope LP of fq_lp_common.solve is infeasible at alpha = 2.29 with slack, and its unconstrained limit is about 2.28988."""
import numpy as np, json
from fractions import Fraction as Fr
from scipy.optimize import linprog
from fq_lp_common import q, instances
alpha=Fr(23,10); I=40; J=I-9
nv=J
af=float(alpha)
def coeffs(idx):
    v=np.zeros(nv); const=0.0
    if idx<J: v[idx-1]=1
    else: const=af*q[idx]-idx/3; v[nv-1]=-1
    return v,const
A=[];b=[]
SL=1e-4
for rem,add in instances(1,I+12):
    v=np.zeros(nv); cst=0.0
    for i in add: a,c=coeffs(i); v+=a; cst+=c
    for i in rem: a,c=coeffs(i); v-=a; cst-=c
    mixed = min(rem+add) < J
    A.append(-v); b.append(cst-1-(SL if mixed else 0))
for i in range(1,J):
    v=np.zeros(nv); v[i-1]=1; A.append(v); b.append(af*q[i]-SL)
res=linprog(np.zeros(nv),A_ub=np.array(A),b_ub=np.array(b),bounds=[(0,0)]+[(None,None)]*(nv-1),method='highs')
print(res.status)
x=res.x
u=[Fr(0)]+[Fr(round(x[i]*10**6),10**6) for i in range(1,J-1)]
beta=Fr(round(x[-1]*10**6),10**6)
json.dump({"alpha":str(alpha),"J":J,"u":[str(v) for v in u],"beta":str(beta),
 "closed_form":"u_i = alpha q_i - i/3 - beta for i >= J"},open('potential.json','w'),indent=1)
def U(i):
    return u[i-1] if i<J else alpha*q[i]-Fr(i,3)-beta
bad=[(r,a) for r,a in instances(1,190) if sum(U(i) for i in a)-sum(U(i) for i in r)<1]
print('violations',len(bad), bad[:3]); print('u<=alpha q', all(U(i)<=alpha*q[i] for i in range(1,190)))
print('2a change', U(1)+U(5)-U(2)-U(4))
