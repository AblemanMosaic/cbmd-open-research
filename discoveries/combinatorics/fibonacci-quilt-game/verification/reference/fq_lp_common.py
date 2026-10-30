import numpy as np, sys
from fractions import Fraction as Fr
from scipy.optimize import linprog
q=[0,1,2,3,4]
while len(q)<200: q.append(q[-3]+q[-2])
def instances(lo,hi):
    R=[]
    for i in range(1,hi+1):
        R.append(([i,i+1],[3] if i==1 else [i+3]))
        if i>=2: R.append(([i,i+4],[i+5]))
        if i==1: R.append(([1,1],[2]))
        elif i==2: R.append(([2,2],[4]))
        elif i==3: R.append(([3,3],[2,4]))
        elif i==4: R+=[([4,4],[1,6]),([4,4],[3,5])]
        elif i==5: R.append(([5,5],[1,7]))
        elif i==6: R+=[([6,6],[2,8]),([6,6],[5,7])]
        else: R.append(([i,i],[i-5,i+2]))
        if i in (1,2): R.append(([i,i+3],[i+4]))
        elif i==3: R.append(([3,6],[1,7]))
        elif i in (4,5): R.append(([i,i+3],[1,i+4]))
        elif i==6: R.append(([6,9],[2,10]))
        else: R.append(([i,i+3],[i-5,i+4]))
    R.append(([1,3],[4]))
    return [(r,a) for r,a in R if max(r+a)<=hi]
def solve(alpha, I=40, J=None):
    J=J or I-9   # closed form for indices >= J: u_i = alpha q_i - i/3 - beta
    # variables: u_1..u_{J-1}, beta
    nv=J
    def coeffs(idx):
        v=np.zeros(nv); const=0.0
        if idx<J: v[idx-1]=1
        else: const=alpha*q[idx]-idx/3; v[nv-1]=-1
        return v,const
    A=[];b=[]
    for rem,add in instances(1,I+12):
        if max(rem+add)<=I+12:
            v=np.zeros(nv); cst=0.0
            for i in add: a,c=coeffs(i); v+=a; cst+=c
            for i in rem: a,c=coeffs(i); v-=a; cst-=c
            A.append(-v); b.append(cst-1)   # sum_add - sum_rem >= 1
    # u_i <= alpha q_i for i<J
    for i in range(1,J):
        v=np.zeros(nv); v[i-1]=1; A.append(v); b.append(alpha*q[i])
    bounds=[(0,0)]+[(None,None)]*(J-2)+[(None,None)]
    c=np.zeros(nv); c[nv-1]=-1  # maximize beta? any feasible
    res=linprog(np.zeros(nv),A_ub=np.array(A),b_ub=np.array(b),bounds=bounds,method='highs')
    return res
if __name__=="__main__":
    for alpha in (2.29,2.295,2.3,2.31,2.35):
        for I in (30,40,50):
            r=solve(alpha,I); print(alpha,I,r.status, (r.x[-1] if r.status==0 else None))
