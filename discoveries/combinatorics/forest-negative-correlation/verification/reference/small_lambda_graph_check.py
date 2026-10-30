"""Hypothesis: for 2-connected G and edges e != f, the lowest nonzero coefficient of
P_Z(lambda) = Z_{G/e}Z_{G/f} - Z_G Z_{G/e/f} sits at degree L-2, L = length of a shortest cycle
through both e and f, and equals the number of such shortest cycles."""
import subprocess, itertools, sys
from collections import deque
def g6(line):
    n=ord(line[0])-63; bits=[]
    for ch in line[1:]:
        v=ord(ch)-63; bits+=[(v>>(5-i))&1 for i in range(6)]
    E=[]; b=0
    for j in range(1,n):
        for i in range(j):
            if bits[b]: E.append((i,j))
            b+=1
    return n,E
def cycles_through(n,E,e,f):
    """count simple cycles containing e and f by length: each is a simple path b->a in G-e using f."""
    adj={v:set() for v in range(n)}
    for x,y in E: adj[x].add(y); adj[y].add(x)
    a,b=e; fs=frozenset(f); cnt={}
    stack=[(b,[b],False)]
    while stack:
        v,p,usedf=stack.pop()
        if v==a:
            if usedf: cnt[len(p)]=cnt.get(len(p),0)+1
            continue
        for w in adj[v]:
            if v==b and w==a: continue  # do not use e itself
            if w in p: continue
            stack.append((w,p+[w],usedf or frozenset((v,w))==fs))
    return cnt
bad=good=0
for nn in [int(a) for a in sys.argv[1:]] or (3,4,5,6,7):
    lines=subprocess.run(['./geng','-Cq',str(nn)],capture_output=True,text=True).stdout.split()
    out=subprocess.run(['./fnc','-v'],input='\n'.join(lines)+'\n',capture_output=True,text=True).stdout.split('\n')
    G={l:g6(l) for l in lines}
    for l in out:
        if not l.startswith('PAIR'): continue
        t=l.split(); g=t[1]; e=(int(t[2]),int(t[3])); f=(int(t[4]),int(t[5])); P=[int(x) for x in t[6:]]
        n,E=G[g]
        k=next(i for i,x in enumerate(P) if x)
        cnt=cycles_through(n,E,e,f); L=min(cnt)
        if k==L-2 and P[k]==cnt[L]: good+=1
        else:
            bad+=1
            if bad<10: print('FAIL',g,e,f,P[:6],cnt)
print('good',good,'bad',bad)
