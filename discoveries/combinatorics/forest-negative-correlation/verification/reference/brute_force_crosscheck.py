import sys, itertools, subprocess
def g6(line):
    n=ord(line[0])-63; bits=[]
    for ch in line[1:]:
        v=ord(ch)-63; bits += [(v>>(5-i))&1 for i in range(6)]
    E=[]; b=0
    for j in range(1,n):
        for i in range(j):
            if bits[b]: E.append((i,j))
            b+=1
    return n,E
def acyclic(n,edges):
    p=list(range(n))
    def f(x):
        while p[x]!=x: p[x]=p[p[x]]; x=p[x]
        return x
    for u,v in edges:
        a,b=f(u),f(v)
        if a==b: return False
        p[a]=b
    return True
def polys(n,E):
    m=len(E); forests=[]
    for mask in range(1<<m):
        sub=[E[i] for i in range(m) if mask>>i&1]
        if acyclic(n,sub): forests.append(mask)
    return forests
def P_pair(n,E,forests,e,f):
    deg=2*n; Z=[0]*n; Ze=[0]*n; Zf=[0]*n; Zef=[0]*n
    for mask in forests:
        k=bin(mask).count('1'); Z[k]+=1
        if mask>>e&1: Ze[k]+=1
        if mask>>f&1: Zf[k]+=1
        if mask>>e&1 and mask>>f&1: Zef[k]+=1
    # P = (Ze*Zf - Z*Zef)/lambda^2
    R=[0]*(2*n)
    for i in range(n):
        for j in range(n):
            R[i+j]+=Ze[i]*Zf[j]-Z[i]*Zef[j]
    assert R[0]==0 and R[1]==0
    return R[2:2*n-1]
ok=bad=0
for nn in (3,4,5,6):
    lines=subprocess.run(['./geng','-q','-c',str(nn)],capture_output=True,text=True).stdout.split()
    out=subprocess.run(['./fnc','-v'],input='\n'.join(lines)+'\n',capture_output=True,text=True).stdout.split('\n')
    cpairs={}
    for l in out:
        if l.startswith('PAIR'):
            t=l.split(); cpairs[(t[1],int(t[2]),int(t[3]),int(t[4]),int(t[5]))]=[int(x) for x in t[6:]]
    for line in lines:
        n,E=g6(line); F=polys(n,E)
        for a in range(len(E)):
            for b in range(a+1,len(E)):
                P=P_pair(n,E,F,a,b)
                key=(line,E[a][0],E[a][1],E[b][0],E[b][1])
                C=cpairs[key]
                if P==C[:len(P)] and all(x==0 for x in C[len(P):]): ok+=1
                else: bad+=1; print('MISMATCH',key,P,C)
print('pairs agree',ok,'mismatch',bad)
