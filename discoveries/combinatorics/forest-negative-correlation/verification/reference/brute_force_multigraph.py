"""Brute-force check of fnc/cnc on multigraphs (multig -T format), n <= 5, multiplicity <= 3."""
import subprocess, sys
def find(p,x):
    while p[x]!=x: p[x]=p[p[x]]; x=p[x]
    return x
def ok_forest(n,edges):
    p=list(range(n))
    for u,v in edges:
        a,b=find(p,u),find(p,v)
        if a==b: return False
        p[a]=b
    return True
def ok_conn(n,edges):
    p=list(range(n))
    for u,v in edges: p[find(p,u)]=find(p,v)
    return len({find(p,x) for x in range(n)})==1
def P_of(n,copies,good,e,f):
    M=len(copies)+1; Z=[0]*M; Ze=[0]*M; Zf=[0]*M; Zef=[0]*M
    for mask in range(1<<len(copies)):
        sub=[copies[i] for i in range(len(copies)) if mask>>i&1]
        if not good(n,sub): continue
        k=len(sub); Z[k]+=1
        if mask>>e&1: Ze[k]+=1
        if mask>>f&1: Zf[k]+=1
        if mask>>e&1 and mask>>f&1: Zef[k]+=1
    R=[0]*(2*M)
    for i in range(M):
        for j in range(M): R[i+j]+=Ze[i]*Zf[j]-Z[i]*Zef[j]
    assert R[0]==0 and R[1]==0
    R=R[2:]
    while R and R[-1]==0: R.pop()
    return R
total=bad=0
for nn in (3,4,5):
    g=subprocess.run(['./geng','-Cq',str(nn)],capture_output=True,text=True).stdout
    T=subprocess.run(['./multig','-q','-T','-m3'],input=g,capture_output=True,text=True).stdout.strip().split('\n')
    T=[l for l in T if sum(int(x) for x in l.split()[4::3]) <= 13]
    for prog,good in (('./fnc',ok_forest),('./cnc',ok_conn)):
        # recompute per line individually for unambiguous parsing
        for line in T:
            o=subprocess.run([prog,'-v','-T'],input=line+'\n',capture_output=True,text=True).stdout.split('\n')
            t=line.split(); n=int(t[0]); ne=int(t[1]); cls=[(int(t[2+3*k]),int(t[3+3*k]),int(t[4+3*k])) for k in range(ne)]
            copies=[]; first={}
            for (a,b,c) in cls:
                first[(min(a,b),max(a,b))]=len(copies)
                copies += [(a,b)]*c
            rows=[l for l in o if l.startswith('PAIR')]
            for r in rows:
                body=r[len('PAIR '+line)+1:].split()
                a1,b1,a2,b2=map(int,body[:4]); Pc=[int(x) for x in body[4:]]
                e=first[(a1,b1)]; f=first[(a2,b2)]+(1 if (a1,b1)==(a2,b2) else 0)
                Pb=P_of(n,copies,good,e,f)
                total+=1
                if not (Pb==Pc[:len(Pb)] and all(x==0 for x in Pc[len(Pb):])): bad+=1; print('MISMATCH',prog,line,body[:4],Pb,Pc)
            # check pair count: classes pairs + parallel (cnc only prints parallel)
            exp=len(cls)*(len(cls)-1)//2 + (sum(1 for c in cls if c[2]>=2) if prog=='./cnc' else 0)
            if len(rows)!=exp: bad+=1; print('COUNT',prog,line,len(rows),exp)
print('checked',total,'bad',bad)
