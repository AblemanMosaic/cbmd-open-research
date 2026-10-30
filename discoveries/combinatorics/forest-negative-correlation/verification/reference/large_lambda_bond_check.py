"""Large-lambda law for connected spanning subgraphs (dual of the small-lambda law):
top-degree term of P_C(lambda) = C_{G/e}C_{G/f} - C_G C_{G/e/f} is N* lambda^(2m - c* - 2),
c* = least size of a bond (minimal edge cut) containing e and f, N* = number of such bonds."""
import subprocess, sys
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
def connected(vs,E):
    vs=set(vs)
    if not vs: return False
    start=next(iter(vs)); seen={start}; st=[start]
    while st:
        v=st.pop()
        for a,b in E:
            for x,y in ((a,b),(b,a)):
                if x==v and y in vs and y not in seen: seen.add(y); st.append(y)
    return seen==vs
def bonds(n,E):
    out=[]
    for S in range(1,1<<n):
        if not S&1: continue  # vertex 0 in S, avoid double count
        if S==(1<<n)-1: continue
        A=[v for v in range(n) if S>>v&1]; B=[v for v in range(n) if not S>>v&1]
        if connected(A,E) and connected(B,E):
            out.append(frozenset(k for k,(a,b) in enumerate(E) if (S>>a&1)!=(S>>b&1)))
    return out
good=bad=0
for nn in [int(a) for a in sys.argv[1:]] or (3,4,5,6,7):
    lines=subprocess.run(['./geng','-Cq',str(nn)],capture_output=True,text=True).stdout.split()
    out=subprocess.run(['./cnc','-v'],input='\n'.join(lines)+'\n',capture_output=True,text=True).stdout.split('\n')
    G={l:g6(l) for l in lines}; BD={l:bonds(*G[l]) for l in lines}
    for l in out:
        if not l.startswith('PAIR'): continue
        t=l.split(); g=t[1]; e=(int(t[2]),int(t[3])); f=(int(t[4]),int(t[5])); P=[int(x) for x in t[6:]]
        n,E=G[g]; m=len(E); ie=E.index(e); jf=E.index(f)
        sizes=[len(B) for B in BD[g] if ie in B and jf in B]
        top=max(i for i,x in enumerate(P) if x)
        cs=min(sizes)
        if top==2*m-cs-2 and P[top]==sizes.count(cs): good+=1
        else:
            bad+=1
            if bad<5: print('FAIL',g,e,f,top,P[top],2*m-cs-2,sizes.count(cs))
print('good',good,'bad',bad)
