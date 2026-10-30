import sys, itertools
W=40; O=W//2  # window positions -O..O-1
def stab_unlabeled(n,S):
    c=[0]*W; c[O]=n
    while True:
        moved=False
        for v in range(1,W-1):
            m=1 if (v-O) in S else 0
            if c[v]>=2+m:
                k=c[v]//(2+m)  # fire k times at once
                c[v]-=k*(2+m); c[v]+=k*m; c[v-1]+=k; c[v+1]+=k; moved=True
        if not moved: return c
def occ(c): 
    idx=[i for i,x in enumerate(c) if x]; return idx[0]-O, idx[-1]-O
def sorts(n,S):
    """two-colour exhaustive: return (True,None) if every reachable stable colouring for every t is sorted."""
    for t in range(1,n):
        start=[0]*(2*W); start[2*O]=t; start[2*O+1]=n-t; start=tuple(start)
        seen={start}; stack=[start]
        while stack:
            s=stack.pop(); any_=False
            for v in range(1,W-1):
                R,B=s[2*v],s[2*v+1]; m=1 if (v-O) in S else 0; d=2+m
                if R+B<d: continue
                any_=True
                for r in range(max(0,d-B),min(d,R)+1):
                    u=list(s); u[2*v]-=r; u[2*v+1]-=d-r
                    # lowest -> left (red iff r>=1); highest -> right (red iff r==d); middle stays (red iff r>=2) if loop
                    u[2*(v-1)+(0 if r>=1 else 1)]+=1
                    u[2*(v+1)+(0 if r==d else 1)]+=1
                    if m: u[2*v+(0 if r>=2 else 1)]+=1
                    u=tuple(u)
                    if u not in seen: seen.add(u); stack.append(u)
            if not any_:
                # sorted iff no blue strictly left of a red
                lastblue_seen=False
                for v in range(W):
                    if s[2*v] and lastblue_seen: return False,(t,s)
                    if s[2*v+1]: lastblue_seen=True
    return True,None
if __name__=='__main__':
    found=0
    sets=[]
    for size in range(0,4):
        for S in itertools.combinations(range(-3,4),size): sets.append(set(S))
    for S in sets:
        for n in range(2,int(sys.argv[1])+1):
            a=occ(stab_unlabeled(n,S)); b=occ(stab_unlabeled(n-1,S))
            if a[0]<b[0] and a[1]>b[1]:
                ok,w=sorts(n,S)
                if not ok:
                    found+=1; print('COUNTEREXAMPLE S=',sorted(S),'n=',n,'t=',w[0]); sys.stdout.flush()
    print('done, counterexamples',found)
