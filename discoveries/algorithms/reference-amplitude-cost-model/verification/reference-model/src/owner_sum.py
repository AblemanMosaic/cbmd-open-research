"""Exact one-selected-slot reference. NOT the native SAT execution.

Literal numerator expansion and Lagrange interpolation follow the carried
LayoutNumerator / LayoutScaledMatrices / SubexpRowInterpolation definitions.
Packing uses actual list order, first occurrence and equal-type bucket ranks.
The prepared index uses an explicit sorted-list merge sort and binary searches;
comparison/coordinate/index preparation costs are counted, not called O(1).
"""
from __future__ import annotations
from dataclasses import dataclass, field
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb, gcd
from common import require, digest, Refusal

@dataclass
class Meter:
    counts: Counter=field(default_factory=Counter)
    def add(self,k,n=1): self.counts[k]+=n
    def json(self):return dict(sorted(self.counts.items()))

class Ring:
    def __init__(self, modulus: int|None, m: Meter):self.modulus=modulus;self.m=m
    def norm(self,a):return Fraction(a) if self.modulus is None else int(a)%self.modulus
    def add(self,a,b):self.m.add('ring_add');return self.norm(a+b)
    def mul(self,a,b):self.m.add('ring_mul');return self.norm(a*b)
    def inv(self,a):
        self.m.add('ring_inverse');a=self.norm(a)
        if self.modulus is None:require(a!=0,'NONUNIT');return 1/a
        require(gcd(a,self.modulus)==1,'NONUNIT');return pow(a,-1,self.modulus)
    def poly_add(self,a,b):
        out=[self.add(a[i] if i<len(a) else 0,b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))];return trim(out)
    def poly_mul(self,a,b):
        out=[self.norm(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]=self.add(out[i+j],self.mul(x,y))
        return trim(out)

def trim(a):
    a=list(a)
    while len(a)>1 and not a[-1]:a.pop()
    return tuple(a or [0])

def serial_poly(poly):
    return [[x.numerator,x.denominator] if isinstance(x,Fraction) else [int(x),1] for x in poly]

def label_cmp(a,b,m):
    m.add('label_comparisons')
    for x,y in zip(a,b):
        m.add('coordinate_comparisons')
        if x!=y:return -1 if x<y else 1
    return 0

def parity(A,R,m):
    # Exact Newton/binomial system, general A. Small bounded input only.
    rows=[[Fraction(comb(A+i,j)) for j in range(R)]+[Fraction((-1)**(A+i))] for i in range(R)]
    for j in range(R):
        p=next(i for i in range(j,R) if rows[i][j]);rows[j],rows[p]=rows[p],rows[j]
        x=rows[j][j];rows[j]=[v/x for v in rows[j]];m.add('parity_rational_cells',R+1)
        for i in range(R):
            if i!=j:
                x=rows[i][j];rows[i]=[a-x*b for a,b in zip(rows[i],rows[j])];m.add('parity_rational_cells',2*(R+1))
    require(all(row[-1].denominator==1 for row in rows),'NONINTEGRAL_PARITY')
    return [int(row[-1]) for row in rows]

def swap(u,S,Q):
    a=list(u)
    for t in S:a[t],a[Q+t]=a[Q+t],a[t]
    return tuple(a)

def literal_numerator(u,y,t,A,R,m):
    Q=len(u)//2;active=[p for p in range(Q) if p!=t];base=swap(u,active,Q)
    c=parity(A,R,m);n=0
    for j in range(R):
        for S in combinations(active,j):
            d=0
            for k in range(j+1):
                for B in combinations(S,k):
                    m.add('numerator_delta_terms');d+=(-1)**k*int(swap(base,B,Q)==y)
            n+=c[j]*2**(R-1-j)*d;m.add('integer_accumulations')
    return n

def source_row(u,y,A,R,ring,m):
    m.add('source_row_calls');Q=len(u)//2
    E=[t for t in range(Q) if y[t]!=u[Q+t]]
    out=(ring.norm(int(u==y)),)
    if len(E)>R:return out
    den=ring.norm(2**max(R-1,0));di=ring.inv(den)
    for t in E:
        # family is zero-extended unless both rows lie in Joint t y.head[t].
        n=literal_numerator(u,y,t,A,R,m) if u[t]==y[t] else 0
        value=ring.mul(ring.norm(-n),di)
        node=ring.norm(t+1)
        basis=(ring.norm(0),ring.inv(node))
        for s in E:
            if s==t:continue
            inv=ring.inv(ring.norm(t-s))
            basis=ring.poly_mul(basis,(ring.mul(ring.norm(-(s+1)),inv),inv))
        out=ring.poly_add(out,tuple(ring.mul(value,v) for v in basis))
    return trim(out)

def candidate(u,h,m):
    Q=len(h);a=u[:Q];d=u[Q:];slot=[]
    for x,y,z in zip(a,d,h):
        m.add('head_coordinate_tests')
        if z!=x and z!=y:return None
        slot.append(y if z==x else x)
    return tuple(h)+tuple(slot)

@dataclass(frozen=True)
class Layout:
    Q:int
    r:int
    labels:tuple
    pairs:tuple
    heads:tuple
    A:int=0
    R:int=2
    modulus:int|None=None
    def object(self):return {'Q':self.Q,'r':self.r,'labels':[list(x) for x in self.labels],'pairs':[list(x) for x in self.pairs],'heads':[list(x) for x in self.heads],'A':self.A,'R':self.R,'modulus':self.modulus}
    @property
    def root(self):return digest(self.object())

def validate(L):
    require(type(L.Q) is int and 1<=L.Q<=4 and type(L.r) is int and 2<=L.r<=3,'LAYOUT_BOUND')
    require(type(L.A) is int and 0<=L.A<=4 and type(L.R) is int and 0<=L.R<=4,'PARAMETER_BOUND')
    require(0<len(L.labels)<=4096 and len(L.labels)==len(L.pairs),'INCIDENCE_BOUND')
    require(L.modulus in (None,9,25),'DOMAIN_UNSUPPORTED')
    for h in L.heads:require(len(h)==L.Q and all(type(x) is int and 0<=x<L.r for x in h),'HEAD_INVALID')
    for u,p in zip(L.labels,L.pairs):
        require(len(u)==2*L.Q and all(type(x) is int and 0<=x<L.r for x in u),'LABEL_INVALID')
        require(len(p)==2 and all(type(x) is int and x>=0 for x in p) and p[0]<len(L.heads),'OWNER_INVALID')
        require(u[:L.Q]==L.heads[p[0]],'HEAD_INCOHERENT')
    if L.modulus:
        require(all(gcd(i,L.modulus)==1 for i in range(1,L.Q+1)),'NONUNIT_NODE')
        require(all(gcd(i-j,L.modulus)==1 for i in range(1,L.Q+1) for j in range(1,L.Q+1) if i!=j),'NONUNIT_DIFFERENCE')
    return {'layout_root':L.root,'incidences':len(L.labels),'status':'VALIDATED_REFERENCE_PREMISES'}

class Scan:
    def __init__(self,L,m):
        self.L=L;self.m=m;self.count=len(L.labels)
        for u in product(range(L.r),repeat=2*L.Q):
            self.count=min(self.count,len(self.bucket(u)));m.add('minimum_comparisons')
    def bucket(self,u):
        out=[]
        for i,v in enumerate(self.L.labels):
            self.m.add('incidence_scans')
            if label_cmp(v,u,self.m)==0:out.append(i)
        return out
    def first(self,p):
        for i,q in enumerate(self.L.pairs):
            self.m.add('pair_scans')
            if p==q:return i
        return None
    def lookup(self,i):
        b=self.bucket(self.L.labels[i])
        for rank,j in enumerate(b):
            self.m.add('index_scans')
            if i==j:return (rank,self.L.labels[i]) if rank<self.count else None
        raise Refusal('INDEX_NOT_FOUND')
    def vertex(self,b,u):
        xs=self.bucket(u)
        for j,v in enumerate(xs):
            self.m.add('index_scans')
            if j==b:return v
        raise Refusal('INVALID_BLOCK')

class Indexed:
    def __init__(self,L,m):
        self.L=L;self.m=m
        def cmp(x,y):
            c=label_cmp(x[0],y[0],m)
            if c:return c
            m.add('index_comparisons');return (x[1]>y[1])-(x[1]<y[1])
        def mergesort(xs,compare):
            if len(xs)<2:return xs
            k=len(xs)//2;a=mergesort(xs[:k],compare);b=mergesort(xs[k:],compare);out=[];i=j=0
            while i<len(a) and j<len(b):
                if compare(a[i],b[j])<=0:out.append(a[i]);i+=1
                else:out.append(b[j]);j+=1
                m.add('index_writes')
            out.extend(a[i:]);out.extend(b[j:]);m.add('index_writes',len(a)-i+len(b)-j);return out
        rows=mergesort([(u,i) for i,u in enumerate(L.labels)],cmp)
        self.buckets=[];self.location=[None]*len(L.labels)
        for u,i in rows:
            if not self.buckets or label_cmp(u,self.buckets[-1][0],m)!=0:self.buckets.append((u,[]))
            self.buckets[-1][1].append(i);m.add('index_writes')
        self.count=min(len(xs) for _,xs in self.buckets) if len(self.buckets)==L.r**(2*L.Q) else 0
        for u,xs in self.buckets:
            for rank,i in enumerate(xs):self.location[i]=(rank,u) if rank<self.count else None;m.add('index_writes')
        def pcmp(x,y):m.add('pair_comparisons');return (x>y)-(x<y)
        self.sorted_pairs=mergesort([(p,i) for i,p in enumerate(L.pairs)],pcmp)
        # Logical retained integer cells, not allocator byte measurement.
        self.storage=sum(2*L.Q+len(xs) for _,xs in self.buckets)+3*len(L.pairs)+2*len(self.location)
        m.add('retained_index_integer_cells',self.storage)
    def first(self,p):
        lo=0;hi=len(self.sorted_pairs)
        while lo<hi:
            mid=(lo+hi)//2;self.m.add('pair_comparisons')
            if self.sorted_pairs[mid][0]<p:lo=mid+1
            else:hi=mid
        self.m.add('pair_comparisons')
        return self.sorted_pairs[lo][1] if lo<len(self.sorted_pairs) and self.sorted_pairs[lo][0]==p else None
    def lookup(self,i):self.m.add('array_reads');return self.location[i]
    def vertex(self,b,u):
        lo=0;hi=len(self.buckets)
        while lo<hi:
            mid=(lo+hi)//2;c=label_cmp(self.buckets[mid][0],u,self.m)
            if c<0:lo=mid+1
            else:hi=mid
        require(lo<len(self.buckets) and label_cmp(self.buckets[lo][0],u,self.m)==0,'TYPE_NOT_FOUND')
        self.m.add('array_reads');return self.buckets[lo][1][b]

def evaluate(L,pack,pair,owner,strategy,m):
    require(type(owner) is int and 0<=owner<len(L.heads),'UNKNOWN_OWNER')
    O=Ring(L.modulus,m);i=pack.first(pair)
    if i is None:return (O.norm(0),)
    loc=pack.lookup(i)
    if strategy=='literal_scan':
        out=(O.norm(0),)
        for j,(own,_) in enumerate(L.pairs):
            m.add('owner_scans')
            if own!=owner:continue
            m.add('packed_source_calls')
            if loc is None:v=(O.norm(int(i==j)),)
            else:
                jl=pack.lookup(j)
                v=source_row(loc[1],jl[1],L.A,L.R,O,m) if jl is not None and jl[0]==loc[0] else (O.norm(0),)
            out=O.poly_add(out,v)
        return out
    if loc is None:return (O.norm(int(L.pairs[i][0]==owner)),)
    y=candidate(loc[1],L.heads[owner],m)
    if y is None:return (O.norm(0),)
    j=pack.vertex(loc[0],y);m.add('exact_owner_checks')
    if L.pairs[j][0]!=owner:return (O.norm(0),)
    m.add('packed_source_calls')
    return source_row(loc[1],y,L.A,L.R,O,m)

def fixture(Q=2,copies=2,modulus=None,collision=True,leftover=True):
    types=list(product(range(2),repeat=2*Q));heads=list(product(range(2),repeat=Q))
    if collision:heads=heads+heads
    labels=[];pairs=[]
    for b in range(copies):
        for k,u in enumerate(types):
            owner=next(i for i,h in enumerate(heads) if h==u[:Q])
            if collision and (k+b)%3==0:owner+=2**Q
            labels.append(u);pairs.append((owner,k%3)) # deliberate repeated pairs: first occurrence is required.
    if leftover:labels.append(types[0]);pairs.append((next(i for i,h in enumerate(heads) if h==types[0][:Q]),77))
    return Layout(Q,2,tuple(labels),tuple(pairs),tuple(heads),0,min(3,Q+1),modulus)

def run_fixture(L,queries=None):
    validate(L)
    if queries is None:
        pairs=sorted(set(L.pairs))+[(0,999)]
        queries=[(p,o) for p in pairs for o in range(len(L.heads))]
    outputs={};rows=[]
    for strategy in ['literal_scan','candidate_scan','prepared_index']:
        m=Meter();pack=Indexed(L,m) if strategy=='prepared_index' else Scan(L,m)
        prep=m.json();m.counts.clear()
        result=[serial_poly(evaluate(L,pack,p,o,strategy,m)) for p,o in queries]
        outputs[strategy]=result
        total=Counter(prep)+m.counts
        rows.append({'strategy':strategy,'preparation':prep,'execution':m.json(),'total':dict(sorted(total.items())), 'result_root':digest(result),'query_count':len(queries)})
    require(outputs['literal_scan']==outputs['candidate_scan']==outputs['prepared_index'],'OWNER_SUM_MISMATCH')
    return {'layout_root':L.root,'Q':L.Q,'domain':'Q' if L.modulus is None else 'Z/'+str(L.modulus),'incidences':len(L.labels),'owners':len(L.heads),'queries':len(queries),'rows':rows,'outputs':outputs['literal_scan']}
