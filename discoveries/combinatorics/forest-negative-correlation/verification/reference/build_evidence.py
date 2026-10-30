import json, re, hashlib, sys
def parse(fn):
    out=[]
    for l in open(fn):
        if l.startswith('SUMMARY'):
            d={}
            body=l.split(' at ')[0].split()[1:]
            for kv in body:
                k,v=kv.split('='); d[k]=float(v) if 'ratio' in k else int(v)
            d['min_ratio_at']=l.strip().split(' at ',1)[1]
            out.append(d)
        elif re.match(r'(P1NEG|COEFNEG|POSNEG)',l): raise SystemExit('violation line in '+fn)
    return out
def merge(rs):
    m={'graphs':0,'pairs':0,'zero':0,'p1neg':0,'coefneg':0}
    for r in rs:
        for k in m: m[k]+=r[k]
    best=min(rs,key=lambda r:r['min_ratio']); m['min_normalised_margin']=best['min_ratio']; m['min_margin_at']=best['min_ratio_at']
    if 'parallel_pairs' in rs[0]: m['parallel_pairs']=sum(r.get('parallel_pairs',0) for r in rs)
    return m
ev={'schema':'cbmd.forest-nc.runs.v1',
 'definition':'P(lambda) = X_{G/e} X_{G/f} - X_G X_{G/e/f}, X = forest (Z) or connected spanning subgraph (C) generating polynomial; checked: P(1) >= 0 and every coefficient >= 0, for every unordered pair of distinct edges of every 2-connected graph from geng -C (nauty 2.8.8).',
 'margin':'min_normalised_margin = min over pairs of P(1) / (X_{G/e}(1) X_{G/f}(1)) = P(e)P(f)/... i.e. (P(e)P(f) - P(ef)) / (P(e)P(f)) at lambda = 1; reported only as a diagnostic.',
 'forests':{}, 'connected':{}, 'multigraphs':{}}
for n in range(3,9):
    ev['forests'][str(n)]=merge(parse(f'f{n}.txt')); ev['connected'][str(n)]=merge(parse(f'c{n}.txt'))
ev['forests']['9']=merge(parse('f9r_0.txt')+parse('f9r_1.txt')); ev['connected']['9']=merge(parse('c9r_0.txt')+parse('c9r_1.txt'))
for key,fn,desc in (('forests_n6_mult_le3','mf6.txt','multig -m3 on all 2-connected 6-vertex graphs'),('connected_n6_mult_le3','mc6.txt','multig -m3 on all 2-connected 6-vertex graphs'),
                    ('forests_n7_mult_le2','mf7.txt','multig -m2 on all 2-connected 7-vertex graphs'),('connected_n7_mult_le2','mc7.txt','multig -m2 on all 2-connected 7-vertex graphs')):
    d=merge(parse(fn)); d['family']=desc
    t=[l for l in open(fn) if l.startswith('real')]; d['wall_time']=t[0].split()[1] if t else None
    ev['multigraphs'][key]=d
import subprocess
for key,n,mm in (('n6_mult_le3',6,3),('n7_mult_le2',7,2)):
    g=subprocess.run(['./geng','-Cq',str(n)],capture_output=True,text=True).stdout
    T=subprocess.run(['./multig','-q','-T','-m%d'%mm],input=g,capture_output=True,text=True).stdout.split('\n')
    tot=par=0
    for l in T:
        if not l.strip(): continue
        t=l.split(); ne=int(t[1]); ms=[int(x) for x in t[4::3]][:ne]; c=sum(ms)
        tot+=c*(c-1)//2; par+=sum(m*(m-1)//2 for m in ms)
    for model in ('forests','connected'):
        ev['multigraphs'][model+'_'+key]['edge_copy_pairs_covered']=tot
        ev['multigraphs'][model+'_'+key]['parallel_edge_copy_pairs_covered']=par
ev['multigraphs']['note']='pairs counts pairs of edge classes (bundles of parallel copies); copies in a class are interchangeable, so these cover edge_copy_pairs_covered pairs of individual edges. parallel_pairs counts classes of multiplicity >= 2.'
json.dump(ev,open(sys.argv[1],'w'),indent=1); open(sys.argv[1],'a').write('\n')
print(json.dumps({k:{n:(v['graphs'],v['pairs']) for n,v in ev[k].items() if isinstance(v,dict)} for k in ('forests','connected','multigraphs')}))
