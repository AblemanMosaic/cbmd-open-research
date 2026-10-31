# usage: build_evidence.py OUT.json [RAWDIR]
# RAWDIR holds the raw run outputs (default '.'; the shipped copies are in evidence/raw/).
# geng and multig (nauty 2.8.8) must be runnable; override with GENG=/path MULTIG=/path.
import json, re, hashlib, sys, os
RAW=sys.argv[2] if len(sys.argv)>2 else '.'
GENG=os.environ.get('GENG','./geng'); MULTIG=os.environ.get('MULTIG','./multig')
def parse(fn):
    out=[]
    for l in open(os.path.join(RAW,fn)):
        if l.startswith('SUMMARY'):
            d={}
            body=l.split(' at ')[0].split()[1:]
            for kv in body:
                k,v=kv.split('='); d[k]=float(v) if 'ratio' in k else int(v)
            # an empty residue class (graphs = 0) has no witness graph after 'at'
            s=l.strip()
            d['min_ratio_at']=s.split(' at ',1)[1] if ' at ' in s else ''
            out.append(d)
        elif re.match(r'(P1NEG|COEFNEG|POSNEG)',l): raise SystemExit('violation line in '+fn)
    return out
def merge(rs):
    m={'graphs':0,'pairs':0,'zero':0,'p1neg':0,'coefneg':0}
    for r in rs:
        for k in m: m[k]+=r[k]
    # fnc.c reports posneg (exact: P takes a negative value on (0, inf)); cnc.c reports
    # posneg_numeric (the same test, evaluated numerically).  Both must be 0.
    for k in ('posneg','posneg_numeric'):
        if all(k in r for r in rs): m[k]=sum(r[k] for r in rs)
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
# n = 10, forests only: fnc4.c over the 500 residue classes of geng -Cq 10 r/500, one SUMMARY per
# class (13 classes are empty).  f10.txt is those 500 summaries concatenated in class order.
chunks=parse('f10.txt')
if len(chunks)!=500: raise SystemExit('f10.txt has %d summaries, expected 500'%len(chunks))
ev['forests']['10']=merge(chunks)
ev['forests']['10']['chunks']=len(chunks)
ev['forests']['10']['empty_residue_classes']=sum(1 for c in chunks if c['graphs']==0)
ev['forests']['10']['tool']='fnc4.c (validated against fnc.c on all 2-connected graphs with n <= 8 by validate_fnc4.sh)'
for key,fn,desc in (('forests_n6_mult_le3','mf6.txt','multig -m3 on all 2-connected 6-vertex graphs'),('connected_n6_mult_le3','mc6.txt','multig -m3 on all 2-connected 6-vertex graphs'),
                    ('forests_n7_mult_le2','mf7.txt','multig -m2 on all 2-connected 7-vertex graphs'),('connected_n7_mult_le2','mc7.txt','multig -m2 on all 2-connected 7-vertex graphs')):
    d=merge(parse(fn)); d['family']=desc
    t=[l for l in open(os.path.join(RAW,fn)) if l.startswith('real')]; d['wall_time']=t[0].split()[1] if t else None
    ev['multigraphs'][key]=d
import subprocess
for key,n,mm in (('n6_mult_le3',6,3),('n7_mult_le2',7,2)):
    g=subprocess.run([GENG,'-Cq',str(n)],capture_output=True,text=True).stdout
    T=subprocess.run([MULTIG,'-q','-T','-m%d'%mm],input=g,capture_output=True,text=True).stdout.split('\n')
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
