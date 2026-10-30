import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json, sys
from itertools import product
import characterize as C

def pred_variant(a,s,c,n,drop):
    L=C.live(a,s,c,n)
    if not L: return True
    ok=True
    if drop!='acyclic': ok = ok and C.acyclic_on(a,n,L)
    if drop!='bound':   ok = ok and C.bound_on_live(a,s,c,n,L)
    if drop!='livedead':ok = ok and C.no_live_to_dead(a,c,n,L)
    return ok

def run(n_max=3,mm=2,ms=1,slack=2):
    out={}
    variants=['none','acyclic','bound','livedead']
    tally={v:{'unsound':0,'incomplete':0,'sample':None} for v in variants}
    for n in range(1,n_max+1):
        for a,s in C.digraphs(n,mm,ms):
            for c in product(*(range(C.od(a,s,v)+slack+1) for v in range(n))):
                actual=C.transfer_holds(a,s,tuple(c),n)
                if actual is None: continue
                for v in variants:
                    p=pred_variant(a,s,tuple(c),n,v)
                    if p and not actual:
                        tally[v]['unsound']+=1
                        if tally[v]['sample'] is None:
                            tally[v]['sample']={'arcs':[list(r) for r in a],'sink':list(s),'capacity':list(c),
                                                'outdeg':[C.od(a,s,w) for w in range(n)],'live':C.live(a,s,tuple(c),n)}
                    if actual and not p: tally[v]['incomplete']+=1
    out['ablation']=tally
    out['reading']={'none':'the full characterization; must be 0/0',
                    'acyclic':'acyclicity on live vertices dropped','bound':'capacity bound on live receivers dropped',
                    'livedead':'the no-live-to-dead condition dropped'}
    return out
print(json.dumps(run(),indent=1))
