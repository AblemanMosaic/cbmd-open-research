"""Generalized live-set conditions for Petri nets with capacities.

The chip-firing notions refine as follows.

  usable t      : every input threshold of t fits inside the capacities,
                  pre[t][q'] <= cap[q'] for all q'.  A transition that is not
                  usable can never fire, whatever the marking.
  Live q        : some USABLE transition consumes from q.
  q -> q'       : a usable consumer of q produces into q'.
  bound         : for every usable t producing into q', some usable consumer s of
                  q' satisfies pre[s][q'] + post[t][q'] <= cap[q'] + 1.
  closed        : a usable transition produces only into live places.
  ordered       : the arc relation on live places is acyclic.
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import product
from petri import preserves, nets

def usable(pre, cap, t, P):
    return all(pre[t][q] <= cap[q] for q in range(P))

def conditions(pre, post, cap, P, T):
    U = [t for t in range(T) if usable(pre, cap, t, P)]
    live = {q for q in range(P) if any(pre[t][q] > 0 for t in U)}
    # closed: a usable transition produces only into live places
    for t in U:
        for q in range(P):
            if post[t][q] > 0 and q not in live:
                return False
    # bound: some usable consumer of the target admits the bundle
    for t in U:
        for q in range(P):
            if post[t][q] <= 0: continue
            cons = [s for s in U if pre[s][q] > 0]
            if not cons: return False
            if not any(pre[s][q] + post[t][q] <= cap[q] + 1 for s in cons):
                return False
    # ordered: place graph on live places, q -> q' when a usable consumer of q feeds q'
    def feeds(q):
        out = set()
        for t in U:
            if pre[t][q] > 0:
                for qq in range(P):
                    if post[t][qq] > 0: out.add(qq)
        return out
    colour = {q: 0 for q in live}
    def dfs(q):
        colour[q] = 1
        for qq in feeds(q):
            if qq in live:
                if colour[qq] == 1: return True
                if colour[qq] == 0 and dfs(qq): return True
        colour[q] = 2; return False
    if any(colour[q] == 0 and dfs(q) for q in list(live)): return False
    return True

def run(P, T, maxw, capmax):
    tt=tf=ft=ff=0; unsound=[]; incomplete=[]
    for pre,post in nets(P,T,maxw):
        for cap in product(range(capmax+1),repeat=P):
            ok,wit=preserves(pre,post,list(cap),P,T)
            if ok is None: continue
            pred=conditions(pre,post,list(cap),P,T)
            if pred and ok: tt+=1
            elif pred and not ok:
                tf+=1
                if len(unsound)<4: unsound.append({"pre":pre,"post":post,"capacity":list(cap),**wit})
            elif ok and not pred:
                ft+=1
                if len(incomplete)<4: incomplete.append({"pre":pre,"post":post,"capacity":list(cap)})
            else: ff+=1
    return {"box":{"P":P,"T":T,"maxw":maxw,"capmax":capmax},
            "both":tt,"UNSOUND":tf,"INCOMPLETE":ft,"neither":ff,
            "sound": tf==0, "exact": tf==0 and ft==0,
            "unsound_samples":unsound,"incomplete_samples":incomplete}

if __name__=="__main__":
    print(json.dumps({"P2T2":run(2,2,2,3),"P3T3":run(3,3,1,2),"P2T3":run(2,3,2,2)},indent=1))
