import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import product
from petri import preserves, nets, ordinarily_enabled

def cf_shape(pre, post, P, T):
    """True chip-firing shape: each transition consumes from exactly one place,
    distinct transitions consume distinct places, and no transition produces back
    into the place it consumes (looplessness)."""
    consumed = []
    for t in range(T):
        qs = [q for q in range(P) if pre[t][q] > 0]
        if len(qs) != 1: return None
        q = qs[0]
        if post[t][q] != 0: return None          # self-feedback: not chip-firing
        consumed.append(q)
    if len(set(consumed)) != T: return None
    return consumed            # consumed[t] = the place transition t drains

def live_conditions(pre, post, cap, P, T, consumed):
    """Translate the live-set characterization into net terms.
    owner[q] = the transition draining q (if any). Live q: cap[q] >= pre[owner][q]."""
    owner = {q: t for t, q in enumerate(consumed)}
    live = {q for q in owner if cap[q] >= pre[owner[q]][q]}
    # arcs among places: q -> q' when the transition draining q feeds q'
    def feeds(q):
        t = owner[q]
        return [qq for qq in range(P) if post[t][qq] > 0]
    # closed: a live place feeds only live places
    for q in live:
        for qq in feeds(q):
            if qq not in live: return False
    # bound: cap[q'] + 1 >= threshold(q') + post[t_q][q']
    for q in live:
        t = owner[q]
        for qq in feeds(q):
            if qq not in owner: return False
            if cap[qq] + 1 < pre[owner[qq]][qq] + post[t][qq]: return False
    # ordered: the live place graph is acyclic
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

def run(P=2, T=2, maxw=2, capmax=3):
    tt = tf = ft = ff = skipped = 0
    unsound = []; incomplete = []
    cf_systems = 0
    for pre, post in nets(P, T, maxw):
        consumed = cf_shape(pre, post, P, T)
        if consumed is None: continue
        for cap in product(range(capmax + 1), repeat=P):
            ok, wit = preserves(pre, post, list(cap), P, T)
            if ok is None: skipped += 1; continue
            cf_systems += 1
            pred = live_conditions(pre, post, list(cap), P, T, consumed)
            if pred and ok: tt += 1
            elif pred and not ok:
                tf += 1
                if len(unsound) < 4: unsound.append({"pre":pre,"post":post,"capacity":list(cap),**wit})
            elif ok and not pred:
                ft += 1
                if len(incomplete) < 4: incomplete.append({"pre":pre,"post":post,"capacity":list(cap)})
            else: ff += 1
    return {"schema":"cbmd.petri-chipfiring-translation.v1",
            "box":{"places":P,"transitions":T,"max_arc_weight":maxw,"max_capacity":capmax},
            "chipfiring_shaped_systems": cf_systems,
            "confusion":{"both":tt,"UNSOUND":tf,"INCOMPLETE":ft,"neither":ff,"skipped":skipped},
            "exact": tf==0 and ft==0,
            "unsound_samples":unsound,"incomplete_samples":incomplete}

if __name__=="__main__":
    out={"P2T2":run(2,2,2,3),"P3T3":run(3,3,1,2)}
    print(json.dumps(out,indent=1))
