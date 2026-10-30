import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import product
from petri import preserves, nets
from petri2 import live_conditions

def shape(pre, post, P, T, allow_selffeed=False, allow_shared=False, allow_multi_input=False):
    consumed=[]
    for t in range(T):
        qs=[q for q in range(P) if pre[t][q]>0]
        if len(qs)!=1:
            if not allow_multi_input or len(qs)==0: return None
            qs=[qs[0]]                       # pick a representative input place
        q=qs[0]
        if post[t][q]!=0 and not allow_selffeed: return None
        consumed.append(q)
    if len(set(consumed))!=T and not allow_shared: return None
    return consumed

def run(relax, P=2, T=2, maxw=2, capmax=3):
    kw={'allow_selffeed':relax=='selffeed','allow_shared':relax=='shared','allow_multi_input':relax=='multi_input'}
    tt=tf=ft=ff=0; unsound=[]
    for pre,post in nets(P,T,maxw):
        c=shape(pre,post,P,T,**kw)
        if c is None: continue
        if relax!='none' and shape(pre,post,P,T) is not None: continue   # only NEWLY admitted nets
        for cap in product(range(capmax+1),repeat=P):
            ok,wit=preserves(pre,post,list(cap),P,T)
            if ok is None: continue
            pred=live_conditions(pre,post,list(cap),P,T,c)
            if pred and ok: tt+=1
            elif pred and not ok:
                tf+=1
                if len(unsound)<2: unsound.append({"pre":pre,"post":post,"capacity":list(cap),**wit})
            elif ok and not pred: ft+=1
            else: ff+=1
    return {"relaxation":relax,"both":tt,"UNSOUND":tf,"INCOMPLETE":ft,"neither":ff,
            "exact":tf==0 and ft==0,"unsound_samples":unsound}

if __name__=="__main__":
    print(json.dumps([run(r) for r in ('none','selffeed','shared','multi_input')],indent=1))
