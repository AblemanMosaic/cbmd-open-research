"""Bounded deterministic data helpers. Integrity is not authentication."""
from __future__ import annotations
import hashlib, json, os, re
from pathlib import Path

class Refusal(ValueError):
    def __init__(self, code: str): super().__init__(code); self.code=code

def require(ok: bool, code: str) -> None:
    if not ok: raise Refusal(code)

def canonical(value) -> bytes:
    def check(x):
        require(type(x) in (dict,list,str,int,bool,type(None)), 'NON_CANONICAL_TYPE')
        if type(x) is int: require(abs(x) <= 2**256, 'INTEGER_LIMIT')
        if type(x) is str: require(len(x)<=2000000, 'STRING_LIMIT')
        if type(x) is dict:
            require(all(type(k) is str for k in x), 'NON_STRING_KEY')
            for v in x.values(): check(v)
        if type(x) is list:
            require(len(x)<=100000, 'LIST_LIMIT')
            for v in x: check(v)
    check(value)
    return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False,allow_nan=False).encode()

def digest(value) -> str: return hashlib.sha256(canonical(value)).hexdigest()
def sha(data: bytes) -> str: return hashlib.sha256(data).hexdigest()
def read_json(path: Path):
    raw=path.read_bytes();require(len(raw)<=32*1024*1024,'JSON_BYTE_LIMIT')
    def pairs(ps):
        d={}
        for k,v in ps: require(k not in d,'DUPLICATE_KEY');d[k]=v
        return d
    def bad(_): raise Refusal('NON_INTEGER_JSON')
    out=json.loads(raw,object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
    canonical(out);return out

def safe_relative(root: Path, value: str) -> Path:
    require(type(value) is str and value and '\\' not in value and ':' not in value,'UNSAFE_PATH')
    require(not value.startswith('/') and all(x not in ('','.','..') for x in value.split('/')),'UNSAFE_PATH')
    p=root.joinpath(*value.split('/'))
    require(p.resolve().is_relative_to(root.resolve()),'PATH_ESCAPE')
    for q in [p,*p.parents]:
        if q==root.parent:break
        require(not q.is_symlink(),'SYMLINK')
    return p

def receipt(kind: str, payload: dict) -> dict:
    body={'schema':'cbmd.receipt.v1','kind':kind,**payload,
          'standing':'INFORMATION_ONLY','authority_effect':'NONE','real_a5':False,'g0':'CLOSED'}
    return {**body,'receipt_root':digest(body)}

def verify_receipt(r: dict) -> bool:
    return type(r) is dict and r.get('receipt_root')==digest({k:v for k,v in r.items() if k!='receipt_root'}) and r.get('standing')=='INFORMATION_ONLY' and r.get('authority_effect')=='NONE' and r.get('real_a5') is False and r.get('g0')=='CLOSED'
