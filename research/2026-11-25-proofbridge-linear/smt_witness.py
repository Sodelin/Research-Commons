"""Use Z3 to search for an integer certificate; verify the actual witness in Lean."""
import argparse
import ctypes
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import linear

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def json_bytes(o):
    return (json.dumps(o,sort_keys=True,ensure_ascii=True)+"\n").encode("ascii")

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

class Z3:
    def __init__(self,path):
        self.lib=ctypes.CDLL(str(path.resolve(strict=True)))
        self.fn={}
        for name,args,out in (
            ("Z3_mk_config",[],ctypes.c_void_p),
            ("Z3_del_config",[ctypes.c_void_p],None),
            ("Z3_mk_context",[ctypes.c_void_p],ctypes.c_void_p),
            ("Z3_del_context",[ctypes.c_void_p],None),
            ("Z3_eval_smtlib2_string",[ctypes.c_void_p,ctypes.c_char_p],ctypes.c_char_p),
            ("Z3_get_full_version",[],ctypes.c_char_p),
        ):
            fn=getattr(self.lib,name)
            fn.argtypes=args
            fn.restype=out
            self.fn[name]=fn

    def exec(self,query):
        conf=self.fn["Z3_mk_config"]()
        need(conf,"Z3 config failed")
        try:
            ctx=self.fn["Z3_mk_context"](conf)
        finally:
            self.fn["Z3_del_config"](conf)
        need(ctx,"Z3 context failed")
        try:
            out=self.fn["Z3_eval_smtlib2_string"](ctx,query.encode("ascii"))
            return out.decode("ascii").strip()
        finally:
            self.fn["Z3_del_context"](ctx)

    def version(self):
        return self.fn["Z3_get_full_version"]().decode("ascii")

def read_goal(path):
    with path.open("rb") as f:
        raw=f.read(16385)
    need(len(raw)<=16384,"oversized goal")
    c=json.loads(raw,object_pairs_hook=linear.object_pairs)
    linear.fields(c,["schema","variables","premises","target"])
    need(c["schema"]=="commons.linear-int.goal.v1","wrong goal schema")
    n=len(c["premises"])
    candidate={**c,"schema":linear.SCHEMA,"multipliers":[1]*n}
    # Exact parser validates all numerals and bounds before text enters SMT.
    linear.parse(json_bytes(candidate))
    return c,raw

def query_for(c):
    ps=c["premises"]; target=c["target"]
    names=["m"+str(i) for i in range(len(ps))]
    def num(n):
        return str(n) if n>=0 else f"(- {-n})"
    def comb(vals):
        return "(+ 0 "+" ".join(f"(* {num(v)} {m})" for v,m in zip(vals,names))+")"
    q=["(set-option :timeout 3000)","(set-logic QF_LIA)"]
    for m in names:
        q.extend([f"(declare-const {m} Int)",f"(assert (and (<= 0 {m}) (<= {m} 1000000)))"])
    q.append("(assert (>= (+ 0 "+" ".join(names)+") 1))")
    for i,w in enumerate(target["coeffs"]):
        q.append(f'(assert (= {comb(x["coeffs"][i] for x in ps)} {num(w)}))')
    q.append(f'(assert (<= {comb(x["le"] for x in ps)} {num(target["le"])}))')
    q.append("(check-sat)")
    return "\n".join(q)+"\n",names

def find(solver,c):
    q,names=query_for(c)
    status=solver.exec(q)
    if status in {"unsat","unknown"}:
        return status,None,sha(q.encode("ascii"))
    need(status=="sat","unexpected SAT response")
    result=solver.exec(q+"(get-value ("+" ".join(names)+"))\n")
    first,_,part=result.partition("\n")
    need(first=="sat","model query did not return sat")
    token=re.compile(r"\((m\d+)\s+(\d{1,7})\)")
    pairs=token.findall(part)
    need(re.fullmatch(r"\(\s*\)",token.sub("",part)) is not None,"bad model value syntax")
    need(len(pairs)==len(names) and {k for k,_ in pairs}==set(names),"incomplete model")
    m={k:int(v) for k,v in pairs}
    candidate={**c,"schema":linear.SCHEMA,"multipliers":[m[k] for k in names]}
    linear.exact(linear.parse(json_bytes(candidate)))
    return status,candidate,sha(q.encode("ascii"))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("goal", type=Path)
    p.add_argument("--z3-library", type=Path, required=True)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--mutate", action="store_true")
    a=p.parse_args()
    c,raw=read_goal(a.goal)
    solver=Z3(a.z3_library)
    status,cert,q_hash=find(solver,c)
    r={"schema":"commons.proofbridge.smt_witness.v1","goal_sha256":sha(raw),
       "solver":solver.version(),"solver_library_sha256":sha(a.z3_library.read_bytes()),
       "query_sha256":q_hash,"solver_status":status}
    if cert is None:
        r["status"]="no_bounded_witness" if status=="unsat" else "solver_inconclusive"
        print(json.dumps(r,indent=2)); return 2
    lean=a.lean.resolve(strict=True)
    linear.LEAN[:]=[str(lean)]
    verified=linear.checked(json_bytes(cert))
    r.update(status="kernel_checked_conditional",multipliers=cert["multipliers"],
             certificate=cert,verification=verified)
    if a.mutate:
        i=next(i for i,x in enumerate(cert["multipliers"]) if x)
        broken={**cert,"multipliers":cert["multipliers"].copy()}
        broken["multipliers"][i]=0
        try:
            linear.exact(broken)
        except ValueError:
            pass
        else:
            raise ValueError("invalid negative-control design")
        with tempfile.TemporaryDirectory(prefix="commons_smt_reject_") as tmp:
            path=Path(tmp)/"Rejected.lean"
            path.write_bytes(linear.lean_source(broken).encode("utf-8"))
            res=subprocess.run([str(lean),path.name],cwd=tmp,capture_output=True,
                               text=True,timeout=30)
            need(res.returncode!=0 and "omega could not prove the goal" in res.stdout+res.stderr,
                 "expected the mutated coefficient to fail at the actual Lean goal")
            r["negative_control"]={"multipliers":broken["multipliers"],
                                   "lean_exit":res.returncode,"expected_goal_failure":True}
    print(json.dumps(r,indent=2))
    return 0

if __name__=="__main__":
    try:
        sys.exit(main())
    except (ValueError, TypeError, OSError, subprocess.SubprocessError) as e:
        sys.exit(str(e))
