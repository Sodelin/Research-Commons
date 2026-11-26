"""Find a bounded integer witness and scale in Z3, then check it in Lean."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

import linear
import rounded_witness
import smt_witness

SCHEMA = "commons.proofbridge.smt_rounded.v1"
CAP = 1_000_000


def query_for(goal, max_scale):
    linear.require(type(max_scale) is int and 1 <= max_scale <= 1000,"bad scale bound")
    ps, target = goal["premises"], goal["target"]
    names = [f"m{i}" for i in range(len(ps))]
    s = linear.sint
    def combo(vals):
        return "(+ 0 " + " ".join(f"(* {s(v)} {m})" for v,m in zip(vals,names)) + ")"
    q = ["(set-option :timeout 3000)","(set-logic QF_LIA)", "(declare-const g Int)",
         f"(assert (and (<= 1 g) (<= g {max_scale})))"]
    for name in names:
        q += [f"(declare-const {name} Int)",f"(assert (and (<= 0 {name}) (<= {name} {CAP})))"]
    q.append("(assert (>= (+ 0 "+" ".join(names)+") 1))")
    for i, coef in enumerate(target["coeffs"]):
        expr = f"(* {s(coef)} g)"
        q += [f'(assert (= {combo(p["coeffs"][i] for p in ps)} {expr}))',
              f'(assert (and (<= {s(-CAP)} {expr}) (<= {expr} {CAP})))']
    rhs = f'(- (* {s(target["le"]+1)} g) 1)'
    q += [f'(assert (<= {combo(p["le"] for p in ps)} {rhs}))',
          f'(assert (and (<= {s(-CAP)} {rhs}) (<= {rhs} {CAP})))',"(check-sat)"]
    return "\n".join(q)+"\n", [*names,"g"]


def witness(solver, goal, max_scale):
    q, names = query_for(goal,max_scale)
    tag = linear.sha(q.encode("ascii"))
    first = solver.exec(q)
    if first in {"unsat","unknown"}:
        return first, None, tag
    linear.require(first == "sat", "unexpected solver status")
    got = solver.exec(q+"(get-value ("+" ".join(names)+"))\n")
    status, _, model = got.partition("\n")
    if status == "unknown":
        return status, None, tag
    linear.require(status == "sat", "witness query did not return sat")
    token = re.compile(r"\((g|m[0-9]+)\s+(\d{1,7})\)")
    rows = token.findall(model)
    linear.require(len(rows) == len(names) and set(k for k,_ in rows) == set(names)
                   and re.fullmatch(r"\(\s*\)",token.sub("",model)), "bad witness response")
    coeffs = {k:int(v) for k,v in rows}
    scale = coeffs["g"]
    linear.require(1 <= scale <= max_scale, "solver scale outside query bounds")
    candidate = {**goal,"schema":linear.SCHEMA,"multipliers":[coeffs[m] for m in names[:-1]]}
    return status, (scale,candidate),tag


def run(goal_path, pin, max_scale, library, lean, out):
    goal, raw = smt_witness.read_goal(goal_path)
    linear.require(linear.sha(raw) == pin, "source goal hash mismatch")
    solver = smt_witness.Z3(library)
    status, found, query = witness(solver,goal,max_scale)
    record = {"schema":SCHEMA,"goal_sha256":pin,"max_scale":max_scale,
              "query_sha256":query,"solver":solver.version(),
              "solver_library_sha256":linear.sha(library.read_bytes()),"solver_status":status}
    if found is None:
        record["status"] = "no_bounded_witness" if status == "unsat" else "solver_inconclusive"
        return record
    scale, candidate = found
    body = smt_witness.json_bytes(candidate)
    result = rounded_witness.checked(body,linear.sha(body),scale,lean,out)
    record.update(status="kernel_checked_conditional",candidate=candidate,verification=result)
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("goal",type=Path)
    p.add_argument("goal_sha256")
    p.add_argument("out",type=Path)
    p.add_argument("--z3-library",type=Path,required=True)
    p.add_argument("--lean",type=Path,required=True)
    p.add_argument("--max-scale",type=int,default=8)
    a = p.parse_args()
    r = run(a.goal,a.goal_sha256,a.max_scale,a.z3_library,a.lean,a.out)
    print(json.dumps(r,indent=2))
    return 0 if r["status"] == "kernel_checked_conditional" else 2


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError,ValueError,TypeError,subprocess.SubprocessError) as exc:
        sys.exit(str(exc))
