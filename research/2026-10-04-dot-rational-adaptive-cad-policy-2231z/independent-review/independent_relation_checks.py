#!/usr/bin/env python3
"""Independent exact relation/CAD-export checks; no source-census replay."""
import ast, hashlib, json, operator, sys
from pathlib import Path
import z3
P=Path(sys.argv[1])
OUT=Path(sys.argv[2]) if len(sys.argv)>2 else Path("INDEPENDENT-RELATION-CONTROLS.json")
env={s:z3.Real(s) for s in ("h0_0","h0_1","h0_2","a0_0")}
def arithmetic(n):
    if isinstance(n,ast.Expression): return arithmetic(n.body)
    if isinstance(n,ast.Constant) and type(n.value) is int:return z3.RealVal(n.value),z3.BoolVal(True)
    if isinstance(n,ast.Name) and n.id in env:return env[n.id],z3.BoolVal(True)
    if isinstance(n,ast.UnaryOp) and isinstance(n.op,(ast.USub,ast.UAdd)):
        v,d=arithmetic(n.operand);return (-v if isinstance(n.op,ast.USub) else v),d
    if isinstance(n,ast.BinOp):
        a,da=arithmetic(n.left);b,db=arithmetic(n.right);d=z3.And(da,db)
        if isinstance(n.op,ast.Add):return a+b,d
        if isinstance(n.op,ast.Sub):return a-b,d
        if isinstance(n.op,ast.Mult):return a*b,d
        if isinstance(n.op,ast.Div):return a/b,z3.And(d,b!=0)
        if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=0:
            return (z3.RealVal(1) if n.right.value==0 else a**n.right.value),d
    raise ValueError("Unexpected expression "+ast.dump(n))
cmp={"eq":operator.eq,"ne":operator.ne,"lt":operator.lt,"le":operator.le,"gt":operator.gt,"ge":operator.ge}
def legacy(n):
    if type(n) is bool:return z3.BoolVal(n),z3.BoolVal(True)
    op=n["op"]
    if op in ("and","or"):
        parts=[legacy(x) for x in n["args"]]
        return (z3.And if op=="and" else z3.Or)(*[v for v,d in parts]),z3.And(*[d for v,d in parts])
    if op=="not":
        v,d=legacy(n["arg"]);return z3.Not(v),d
    a,da=arithmetic(ast.parse(n["left"],mode="eval"));b,db=arithmetic(ast.parse(n["right"],mode="eval"))
    return cmp[op](a,b),z3.And(da,db)
def value(n):
    k=n["kind"]
    if k=="rational":return arithmetic(ast.parse(n["value"],mode="eval"))
    if k=="observation":return env[n["name"]],z3.BoolVal(True)
    if k in ("add","multiply"):
        parts=[value(x) for x in n["args"]];v=z3.RealVal(0 if k=="add" else 1)
        for a,d in parts:v=v+a if k=="add" else v*a
        return v,z3.And(*[d for a,d in parts])
    if k=="power":
        a,d=value(n["base"]);e=n["exponent"];assert type(e) is int
        return (z3.RealVal(1) if e==0 else a**e),z3.And(d,a!=0) if e<0 else d
    if k=="divide":
        a,da=value(n["numerator"]);b,db=value(n["denominator"]);return a/b,z3.And(da,db,b!=0)
    raise ValueError("Unexpected CAD value kind "+k)
def cad(n):
    k=n["kind"]
    if k=="boolean":return z3.BoolVal(n["value"]),z3.BoolVal(True)
    if k in ("and","or"):
        ps=[cad(x) for x in n["args"]]
        return (z3.And if k=="and" else z3.Or)(*[a for a,d in ps]),z3.And(*[d for a,d in ps])
    if k=="not":
        a,d=cad(n["arg"]);return z3.Not(a),d
    a,da=value(n["left"]);b,db=value(n["right"]);return cmp[n["op"]](a,b),z3.And(da,db)
checks=[]
def unsat(name,query):
    s=z3.SolverFor("QF_NRA");s.set(timeout=10000);s.add(query);ans=s.check()
    assert ans==z3.unsat,(name,str(ans),s.model() if ans==z3.sat else s.reason_unknown())
    checks.append({"name":name,"result":"unsat","smt2":s.to_smt2()})
r=json.loads((P/"ACTUAL-FULL-SUPPORT-TERMINAL-FIBRE.json").read_text())
c=json.loads((P/"EXPORTED-ACTUAL-TERMINAL-SELECTOR.json").read_text())
x,y,z,w=[env[s] for s in ("h0_0","h0_1","h0_2","a0_0")]
third=z3.RealVal("1/3")
expected=[z3.And(x>0,x<third,y==1-2*x,z==x),
          z3.And(x>third,x<1,y==(1-x)/2,z==(1-x)/2),
          z3.And(x>0,x<third,y==x,z==1-2*x)]
H=z3.Or(*expected)
hd,hdef=legacy(r["history_domain"]);wr,wdef=legacy(r["winning_relation"])
unsat("history_domain_equals_three_actual_segments",z3.Or(z3.Not(hdef),z3.Xor(hd,H)))
unsat("raw_FM_relation_iff_H_and_strict_full_support",z3.Or(z3.Not(wdef),z3.Xor(wr,z3.And(H,w>0,w<1))))
parts=[cad(cel["guard"]) for cel in c["Export"]["cells"]]
assert len(parts)==3
unsat("exported_CAD_guard_union_equals_H",z3.Or(z3.Not(z3.And(*[d for a,d in parts])),z3.Xor(z3.Or(*[a for a,d in parts]),H)))
for i,((g,d),e,cell) in enumerate(zip(parts,expected,c["Export"]["cells"])):
    unsat("CAD_cell_"+str(i)+"_geometry",z3.Or(z3.Not(d),z3.Xor(g,e)))
    aa=[value(t) for t in cell["weights"]];assert len(aa)==2
    pref=(x*x+1)/(x*x+2)
    unsat("CAD_cell_"+str(i)+"_returned_history_rational_action",z3.Or(z3.Not(aa[0][1]),z3.Not(aa[1][1]),aa[0][0]!=pref,aa[1][0]!=1-pref))
    unsat("CAD_cell_"+str(i)+"_full_raw_winning_relation",z3.And(g,z3.Not(z3.substitute(wr,(w,aa[0][0])))))
    for j in range(i):unsat("first_eligible_disjoint_"+str(j)+"_"+str(i),z3.And(g,parts[j][0]))
unsat("adaptive_sector_fraction_strictly_inside_for_all_real_history",z3.Not(z3.And(x*x+2>0,(x*x+1)/(x*x+2)>0,(x*x+1)/(x*x+2)<1)))
# Explicit negative-power domains cannot disappear inside a zero product or a zeroth power.
for label,tree in [
 ("zero_product_written_reciprocal",{"kind":"multiply","args":[{"kind":"rational","value":"0"},{"kind":"power","base":{"kind":"observation","name":"h0_0"},"exponent":-1}]}),
 ("zeroth_power_written_reciprocal",{"kind":"power","base":{"kind":"power","base":{"kind":"observation","name":"h0_0"},"exponent":-1},"exponent":0})]:
 a,d=value(tree);unsat(label,z3.And(x==0,d))
stored=json.loads((P/"ACTUAL-AFFINE-WINNING-RELATION-EQUIVALENCE.json").read_text())
assert stored["source_relation_sha256"]==hashlib.sha256((P/"ACTUAL-FULL-SUPPORT-TERMINAL-FIBRE.json").read_bytes()).hexdigest()
solver=z3.Solver();solver.from_string(stored["query_smt2"]);assert solver.check()==z3.unsat
out={"status":"PASS_INDEPENDENT_ADAPTIVE_CAD_RELATION_AND_EXPORT_CONTROLS","checks":checks,"stored_global_equivalence_replayed":"unsat",
     "source_relation_sha256":stored["source_relation_sha256"],"export_sha256":hashlib.sha256((P/"EXPORTED-ACTUAL-TERMINAL-SELECTOR.json").read_bytes()).hexdigest(),
     "trust":"Exact QF_NRA checks with independently transcribed AST readers and hand-derived source-history segments; SAME_BACKEND, no new census."}
OUT.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"status":out["status"],"global_checks":len(checks),"stored_equivalence":"unsat"}))

