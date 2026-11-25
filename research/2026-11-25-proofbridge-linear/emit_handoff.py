"""Prototype importable handoff; only this existing Commons theorem is registered."""
import hashlib, json, os, subprocess, sys
from pathlib import Path
import linear

SOURCE = {"commit":"c205f5fdfcfd6eda3f345bbe59cc04c9e378e9a0",
          "path":"research/2026-11-25-proofbridge-linear/goldbach-budget.json",
          "sha256":"98e115ecaa9245a6662048c78a15db5929be523f97f9b18f7fd22dc7d0ffff3e"}
THEOREM_ID = "commons.goldbach.integer_budget_187.v1"
THEOREM = "CommonsBudget187.certificate"
PRODUCER = "Budget187"
PINS = ["8872348bfde6b6961e985e8bcfac1db320239e973b84cb79d3b36ec065ae7ee5"]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    base = Path(__file__).resolve().parent
    input_file = base/"goldbach-budget.json"
    linear.require(sha(input_file) == SOURCE["sha256"],"source hash mismatch")
    linear.require(sha(base/"linear.py") in PINS,"checker hash mismatch")
    raw = input_file.read_bytes()
    checked = linear.checked(raw)
    code = linear.lean_source(linear.parse(raw))
    options, body = code.split("theorem addScaled", 1)
    body, _ = ("theorem addScaled" + body).rsplit("#print axioms certificate",1)
    module = options+"namespace CommonsBudget187\n"+body+"end CommonsBudget187\n"
    module += "#print axioms " + THEOREM + "\n"
    out = Path(sys.argv[1]).resolve()
    out.mkdir(exist_ok=False)
    name=out/(PRODUCER+".lean")
    name.write_bytes(module.encode("utf-8"))
    env = os.environ.copy()
    env["LEAN_PATH"] = str(out)
    result = subprocess.run(linear.LEAN+["-o",PRODUCER+".olean",name.name],
                            cwd=out,env=env,capture_output=True,text=True,timeout=30,check=True)
    expected = f"'{THEOREM}' depends on axioms: [{', '.join(checked['axioms'])}]"
    if result.stdout.strip()!=expected:
        raise ValueError("unexpected compiled axioms")
    compiled = out/(PRODUCER+".olean")
    receipt = {"schema":"commons.proofbridge.handoff.v1","status":"kernel_checked",
               "theorem_id":THEOREM_ID,"lean_name":THEOREM,"source":SOURCE,
               "premise_ids":["model-margin","odd-semiprime-cap","odd-center-cap"],
               "verification":checked,"unresolved":["analytic-premises-not-proved-here"],
               "artifact":{"lean_module":PRODUCER,"source_sha256":sha(name),
                           "object_sha256":sha(compiled),"lean_commit":linear.COMMIT}}
    (out/"handoff.json").write_bytes((json.dumps(receipt,indent=2)+"\n").encode("utf-8"))
    print(json.dumps(receipt))
if __name__=="__main__":
    main()
