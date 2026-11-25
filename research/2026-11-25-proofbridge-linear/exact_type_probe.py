"""Distinguish downstream reuse from the exact type of its supplying theorem."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

import linear

ROOT = Path(__file__).resolve().parent
SOURCE_SHA = "98e115ecaa9245a6662048c78a15db5929be523f97f9b18f7fd22dc7d0ffff3e"
GENERATOR_SHA = "8872348bfde6b6961e985e8bcfac1db320239e973b84cb79d3b36ec065ae7ee5"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", type=Path, required=True)
    a=p.parse_args()
    lean=a.lean.resolve(strict=True)
    version=subprocess.check_output([str(lean),"--version"],text=True,timeout=10).strip()
    if linear.COMMIT not in version:
        raise ValueError("wrong Lean compiler commit")
    src=ROOT/"goldbach-budget.json"
    if sha(src)!=SOURCE_SHA or sha(ROOT/"linear.py")!=GENERATOR_SHA:
        raise ValueError("wrong pinned source or generator")
    base=linear.parse(src.read_bytes())
    cases=[]
    for name in ["exact","weaker_conclusion","stronger_premise"]:
        c=copy.deepcopy(base)
        if name=="weaker_conclusion":
            c["target"]["le"]=-186
        elif name=="stronger_premise":
            c["premises"][0]["le"]=-331
        linear.exact(c)
        with tempfile.TemporaryDirectory(prefix="proofbridge_type_") as raw:
            d=Path(raw)
            code=linear.lean_source(c)
            opts, body=code.split("theorem addScaled",1)
            body=("theorem addScaled"+body).rsplit("#print axioms certificate",1)[0]
            provider=d/"Budget187.lean"
            provider.write_text(opts+"namespace CommonsBudget187\n"+body+
                                "end CommonsBudget187\n",encoding="utf-8")
            consumer=d/"ExactBudgetType.lean"
            shutil.copyfile(ROOT/consumer.name,consumer)
            env=os.environ.copy()
            env["LEAN_PATH"]=str(d)
            subprocess.run([str(lean),"-o","Budget187.olean",provider.name],cwd=d,
                           env=env,check=True,timeout=30,capture_output=True,text=True)
            res=subprocess.run([str(lean),consumer.name],cwd=d,env=env,
                               timeout=30,capture_output=True,text=True)
            logs=res.stdout+res.stderr
            if name=="exact":
                if res.returncode!=0 or "'exactBudgetType' depends on axioms: [propext, Quot.sound]" not in logs:
                    raise ValueError(logs)
            elif res.returncode==0 or "type mismatch" not in logs.lower():
                raise ValueError("did not reject alternate provider specifically on type: "+logs)
            cases.append({"id":name,"provider":"compiled","consumer_exit":res.returncode,
                          "provider_source_sha256":sha(provider),
                          "consumer_source_sha256":sha(consumer),
                          "result":"exact_type_checked" if name=="exact" else "type_mismatch_rejected"})
    print(json.dumps({"schema":"commons.proofbridge.exact_type_probe.v1","lean":version,
                      "source_sha256":SOURCE_SHA,"generator_sha256":GENERATOR_SHA,"cases":cases},
                     indent=2))
if __name__=="__main__":
    main()
