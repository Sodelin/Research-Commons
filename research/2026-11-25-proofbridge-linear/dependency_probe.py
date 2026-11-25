"""Transitive Lean dependency negative control for receipt reuse."""
import argparse, hashlib, json, os, subprocess
from pathlib import Path
import tempfile

PIN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
SOURCES = {
    "Alias": "import Base\nabbrev retainedBound : Nat := sourceBound\n",
    "Consumer": "import Alias\ntheorem usesBound : retainedBound = 187 := rfl\n#print axioms usesBound\n",
}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check(lean,root,bound):
    root.mkdir()
    src={**SOURCES,"Base":f"def sourceBound : Nat := {bound}\n"}
    env={**os.environ,"LEAN_PATH":str(root)}
    res={}
    for mod in ("Base","Alias","Consumer"):
        name=mod+".lean"
        path=root/name
        path.write_bytes(src[mod].encode())
        p=subprocess.run([str(lean),"-o",mod+".olean",name],
                         cwd=root,env=env,capture_output=True,text=True,timeout=30)
        diagnostic=p.stdout+p.stderr
        res[mod]={"source_sha256":sha(path),"exit":p.returncode}
        if p.returncode==0:
            res[mod]["object_sha256"]=sha(root/(mod+".olean"))
        elif mod!="Consumer" or bound!=186 or "Type mismatch" not in diagnostic:
            raise ValueError(diagnostic)
        elif "rfl" not in diagnostic:
            raise ValueError(diagnostic)
        if mod=="Consumer" and bound==187:
            if p.returncode!=0 or "'usesBound' does not depend on any axioms" not in diagnostic:
                raise ValueError(diagnostic)
            res[mod]["axioms"]=[]
    return res

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean",required=True,type=Path)
    a=ap.parse_args()
    lean=a.lean.resolve(strict=True)
    version=subprocess.check_output([str(lean),"--version"],text=True,timeout=10).strip()
    if PIN not in version:
        raise ValueError("wrong Lean compiler commit")
    with tempfile.TemporaryDirectory(prefix="proofbridge_deps_") as d:
        prior=check(lean,Path(d)/"prior",187)
        changed=check(lean,Path(d)/"changed",186)
    if prior["Consumer"]["exit"]!=0 or changed["Consumer"]["exit"]==0:
        raise ValueError("missing expected rejection")
    for mod in SOURCES:
        if prior[mod]["source_sha256"]!=changed[mod]["source_sha256"]:
            raise ValueError("an unchanged source changed")
    if prior["Base"]["source_sha256"]==changed["Base"]["source_sha256"]:
        raise ValueError("the source dependency did not actually change")
    print(json.dumps({"schema":"commons.proofbridge.dependency_probe.v1",
                      "lean":version,"prior":prior,"changed":changed,
                      "result":"transitive_change_invalidates_unchanged_consumer"},indent=2))

if __name__=="__main__":
    main()
