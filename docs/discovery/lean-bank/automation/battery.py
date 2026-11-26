"""Run bounded repository-owned checks and leave explicit evidence states."""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, tempfile
from pathlib import Path
from index_sources import git

SCHEMA = "commons.discovery.check-battery.v1"
BANK = "docs/discovery/lean-bank"
def test(cmd, cwd):
    try:
        p=subprocess.run(cmd,cwd=cwd,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT,timeout=80,check=False,
                         env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1"})
        return {"status":"passed" if p.returncode==0 else "failed","exit_code":p.returncode,
                "output_sha256":hashlib.sha256(p.stdout).hexdigest(),
                "output_tail":p.stdout.decode("utf-8","replace")[-6500:]}
    except (OSError,subprocess.TimeoutExpired) as e:
        return {"status":"blocked","reason":type(e).__name__}

def lean_stage(root,bank,lean):
    if not lean: return {"status":"not_run","reason":"compatible pinned Lean is not installed on this runner"}
    lock=json.loads((bank/"source-pull.lock.json").read_text())
    with tempfile.TemporaryDirectory() as tmp:
        stage=Path(tmp)
        for row in lock["sources"]:
            # An explicit same-repository whitelist, not directions embedded in a proof.
            if row["repo"]!="Sodelin/Research-Commons" or not re.fullmatch(r"[a-f0-9]{40}",row["ref"]) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*\.lean",row["stage"]):
                return {"status":"failed","reason":"invalid pinned same-repository source lock"}
            path=Path(row["path"])
            if path.is_absolute() or ".." in path.parts or not str(path).startswith("research/") or path.suffix!=".lean":
                return {"status":"failed","reason":"invalid source path"}
            try:
                body=git(root,"show",row["ref"]+":"+str(path))
            except subprocess.CalledProcessError:
                return {"status":"not_run","reason":"a pinned Git ancestor is not materialized"}
            (stage/row["stage"]).write_bytes(body)
        shutil.copyfile(bank/"CheckBank.lean",stage/"CheckBank.lean")
        # Copy the runner and its lock to avoid modifying checked-out source.
        job=stage/"job"; job.mkdir()
        for name in ("check-source-pull.py","source-pull.lock.json"):
            shutil.copyfile(bank/name,job/name)
        return test([sys.executable,str(job/"check-source-pull.py"),str(stage),lean],job)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,default=Path.cwd())
    p.add_argument("--index",type=Path,required=True)
    p.add_argument("--lean",type=str,default=shutil.which("lean"))
    args=p.parse_args()
    root=args.root.resolve(); ix=args.index.resolve(); bank=root/BANK
    manifest=json.loads((ix/"receipt.json").read_text())
    h=manifest["sha256"]
    sys.path.insert(0,str(bank/"tools"))
    from importlib import import_module
    reader=import_module("search-bank")
    if sum(1 for _ in reader.generated_rows(ix,manifest)) != manifest["rows"]:
        raise ValueError("index bytes do not match index receipt")
    versions={"source_commit":manifest["source_commit"],"index_sha256":h}
    steps={
      "source_index":{"status":"passed","scope":"inventory and Git provenance, not proof"},
      "catalog_contract":test([sys.executable,str(bank/"tools/catalog.py"),str(bank/"catalog.json"),"validate"],root),
      "catalog_tests":test([sys.executable,"-m","unittest","-v"],bank/"tools"),
      "lean":lean_stage(root,bank,args.lean),
      "smt":{"status":"not_run","reason":"no registered SMT proof job for these sources; solver status is not a Lean proof"}
    }
    steps["lean"]["scope"]="the explicit lock-listed two-consumer regression, never arbitrary newly committed Lean code"
    value={"schema":SCHEMA,**versions,"checks":steps}
    (ix/"checks.json").write_text(json.dumps(value,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    print(json.dumps({k:v["status"] for k,v in steps.items()}))
if __name__=="__main__": main()
