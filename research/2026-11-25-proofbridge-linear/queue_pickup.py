"""Advance one persistent typed ProofBridge queue in bounded, atomic chunks."""
import argparse
import contextlib
import fcntl
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import uuid

import linear
import manifest_runner as runner

HERE = Path(__file__).resolve().parent
SCHEMA = "commons.proofbridge.queue_cursor.v1"
need = linear.require


def intake_tool():
    path=HERE/"theorem-intake.py"
    if not path.is_file():
        path=HERE.parents[1]/"docs/discovery/tools/theorem-intake.py"
    spec=importlib.util.spec_from_file_location("proofbridge_theorem_intake", path)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def json_bytes(obj):
    return (json.dumps(obj,sort_keys=True,indent=2,ensure_ascii=True)+"\n").encode("ascii")


def atomic(path, obj):
    with tempfile.NamedTemporaryFile(mode="wb",dir=path.parent,prefix="staging_",delete=False) as f:
        f.write(json_bytes(obj))
        f.flush()
        os.fsync(f.fileno())
        source=f.name
    os.replace(source,path)
    durable_dir(path.parent)


def durable_dir(path):
    fd=os.open(path,os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def seal(path):
    with path.open("rb") as f:
        contents=f.read()
        os.fsync(f.fileno())
    return linear.sha(contents)


def verify_chunk(run, entries, index, stop, pin):
    refs=[]
    for i in range(index,stop):
        name=f"{i:04}.json"
        file=run/name
        r=json.loads(file.read_bytes())
        expected=entries[i]
        need(r["index"]==i and r["file"]==expected["file"]
             and r["input_sha256"]==expected["sha256"] and r["manifest_sha256"]==pin,
             "worker receipt is outside the staged manifest")
        # A valid arithmetic rejection is terminal for these bytes. Unknown
        # runtime failures and timeouts deliberately stop at the last safe row.
        terminal=(r["status"]=="verified_now" or
                  (r["status"]=="not_verified" and r.get("diagnostic")=="invalid linear combination"))
        if not terminal:
            return refs,r["status"]
        art=r.get("artifact_dir")
        if art is not None:
            need(art==f"module_{i:04}", "artifact outside its row")
            for n,h in r["proof"]["files_sha256"].items():
                need(Path(n).name==n and seal(run/art/n)==h,"artifact hash mismatch")
            durable_dir(run/art)
        refs.append({"index":i,"run":run.name,"file":name,"receipt_sha256":seal(file),"status":r["status"]})
    return refs,None


def drive(repo, store, ref, lean, budget=20, base=None):
    need(1<=budget<=20,"max 20 jobs per wake")
    repo=repo.resolve(strict=True)
    lean=lean.resolve(strict=True)
    store=store.resolve()
    store.mkdir(exist_ok=True)
    with (store/"worker.lock").open("ab") as lock:
        try:
            fcntl.flock(lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return {"status":"another_worker_holds_lock"}
        intake=intake_tool()
        head=intake.queue_revision(repo,ref)
        state_path=store/"cursor.json"
        if state_path.exists():
            state=json.loads(state_path.read_bytes())
            need(state["schema"]==SCHEMA,"unknown cursor schema")
            need(base is None,"--base is allowed only for a new cursor")
        else:
            need(base is not None,"initial cursor requires explicit --base")
            state={"schema":SCHEMA,"completed":intake.queue_revision(repo,base),"pending":None}
            # Initialization selects the caller's baseline; it grants no proofs.
            atomic(state_path,state)
        complete=state["completed"]
        pending=state["pending"]
        if pending is None and complete==head:
            return {"status":"no_new_revision","completed":complete}
        version=subprocess.check_output([str(lean),"--version"],text=True,timeout=10).strip()
        need("commit "+linear.COMMIT+"," in version,"wrong Lean toolchain")
        fingerprint={"lean":version,"lean_binary_sha256":linear.sha(lean.read_bytes()),
                     "driver_sha256":linear.sha(Path(__file__).read_bytes()),
                     "intake_sha256":linear.sha(Path(intake.__file__).read_bytes()),
                     "runner_sha256":linear.sha(Path(runner.__file__).read_bytes()),
                     "checker_sha256":runner.checker_hash(),"rounded_helpers":runner.ROUND_HELPERS}
        runner.rounded_dependencies()
        linear.LEAN[:]=[str(lean)]
        if pending is None:
            rows,delta=intake.queue_delta(repo,complete,head)
            stage=Path(tempfile.mkdtemp(prefix="delta_",dir=store))
            with contextlib.redirect_stdout(io.TextIOWrapper(io.BytesIO(),encoding="ascii")):
                intake.export_ready(rows,stage/"export",delta)
            jobs=json.loads((stage/"export/index.json").read_bytes())["jobs"]
            pending={"head":head,"stage":stage.name,"next_index":0,"receipts":[],
                     "count":len(jobs),"export_index_sha256":seal(stage/"export/index.json"),
                     "fingerprint":fingerprint}
            for j in jobs:
                need(seal(stage/"export/inputs"/j["file"])==j["sha256"],"staged input changed")
            durable_dir(stage/"export/inputs")
            durable_dir(stage/"export")
            if jobs:
                manifest=runner.make(stage/"export/inputs",[j["file"] for j in jobs])
                atomic(stage/"manifest.json",manifest)
                pending["manifest_sha256"]=seal(stage/"manifest.json")
            durable_dir(stage)
            state["pending"]=pending
            atomic(state_path,state)
        need(pending["fingerprint"]==fingerprint,"pending verifier identity changed")
        stage=store/pending["stage"]
        need(seal(stage/"export/index.json")==pending["export_index_sha256"], "staged export index changed")
        idx=pending["next_index"]
        # Recheck all durable rows referenced by the journal before further work.
        need(idx==len(pending["receipts"])<=pending["count"],"bad pending cursor")
        for i,r in enumerate(pending["receipts"]):
            need(r["index"]==i and r["file"]==f"{i:04}.json" and Path(r["run"]).name==r["run"]
                 and seal(stage/r["run"]/r["file"])==r["receipt_sha256"], "durable worker receipt changed")
            prior=json.loads((stage/r["run"]/r["file"]).read_bytes())
            art=prior.get("artifact_dir")
            if art is not None:
                for name,digest in prior["proof"]["files_sha256"].items():
                    need(Path(name).name==name and seal(stage/r["run"]/art/name)==digest,
                         "retained artifact hash mismatch")
        blocker=None
        if pending["count"]>idx:
            manifest=stage/"manifest.json"
            pin=pending["manifest_sha256"]
            entries=runner.load(manifest,pin)
            need(len(entries)==pending["count"],"pending job count mismatch")
            run_name=uuid.uuid4().hex
            run=stage/("run_"+run_name)
            with contextlib.redirect_stdout(io.StringIO()) as output:
                runner.run(stage/"export/inputs",manifest,pin,run,idx,budget,120,30,True,lean)
            stop=json.loads(output.getvalue().splitlines()[-1])["next_index"]
            refs,blocker=verify_chunk(run,entries,idx,stop,pin)
            durable_dir(run)
            durable_dir(stage)
            pending["receipts"].extend(refs)
            pending["next_index"]+=len(refs)
            atomic(state_path,state)
        if pending["next_index"]==pending["count"]:
            final={"schema":"commons.proofbridge.queue_completed.v1","previous":complete,**pending}
            atomic(stage/"completed.json",final)
            state={"schema":SCHEMA,"completed":pending["head"],"pending":None,
                   "last_completion":f"{stage.name}/completed.json"}
            atomic(state_path,state)
            return {"status":"completed","head":pending["head"],"processed":pending["count"],
                    "checkpoint":state["last_completion"]}
        return {"status":"blocked" if blocker else "partial","head":pending["head"],
                "next_index":pending["next_index"],"count":pending["count"],"blocker":blocker}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("repo",type=Path)
    p.add_argument("state",type=Path)
    p.add_argument("head")
    p.add_argument("lean",type=Path)
    p.add_argument("--base")
    p.add_argument("--jobs",type=int,default=20)
    a=p.parse_args()
    print(json.dumps(drive(a.repo,a.state,a.head,a.lean,a.jobs,a.base),indent=2))


if __name__=="__main__":
    try:
        main()
    except (KeyError,OSError,ValueError,subprocess.SubprocessError) as e:
        sys.exit(str(e))
