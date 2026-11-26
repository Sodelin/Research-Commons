"""Check queue-only changes from pinned commits through a real cloud Lean replay."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import linear

HERE=Path(__file__).resolve().parent


def test(lean):
    intake=HERE/"theorem-intake.py"
    if not intake.is_file():
        intake=HERE.parents[1]/"docs/discovery/tools/theorem-intake.py"
    gold=linear.parse((HERE/"goldbach-budget.json").read_bytes())
    record=json.loads((HERE/"smt-rounded.receipt.json").read_bytes())["cases"]["positive"]["exact"]
    wrap={"schema":"commons.proofbridge.rounded_batch_input.v1",
          "scale":record["verification"]["scale"],"certificate":record["candidate"]}
    with tempfile.TemporaryDirectory(prefix="pb_delta_") as tmp:
        d=Path(tmp)
        root=d/"repo"
        root.mkdir()
        def run(a, status=0):
            p=subprocess.run(a,text=True,capture_output=True,timeout=60)
            assert p.returncode==status,(a,p.stderr)
            return p.stdout
        def git(*args):
            return run(["git","-C",str(root),"-c","user.name=Replay fixture",
                        "-c","user.email=replay@example.invalid",*args]).strip()
        def checkpoint(label):
            git("add",".")
            git("commit","-qm",label)
            return git("rev-parse","HEAD")
        def export(base,head,out,status=0):
            call=[sys.executable,str(intake),"--repo",str(root),
                  "--include-queue-at",head,"--queue-delta-since",base,"--export-ready",str(out)]
            return json.loads(run(call,status)) if status==0 else run(call,status)
        git("init","-q")
        queue=root/"research/proofbridge-incoming/fixtures.json"
        queue.parent.mkdir(parents=True)
        def write(entries, indent=None):
            queue.write_text(json.dumps({"schema":"commons.proofbridge.certificate_records.v1",
                                         "records":[{"id":k,"certificate":v} for k,v in entries.items()]},
                                         indent=indent))
        records={"unchanged":gold,"amend":gold,"retired":gold}
        write(records)
        base=checkpoint("before")
        (root/"README.md").write_text("Unrelated change")
        doc=checkpoint("documentation only")
        idx=export(base,doc,d/"noop")
        assert not idx["jobs"] and idx["queue_delta"]["unchanged_count"]==3
        write(records,indent=2)
        reformatted=checkpoint("JSON formatting only")
        assert not export(doc,reformatted,d/"format")["jobs"]
        altered=copy.deepcopy(gold)
        altered["target"]["le"]=-188
        write({"unchanged":gold,"amend":altered,"rounded":wrap})
        head=checkpoint("one new, one revised, one retired")
        staged=d/"new"
        k="certificate_records:"
        idx=export(reformatted,head,staged)
        delta=idx["queue_delta"]
        assert delta["added"]==[k+"rounded"] and delta["changed"]==[k+"amend"]
        assert delta["removed"]==[k+"retired"] and delta["unchanged_count"]==1
        export(head,base,d/"wrong-base",2)
        assert not (d/"wrong-base").exists()
        files=[j["file"] for j in idx["jobs"]]
        runner=[sys.executable,str(HERE/"manifest_runner.py")]
        args=[*runner,"make",str(staged/"inputs"),*files]
        manifest=d/"manifest.json"
        manifest.write_text(run(args))
        stdout=run([*runner,"run",str(staged/"inputs"),str(manifest),
                     linear.sha(manifest.read_bytes()),str(d/"run"),"--rounded","--lean",str(lean),
                     "--discovery-jsonl"],1)
        file_ids={j["file"]:j["id"] for j in idx["jobs"]}
        outcome={file_ids[r["file"]]:r["status"] for r in map(json.loads,stdout.splitlines()[:-1])}
        assert outcome=={k+"rounded":"verified_now",k+"amend":"not_verified"}
        return {"schema":"commons.proofbridge.queue_delta_smoke.v1","fixture_delta":delta,
                "outcome":outcome,"unrelated_and_format_only_exported_zero":True,
                "reverse_history_rejected_before_export":True,"automatic_wake_wired":False}


if __name__=="__main__":
    print(json.dumps(test(Path(sys.argv[1]).resolve(strict=True)),indent=2))
