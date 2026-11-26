"""Exercise pause, resume, tamper refusal, and no-op behavior on exact Git pins."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import linear
import queue_pickup as pickup

HERE=Path(__file__).resolve().parent


def smoke(lean):
    gold=linear.parse((HERE/"goldbach-budget.json").read_bytes())
    r=json.loads((HERE/"smt-rounded.receipt.json").read_bytes())["cases"]["positive"]["exact"]
    wrapped={"schema":"commons.proofbridge.rounded_batch_input.v1",
             "scale":r["verification"]["scale"],"certificate":r["candidate"]}
    bad=copy.deepcopy(gold)
    bad["target"]["le"]=-188
    with tempfile.TemporaryDirectory(prefix="commons_pickup_") as d:
        d=Path(d)
        repo=d/"repo"
        repo.mkdir()
        def git(*args):
            return subprocess.check_output(["git","-C",str(repo),"-c","user.name=Fixture",
                     "-c","user.email=fixture@example.invalid",*args],text=True,timeout=20).strip()
        def checkpoint(msg):
            git("add",".")
            git("commit","-qm",msg)
            return git("rev-parse","HEAD")
        git("init","-q")
        q=repo/"research/proofbridge-incoming/certs.json"
        q.parent.mkdir(parents=True)
        def put(entries):
            q.write_text(json.dumps({"schema":"commons.proofbridge.certificate_records.v1",
                    "records":[{"id":k,"certificate":c} for k,c in entries.items()]}))
        put({"stable":gold,"same-name":gold})
        base=checkpoint("Base")
        put({"stable":gold,"same-name":bad,"new-rounded":wrapped})
        head=checkpoint("Two jobs")
        store=d/"state"
        first=pickup.drive(repo,store,head,lean,budget=1,base=base)
        assert first["status"]=="partial" and first["count"]==2 and first["next_index"]==1
        cursor=(store/"cursor.json").read_bytes()
        cur=json.loads(cursor)
        assert cur["completed"]==base
        p=cur["pending"]
        row=p["receipts"][0]
        file=store/p["stage"]/row["run"]/row["file"]
        data=file.read_bytes()
        file.write_bytes(data+b" ")
        try:
            pickup.drive(repo,store,head,lean,budget=1)
        except ValueError as e:
            assert str(e)=="durable worker receipt changed"
        else:
            raise AssertionError("modified receipt accepted")
        assert (store/"cursor.json").read_bytes()==cursor
        file.write_bytes(data) # Temporary fixture only.
        second=pickup.drive(repo,store,head,lean,budget=1)
        assert second["status"]=="completed" and second["processed"]==2
        completion=json.loads((store/second["checkpoint"]).read_bytes())
        statuses=sorted(x["status"] for x in completion["receipts"])
        assert statuses==["not_verified","verified_now"]
        assert pickup.drive(repo,store,head,lean)["status"]=="no_new_revision"
        (repo/"README.md").write_text("A documentation-only change")
        newer=checkpoint("No proof edit")
        dry=pickup.drive(repo,store,newer,lean,budget=1)
        assert dry["status"]=="completed" and dry["processed"]==0
        return {"schema":"commons.proofbridge.pickup_smoke.v1","first_tick":first,
                "completed_after_resume":second["status"]=="completed","statuses":statuses,
                "tampered_receipt_preserved_cursor":True,"same_revision_noop":True,
                "docs_only_checked_count":dry["processed"],"hosted_trigger_enabled":False}


if __name__=="__main__":
    print(json.dumps(smoke(Path(sys.argv[1]).resolve(strict=True)),indent=2))
