"""Stratified preflight on twenty actual Discovery records, with typed Lean replays."""
import collections
import json
from pathlib import Path
import subprocess
import sys
import time

QUOTAS = {"ready_for_checker":2,"recorded_kernel_handoff":1,"needs_statement_review":6,
          "reuse_audit_not_a_batch_job":6,"source_only":5}


def parse_lines(text):
    return [json.loads(line) for line in text.splitlines() if line.strip()]


def pick(rows,n):
    # Prefer distinct source kinds before taking more from an already covered kind.
    bins=collections.defaultdict(collections.deque)
    for r in sorted(rows,key=lambda r:r["id"]):
        bins[r["provenance"]["kind"]].append(r)
    out=[]
    while len(out)<n:
        available=[k for k in sorted(bins) if bins[k]]
        assert available,"not enough records in stratum"
        for k in available:
            if len(out)==n:
                break
            out.append(bins[k].popleft())
    return out


def audit(repo, sources, head, intake, runner, lean, out):
    out.mkdir(exist_ok=False)
    def run(args,max_time=180):
        p=subprocess.run([str(x) for x in args],text=True,capture_output=True,timeout=max_time)
        if p.returncode:
            raise RuntimeError(p.stderr)
        return p.stdout
    tool=[sys.executable,intake,"--repo",repo,"--sources",sources,"--include-queue-at",head]
    rows=parse_lines(run(tool))
    bins=collections.defaultdict(list)
    for r in rows:
        bins[r["intake_status"]].append(r)
    assert len(bins["ready_for_checker"])==2,"frozen audit expects exactly two typed pilot jobs"
    sample=[r for kind,n in QUOTAS.items() for r in pick(bins[kind],n)]
    handoff=next(r for r in sample if r["intake_status"]=="recorded_kernel_handoff")
    prior=json.loads(run([*tool,"--emit-certificate","--id",handoff["id"]]))
    assert sum(r["certificate"]==prior for r in sample if r["intake_status"]=="ready_for_checker")==1
    export=out/"jobs"
    index=json.loads(run([*tool,"--export-ready",export]))
    cmd=[sys.executable,runner]
    manifest=out/"manifest.json"
    import hashlib
    manifest.write_text(run([*cmd,"make",export/"inputs",*[e["file"] for e in index["jobs"]]]))
    pin=hashlib.sha256(manifest.read_bytes()).hexdigest()
    start=time.monotonic()
    run([*cmd,"run",export/"inputs",manifest,pin,out/"check","--lean",lean,
         "--rounded","--discovery-jsonl"])
    build_wall=time.monotonic()-start
    joins=parse_lines(run([*tool,"--export-index",export/"index.json","--checker-results",
                           out/"check/discovery-results.jsonl"]))
    statuses={r["id"]:r["imported_replay"]["result"]["status"]
              for r in joins if "imported_replay" in r}
    assert len(statuses)==2 and set(statuses.values())=={"kernel-checked-conditional"}
    return {"schema":"commons.proofbridge.audit_fit.v1","head":head,"population_status_counts":
            {kind:len(v) for kind,v in sorted(bins.items())},"sample_status_quotas":QUOTAS,
            "sample":[{"id":r["id"],"intake_status":r["intake_status"],
                       "provenance":r["provenance"],
                       **({"replay_status":statuses[r["id"]]} if r["id"] in statuses else {})}
                      for r in sample],"typed_batch_seconds":round(build_wall,2),
            "duplicate_recorded_handoff_matched_existing_typed_job":True,
            "scope":"stratified coverage sample, not a random success-rate estimate; unsupported rows not attempted"}


if __name__=="__main__":
    repo,sources,head,intake,runner,lean,out=sys.argv[1:]
    print(json.dumps(audit(Path(repo),Path(sources),head,Path(intake),Path(runner),Path(lean),Path(out)),indent=2))
