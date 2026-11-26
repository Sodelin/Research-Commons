"""Do not republish merely because a bot-only or unrelated commit changed the SHA."""
import json
from pathlib import Path
import sys

def snapshot(directory):
    def read(name):
        return json.loads((Path(directory)/(name+".json")).read_text())
    m=read("receipt")
    coverage=read("coverage")
    check=read("checks")
    smoke=read("query-smoke")
    for r in (coverage,check,smoke):
        if r["source_commit"]!=m["source_commit"] or r["index_sha256"]!=m["sha256"]:
            raise ValueError("mixed receipt")
    if coverage["status"]!="passed":
        raise ValueError("coverage not passed")
    # Compare status/identity, not check timings, source SHA or reused-body counts.
    dispositions={k:(v["status"],v.get("reason"),v.get("output_sha256") if k in ("lean","smt") else None)
                  for k,v in check["checks"].items()}
    provider=read("provider-observation")
    return (m["sha256"],dispositions,coverage["roots"],coverage["excluded_in_roots"],provider,
            [(x["path"],x["git_blob"]) for x in smoke["checks"]])

if __name__=="__main__":
    try:
        report=json.loads((Path(sys.argv[2])/"receipt.json").read_text())
        healthy=report.get("scan",{}).get("prior_index")=="verified"
        raise SystemExit(0 if healthy and snapshot(sys.argv[1])==snapshot(sys.argv[2]) else 1)
    except (OSError,ValueError,KeyError,TypeError,IndexError):
        raise SystemExit(1)
