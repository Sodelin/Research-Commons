"""Federated read-only search across typed Commons rows and source-only corpora."""
import argparse, hashlib, json, re, sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent

def terms(value):
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    return set(re.findall(r"[a-z0-9]+", value.lower()))

def rows(root, generated_override=None):
    primary = json.loads((root / "catalog.json").read_text())
    providers = json.loads((root / "external" / "providers.json").read_text())
    for group in ("problems","theorems","artifacts"):
        for row in primary[group]:
            yield "commons_typed", {"collection":group,**row}
    seen_shards=set()
    for _,pr in sorted(providers.items()):
        files=pr.get("shards",[])
        if type(files) is not list: raise ValueError("invalid provider shards")
        layer=("external_manifest_entry" if pr["evidence"]=="provider_manifest_not_locally_replayed" else "external_source_only")
        for name in files:
            if not re.fullmatch(r"[a-zA-Z0-9_.-]+\.jsonl",name) or name in seen_shards:
                raise ValueError("invalid or duplicate provider shard")
            seen_shards.add(name)
            body=(root/"external"/name).read_bytes()
            if "rows_sha256" in pr and (len(files)!=1 or hashlib.sha256(body).hexdigest()!=pr["rows_sha256"]):
                raise ValueError("external snapshot hash mismatch")
            for line in body.decode().splitlines():
                yield layer, {**{k:v for k,v in pr.items() if k!="shards"},**json.loads(line)}
    generated=generated_override or (root.parent/"generated-source-index")
    manifest_path=generated/"receipt.json"
    if manifest_path.is_file():
        manifest=json.loads(manifest_path.read_text())
        for row in generated_rows(generated,manifest):
            yield "commons_git_source",row
        checks=generated/"checks.json"
        if checks.is_file():
            report=json.loads(checks.read_text())
            if report.get("index_sha256")!=manifest.get("sha256") or report.get("source_commit")!=manifest.get("source_commit"):
                raise ValueError("check receipt does not match generated index")
            yield "commons_worker_receipt",report
        coverage=generated/"coverage.json"
        if coverage.is_file():
            r=json.loads(coverage.read_text())
            if (r.get("schema")!="commons.discovery.coverage-reconciliation.v1" or
                r.get("status")!="passed" or r.get("index_sha256")!=manifest.get("sha256") or
                r.get("source_commit")!=manifest.get("source_commit")):
                raise ValueError("coverage receipt does not match generated index")
            yield "commons_coverage_receipt",r
        provider_receipt=generated/"provider-observation.json"
        if provider_receipt.is_file():
            report=json.loads(provider_receipt.read_text())
            if report.get("schema")!="commons.discovery.provider-observation.v1":
                raise ValueError("invalid live metadata receipt")
            for ident,x in sorted(report["providers"].items()):
                if x["status"]!="passed":
                    yield "external_refresh_status",{"provider_id":ident,**x}
                    continue
                rt=x["receipt"]
                # Same canonical row encoding as the independently verified tree adapter.
                payload="".join(json.dumps(r,ensure_ascii=True,sort_keys=True,separators=(",",":"))+"\n" for r in x["rows"]).encode()
                if (hashlib.sha256(payload).hexdigest()!=rt.get("rows_sha256") or
                    rt.get("provider")!=ident or rt.get("evidence")!="source_path_only" or
                    rt.get("count")!=len(x["rows"])):
                    raise ValueError("live provider rows do not match source-only receipt")
                for r in x["rows"]:
                    yield "external_live_source",{"provider_id":ident,"repo":rt["repo"],"commit":rt["commit"],
                        "evidence":"source_path_only",**r}
    for p in sorted((root/"legacy").glob("*.jsonl")):
        for line in p.read_text().splitlines():
            yield "commons_legacy_metadata", json.loads(line)

def generated_rows(root,manifest):
    if manifest.get("schema")=="commons.discovery.git-source-index.v1":
        entries=[{"path":"index.jsonl","sha256":manifest["sha256"],"rows":manifest["rows"]}]
    elif manifest.get("schema")=="commons.discovery.git-source-index.v2":
        entries=manifest["shards"]
        if [x["path"] for x in entries]!=[f"shards/{i:02x}.jsonl" for i in range(256)]:
            raise ValueError("unexpected shard layout")
    else:
        raise ValueError("unknown generated index schema")
    checksum=hashlib.sha256()
    total=0
    for entry in entries:
        data=(root/entry["path"]).read_bytes()
        if hashlib.sha256(data).hexdigest()!=entry["sha256"]:
            raise ValueError("bad generated shard digest")
        checksum.update(data)
        lines=data.decode().splitlines()
        if len(lines)!=entry["rows"]:
            raise ValueError("bad generated shard count")
        total+=len(lines)
        for line in lines:
            yield {**json.loads(line),"source_commit":manifest["source_commit"]}
    if total!=manifest["rows"] or checksum.hexdigest()!=manifest["sha256"]:
        raise ValueError("bad generated index aggregate")

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("query")
    p.add_argument("--root",type=Path,default=BASE)
    p.add_argument("--generated-index",type=Path,help="staged index directory for worker smoke test")
    p.add_argument("--limit",type=int,default=20)
    p.add_argument("--layer", choices=["commons_typed","external_source_only","external_manifest_entry","commons_legacy_metadata","commons_git_source","commons_worker_receipt","external_live_source","external_refresh_status","commons_coverage_receipt"])
    args = p.parse_args()
    if not 1 <= args.limit <= 1000 or not terms(args.query):
        p.error("query must contain tokens; limit must be between 1 and 1000")
    found=[]
    for layer, row in rows(args.root,args.generated_index):
        if args.layer and args.layer != layer:
            continue
        hay = json.dumps(row,ensure_ascii=False)
        if terms(args.query) <= terms(hay):
            found.append({"layer":layer,**row})
    print(json.dumps({"matches":len(found),"results":found[:args.limit]},ensure_ascii=False,indent=2))

if __name__ == "__main__":
    main()
