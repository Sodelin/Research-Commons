"""Federated read-only search across typed Commons rows and source-only corpora."""
import argparse, json, re, sys
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent

def terms(value):
    value = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    return set(re.findall(r"[a-z0-9]+", value.lower()))

def rows(root):
    primary = json.loads((root / "catalog.json").read_text())
    providers = json.loads((root / "external" / "providers.json").read_text())
    for group in ("problems","theorems","artifacts"):
        for row in primary[group]:
            yield "commons_typed", {"collection":group,**row}
    for p in sorted((root/"external").glob("*.jsonl")):
        for line in p.read_text().splitlines():
            rec = json.loads(line)
            if p.name.startswith("formal-conjectures-"):
                prov = providers["formal_conjectures"]
                yield "external_source_only", {**prov,**rec}
            elif p.name == "openai-math-index.jsonl":
                prov = providers["openai_math"]
                yield "external_manifest_entry", {**prov,**rec}
            else:
                sys.exit(f"unknown external shard {p.name}")
    generated=root.parent/"generated-source-index"
    index=generated/"index.jsonl"
    if index.is_file():
        import hashlib
        manifest=json.loads((generated/"receipt.json").read_text())
        data=index.read_bytes()
        if manifest.get("schema")!="commons.discovery.git-source-index.v1" or manifest.get("sha256")!=hashlib.sha256(data).hexdigest():
            raise ValueError("invalid generated index receipt")
        for line in data.decode().splitlines():
            yield "commons_git_source",json.loads(line)
        checks=generated/"checks.json"
        if checks.is_file():
            report=json.loads(checks.read_text())
            if report.get("index_sha256")!=manifest.get("sha256"):
                raise ValueError("check receipt does not match generated index")
            yield "commons_worker_receipt",report
    for p in sorted((root/"legacy").glob("*.jsonl")):
        for line in p.read_text().splitlines():
            yield "commons_legacy_metadata", json.loads(line)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("query")
    p.add_argument("--root",type=Path,default=BASE)
    p.add_argument("--limit",type=int,default=20)
    p.add_argument("--layer", choices=["commons_typed","external_source_only","external_manifest_entry","commons_legacy_metadata","commons_git_source","commons_worker_receipt"])
    args = p.parse_args()
    if not 1 <= args.limit <= 1000 or not terms(args.query):
        p.error("query must contain tokens; limit must be between 1 and 1000")
    found=[]
    for layer, row in rows(args.root):
        if args.layer and args.layer != layer:
            continue
        hay = json.dumps(row,ensure_ascii=False)
        if terms(args.query) <= terms(hay):
            found.append({"layer":layer,**row})
    print(json.dumps({"matches":len(found),"results":found[:args.limit]},ensure_ascii=False,indent=2))

if __name__ == "__main__":
    main()
