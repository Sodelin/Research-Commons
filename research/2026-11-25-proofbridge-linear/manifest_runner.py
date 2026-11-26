"""Bounded ProofBridge manifest replay; an earlier receipt never skips a check."""
import argparse, hashlib, json, os, re, subprocess, sys, tempfile, time
from pathlib import Path
import linear

SCHEMA = "commons.proofbridge.manifest.v1"
PINNED_CHECKER = "8872348bfde6b6961e985e8bcfac1db320239e973b84cb79d3b36ec065ae7ee5"
HEX = re.compile(r"[0-9a-f]{64}")
ROUND_SCHEMA = "commons.proofbridge.rounded_batch_input.v1"
ROUND_HELPERS = {
    "assumption_relay.py":"3427f576c3bae3c6fef3c358e0b21b53a5b1bcbb7c9452a8cc5bc3facf0e42d1",
    "import_reduced.py":"999b7fa74ca16e6353b92a172c7986a9fc15d3d65a1a0b1abcf5dc433f483c1f",
    "premise_handoff.py":"b7f5630f3f0fdf1bbf2ed564f883234d861148d4fcc1e97e620f925a079e51b6",
    "rounded_witness.py":"50e01df9491619035384eadf049d040563927bad726c775093a280259f45dbf2",
}
NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]{0,95}\.json")

def need(condition, msg):
    if not condition:
        raise ValueError(msg)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def bounded_read(path, limit):
    with path.open("rb") as stream:
        contents = stream.read(limit + 1)
    need(len(contents) <= limit, f"oversized input: {path.name}")
    return contents

def checker_hash():
    result = digest(Path(linear.__file__).read_bytes())
    need(result == PINNED_CHECKER, "unexpected validator source")
    return result

def entry_bytes(folder, name):
    need(type(name) is str and NAME.fullmatch(name), "invalid flat input name")
    p = folder / name
    need(p.is_file() and not p.is_symlink() and p.resolve().parent == folder,
         f"input escaped the manifest folder: {name}")
    return bounded_read(p, 16384)

def make(folder, names):
    checker_hash()
    folder = folder.resolve(strict=True)
    need(0 < len(names) <= 512 and len(set(x.casefold() for x in names)) == len(names),
         "empty manifest, too many entries, or duplicate name")
    return {"schema": SCHEMA, "checker_sha256": PINNED_CHECKER,
            "inputs": [{"file": n, "sha256": digest(entry_bytes(folder, n))}
                       for n in sorted(names)]}

def load(path, expected):
    raw = bounded_read(path, 131072)
    need(HEX.fullmatch(expected) and digest(raw) == expected, "manifest hash mismatch")
    o = json.loads(raw, object_pairs_hook=linear.object_pairs)
    linear.fields(o, ["schema", "checker_sha256", "inputs"])
    need(o["schema"] == SCHEMA and o["checker_sha256"] == checker_hash(),
         "unexpected manifest or validator")
    entries = o["inputs"]
    need(type(entries) is list and 0 < len(entries) <= 512, "invalid input count")
    for e in entries:
        linear.fields(e, ["file", "sha256"])
        need(type(e["file"]) is str and NAME.fullmatch(e["file"]) and
             type(e["sha256"]) is str and HEX.fullmatch(e["sha256"]), "invalid entry")
    names = [e["file"] for e in entries]
    need(sorted(names) == names and len(set(n.casefold() for n in names)) == len(names),
         "entries must be sorted and unique")
    return entries

def save_new_receipt(out, item):
    name = f"{item['index']:04}.json"
    dest = out / name
    need(not dest.exists(), "receipt already exists; use a new run directory")
    with tempfile.NamedTemporaryFile(dir=out, prefix="staging_", delete=False,
                                     mode="w", encoding="utf-8", newline="\n") as f:
        stage = Path(f.name)
        json.dump(item, f, sort_keys=True, indent=2)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
    # The run owns a freshly created output directory; readers see only complete receipts.
    os.replace(stage, dest)

def rounded_dependencies():
    here = Path(__file__).resolve().parent
    for name, h in ROUND_HELPERS.items():
        need(digest((here/name).read_bytes()) == h, "unexpected rounded helper: "+name)
    # Only locally installed, source-pinned helpers are executable.
    import rounded_witness
    return rounded_witness


def run(folder, manifest, pin, out, start, jobs, wall, per_job, discovery_jsonl=False,
        rounded_lean=None):
    folder = folder.resolve(strict=True)
    entries = load(manifest, pin)
    need(0 <= start < len(entries) and 1 <= jobs <= 512 and
         3 <= wall <= 14400 and 1 <= per_job <= 120, "bad run limits")
    rounded = rounded_dependencies() if rounded_lean is not None else None
    out.mkdir(exist_ok=False)
    stop = time.monotonic() + wall
    index = start
    failures = 0
    omitted_rounded = 0
    while index < len(entries) and index < start + jobs:
        allowance = min(per_job, (stop-time.monotonic())/3)
        if allowance < 1:
            break
        e = entries[index]
        item = {"index": index, "file": e["file"], "input_sha256": e["sha256"],
                "checker_sha256": PINNED_CHECKER, "manifest_sha256": pin}
        try:
            data = entry_bytes(folder, e["file"])
            need(digest(data) == e["sha256"], "input hash mismatch")
            obj = json.loads(data,object_pairs_hook=linear.object_pairs)
            if type(obj) is dict and obj.get("schema") == ROUND_SCHEMA:
                item["input_schema"] = ROUND_SCHEMA
                need(rounded is not None, "rounded batch input requires --rounded and --lean")
                linear.fields(obj, ["schema","scale","certificate"])
                body = rounded.assumption_relay.canonical(obj["certificate"])
                item["rounded_helper_sha256"] = ROUND_HELPERS
                stage = out / f"module_{index:04}"
                result = rounded.checked(body, digest(body), obj["scale"], rounded_lean, stage,
                                         timeout=min(allowance,per_job/3))
                need(result["source_sha256"] == digest(body), "rounded receipt mismatch")
                item["artifact_dir"] = stage.name
            else:
                result = linear.checked(data, timeout=allowance)
                need(result["checker_sha256"] == PINNED_CHECKER and
                     result["certificate_sha256"] == e["sha256"], "checker receipt mismatch")
            item.update(status="verified_now", proof=result)
        except subprocess.TimeoutExpired as exc:
            failures += 1
            item.update(status="timed_out", diagnostic=str(exc)[:1000])
        except (OSError, TypeError, ValueError, subprocess.SubprocessError) as exc:
            failures += 1
            item.update(status="not_verified", diagnostic=str(exc)[:1000])
        save_new_receipt(out, item)
        if discovery_jsonl and item.get("input_schema") == ROUND_SCHEMA:
            omitted_rounded += 1
        elif discovery_jsonl:
            if item["status"] == "verified_now":
                row={**item["proof"],"file":item["file"]}
            else:
                row={"file":item["file"],"status":"not-verified",
                     "runner_status":item["status"],"diagnostic":item.get("diagnostic","")}
            row.update(schema="commons.proofbridge.discovery_result.v1",
                       certificate_sha256=item["input_sha256"], checker_sha256=PINNED_CHECKER)
            with (out/"discovery-results.jsonl").open("a",encoding="ascii") as log:
                log.write(json.dumps(row,ensure_ascii=True)+"\n")
                log.flush()
                os.fsync(log.fileno())
        print(json.dumps(item), flush=True)
        index += 1
    print(json.dumps({"next_index": index, "entries": len(entries), "failures": failures,
                      "complete": index == len(entries),
                      **({"rounded_omitted_from_discovery":omitted_rounded}
                         if omitted_rounded else {})}), flush=True)
    return int(failures > 0)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    subs=ap.add_subparsers(dest="op", required=True)
    make_p=subs.add_parser("make")
    make_p.add_argument("folder",type=Path)
    make_p.add_argument("files",nargs="+")
    run_p=subs.add_parser("run")
    run_p.add_argument("folder",type=Path)
    run_p.add_argument("manifest",type=Path)
    run_p.add_argument("sha256")
    run_p.add_argument("out",type=Path)
    run_p.add_argument("--start",type=int,default=0)
    run_p.add_argument("--jobs",type=int,default=20)
    run_p.add_argument("--wall",type=int,default=120)
    run_p.add_argument("--per-job",type=int,default=30)
    run_p.add_argument("--lean",type=Path,help="trusted pinned direct Lean executable")
    run_p.add_argument("--discovery-jsonl",action="store_true")
    run_p.add_argument("--rounded",action="store_true",help="enable typed integer-rounding replay")
    a=ap.parse_args()
    if a.op == "make":
        sys.stdout.buffer.write((json.dumps(make(a.folder,a.files),sort_keys=True,indent=2)+"\n").encode("ascii"))
        return 0
    need(not a.rounded or a.lean is not None, "--rounded requires --lean")
    binary=None
    if a.lean is not None:
        binary=a.lean.resolve(strict=True)
        version=subprocess.check_output([str(binary),"--version"],text=True,timeout=10)
        need(linear.COMMIT in version,"wrong Lean toolchain commit")
        linear.LEAN[:]=[str(binary)]
    return run(a.folder,a.manifest,a.sha256,a.out,a.start,a.jobs,a.wall,a.per_job,a.discovery_jsonl,binary if a.rounded else None)

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError,ValueError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        sys.exit(2)
