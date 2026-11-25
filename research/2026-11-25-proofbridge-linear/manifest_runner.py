"""Bounded ProofBridge manifest replay; an earlier receipt never skips a check."""
import argparse, hashlib, json, os, re, subprocess, sys, tempfile, time
from pathlib import Path
import linear

SCHEMA = "commons.proofbridge.manifest.v1"
PINNED_CHECKER = "8872348bfde6b6961e985e8bcfac1db320239e973b84cb79d3b36ec065ae7ee5"
HEX = re.compile(r"[0-9a-f]{64}")
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

def run(folder, manifest, pin, out, start, jobs, wall, per_job):
    folder = folder.resolve(strict=True)
    entries = load(manifest, pin)
    need(0 <= start < len(entries) and 1 <= jobs <= 512 and
         3 <= wall <= 14400 and 1 <= per_job <= 120, "bad run limits")
    out.mkdir(exist_ok=False)
    stop = time.monotonic() + wall
    index = start
    failures = 0
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
            result = linear.checked(data, timeout=allowance)
            need(result["checker_sha256"] == PINNED_CHECKER and
                 result["certificate_sha256"] == e["sha256"], "checker receipt mismatch")
            item.update(status="verified_now", proof=result)
        except subprocess.TimeoutExpired as exc:
            failures += 1
            item.update(status="timed_out", diagnostic=str(exc)[:1000])
        except (OSError, ValueError, subprocess.SubprocessError) as exc:
            failures += 1
            item.update(status="not_verified", diagnostic=str(exc)[:1000])
        save_new_receipt(out, item)
        print(json.dumps(item), flush=True)
        index += 1
    print(json.dumps({"next_index": index, "entries": len(entries), "failures": failures,
                      "complete": index == len(entries)}), flush=True)
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
    a=ap.parse_args()
    if a.op == "make":
        sys.stdout.buffer.write((json.dumps(make(a.folder,a.files),sort_keys=True,indent=2)+"\n").encode("ascii"))
        return 0
    return run(a.folder,a.manifest,a.sha256,a.out,a.start,a.jobs,a.wall,a.per_job)

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError,ValueError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        sys.exit(2)
