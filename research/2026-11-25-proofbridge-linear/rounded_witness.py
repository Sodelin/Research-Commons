"""Kernel-check one scaled integer-linear witness with an exact pinned target."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

import assumption_relay
import import_reduced as importer
import linear
import premise_handoff

RULE = "commons.linear-int.rounded-witness.v1"


def checked(raw, pin, scale, lean, out, timeout=30):
    linear.require(type(scale) is int and 1 <= scale <= 1000, "invalid positive scale")
    linear.require(linear.sha(raw) == pin, "source certificate hash mismatch")
    original = linear.parse(raw)
    target = original["target"]
    intermediate = {**original, "target":{
        "coeffs":[scale * x for x in target["coeffs"]],
        "le":scale * (target["le"] + 1) - 1}}
    mid_bytes = assumption_relay.canonical(intermediate)
    linear.exact(linear.parse(mid_bytes))
    linear.require(linear.sha(Path(linear.__file__).read_bytes()) == premise_handoff.CHECKER,
                   "unexpected checker bytes")
    lean = lean.resolve(strict=True)
    out = out.resolve()
    version = importer.invoke(lean, out.parent, "--version", timeout=timeout)
    linear.require("commit " + linear.COMMIT + "," in version, "wrong Lean toolchain commit")
    module = "PB_" + linear.sha(mid_bytes)
    provider = importer.provider(module, intermediate)
    original_use = importer.consumer(module, original, list(range(len(original["premises"]))))
    lines = original_use.splitlines()
    linear.require(len(lines) == 5 and lines[3].strip().startswith(module+".certificate "),
                   "unexpected generated consumer")
    lines[2] += " by"
    lines[3] = "  have scaled := " + lines[3].strip()
    lines[4:4] = ["  clear " + " ".join(f"h{i}" for i in range(len(original["premises"]))), "  omega"]
    consumer = "\n".join(lines)+"\n"
    files = {module+".lean":provider, "ReuseOriginal.lean":consumer}
    out.mkdir(exist_ok=False)
    for name, content in files.items():
        (out/name).write_bytes(content.encode("ascii"))
    provider_axioms = importer.axioms(importer.invoke(lean, out, "-o", module+".olean",module+".lean",timeout=timeout))
    consumer_axioms = importer.axioms(importer.invoke(lean, out,"ReuseOriginal.lean",timeout=timeout))
    return {"schema":RULE,"status":"kernel-checked-conditional",
            "source_sha256":pin,"variables":original["variables"],"premises":original["premises"],
            "multipliers":original["multipliers"],"scale":scale,"target":target,
            "intermediate_target":intermediate["target"],"intermediate_certificate_sha256":linear.sha(mid_bytes),
            "lean":version,"provider_axioms":provider_axioms,"consumer_axioms":consumer_axioms,
            "files_sha256":{name:linear.sha((out/name).read_bytes()) for name in [*files,module+".olean"]}}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("source_sha256")
    p.add_argument("scale",type=int)
    p.add_argument("lean",type=Path)
    p.add_argument("out",type=Path)
    a=p.parse_args()
    print(json.dumps(checked(premise_handoff.read(a.source,16384),a.source_sha256,a.scale,a.lean,a.out),indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError,ValueError,subprocess.SubprocessError) as exc:
        sys.exit(str(exc))
