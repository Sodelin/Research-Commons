"""Build a checked, importable Lean module from an exact premise handoff."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import assumption_relay
import linear
import premise_handoff as handoff


def provider(module, certificate):
    source = linear.lean_source(certificate)
    marker = "theorem addScaled"
    linear.require(source.count(marker) == 1, "unexpected source template")
    return source.replace(marker, f"namespace {module}\n{marker}", 1) + f"end {module}\n"


def consumer(module, original, kept_indices):
    names = [f"x{i}" for i in range(len(original["variables"]))]
    def inequality(row):
        lhs = " + ".join(f"{linear.lint(a)} * {x}" for a, x in zip(row["coeffs"], names))
        return f'{lhs} <= {linear.lint(row["le"])}'
    args = [f"({'_' if i not in kept_indices else ''}h{i} : {inequality(p)})" for i, p in enumerate(original["premises"])]
    apply_args = names + [f"h{i}" for i in kept_indices]
    vars_str = " ".join(names)
    return (f"import {module}\nset_option warningAsError true\n"
            f"theorem reuseOriginal ({vars_str} : Int) {' '.join(args)} : "
            f"{inequality(original['target'])} :=\n"
            f"  {module}.certificate {' '.join(apply_args)}\n"
            "#print axioms reuseOriginal\n")


def invoke(lean, directory, *args, timeout=30):
    env = {k:v for k,v in os.environ.items() if not k.startswith("LEAN_")}
    env["LEAN_PATH"] = str(directory)
    proc = subprocess.run([str(lean), *args], cwd=directory, env=env,
                          text=True, capture_output=True, timeout=timeout)
    linear.require(proc.returncode == 0, "Lean refused: " + (proc.stdout + proc.stderr)[:2000])
    return proc.stdout.strip()


def axioms(output):
    m = re.fullmatch(r"'[A-Za-z0-9_.]+' depends on axioms: \[([^\]]*)\]", output)
    if re.fullmatch(r"'[A-Za-z0-9_.]+' does not depend on any axioms", output):
        return []
    linear.require(m is not None, "unexpected axiom output")
    got = [a.strip() for a in m[1].split(",")] if m[1] else []
    linear.require(set(got) <= {"propext", "Quot.sound", "Classical.choice"}, "unapproved axioms")
    return got


def build(raw, pin, theorem_id, acceptance, lean, out):
    shape = handoff.shape(raw, pin, theorem_id)
    reduced = shape["reduced_certificate"]
    canonical = assumption_relay.canonical(reduced)
    keys = {"schema":"commons.proofbridge.premise_acceptance.v1", "theorem_id":theorem_id,
            "source_certificate_sha256":pin, "target_id":shape["target_id"],
            "premise_ids":shape["retained_premise_ids"], "dropped_premise_ids":shape["dropped_premise_ids"]}
    linear.require(type(acceptance) is dict and all(acceptance.get(k) == v for k,v in keys.items()),
                   "acceptance scope or premise IDs mismatch")
    linear.require(keys["dropped_premise_ids"], "no smaller theorem to import")
    linear.exact(reduced)
    lean = lean.resolve(strict=True)
    out = out.resolve()
    version = invoke(lean, out.parent, "--version")
    linear.require("commit " + linear.COMMIT + "," in version, "wrong Lean toolchain commit")
    module = "PB_" + linear.sha(canonical)
    original = linear.parse(raw)
    kept = [i for i, w in enumerate(original["multipliers"]) if w]
    paths = {module+".lean":provider(module, reduced), "ReuseOriginal.lean":consumer(module, original, kept)}
    out.mkdir(exist_ok=False)
    for name, content in paths.items():
        (out/name).write_bytes(content.encode("ascii"))
    provider_axioms = axioms(invoke(lean, out, "-o", module+".olean", module+".lean"))
    consumer_axioms = axioms(invoke(lean, out, "ReuseOriginal.lean"))
    return {**keys, "schema":"commons.proofbridge.import_reduced.v1",
            "status":"kernel-checked-conditional",
            "standalone_module":module, "theorem":module+".certificate",
            "lean":version, "lean_binary_sha256":linear.sha(lean.read_bytes()), "implicit_imports":["Lean"], "checker_sha256":handoff.CHECKER,
            "provider_axioms":provider_axioms, "consumer_axioms":consumer_axioms,
            "files_sha256":{name:linear.sha((out/name).read_bytes())
              for name in [*paths, module+".olean"]}}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("theorem_id")
    p.add_argument("source_sha256")
    for key in ("source", "acceptance", "lean", "out"):
        p.add_argument(key, type=Path)
    a = p.parse_args()
    raw = handoff.read(a.source, 16384)
    got = json.loads(handoff.read(a.acceptance, 65536), object_pairs_hook=linear.object_pairs)
    print(json.dumps(build(raw, a.source_sha256, a.theorem_id, got, a.lean, a.out), indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        sys.exit(str(exc))
