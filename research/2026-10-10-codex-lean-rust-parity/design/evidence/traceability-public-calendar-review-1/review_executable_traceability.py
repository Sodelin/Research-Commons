#!/usr/bin/env python3
"""Freeze and check local evidence links in the mutable executable trace map."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

DESIGN = Path(__file__).resolve().parent
DOCS = ["TRACEABILITY.md", "EPOCH-REFINEMENT.md", "CROSS-DOMAIN-REUSE-20261010.md",
        "ANCESTRAL-COMPLETION-REVIEW-20261010T1317Z.md", "CALENDAR-REFINEMENT-20261010T1340Z.md"]
FROZEN = {"DISCOVERY-MAP.md": "7ef71029593e5e3469ad27331678947cd881eaa328575ae56244628729878179",
          "SOURCE-MAP.json": "5dccc997895eb90da368b40445b037e257a8b3976981ad9499890f9d7eaf10bf"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    pins, links, errors = {}, [], []
    for name in [*DOCS, *FROZEN, Path(__file__).name]:
        path = DESIGN / name
        pins[str(path)] = digest(path)
        if name in FROZEN and pins[str(path)] != FROZEN[name]:
            errors.append("frozen snapshot changed: " + name)
        if name not in DOCS:
            continue
        (args.output / name).write_bytes(path.read_bytes())
        for target in re.findall(r"\]\(([^)]+)\)", path.read_text()):
            target = target.strip().strip("<>")
            if target.startswith(("http://", "https://", "#", "app://", "skill://")):
                continue
            resolved = (path.parent / target.split("#", 1)[0]).resolve()
            links.append({"from": str(path), "target": target, "resolved": str(resolved), "exists": resolved.exists()})
            if not resolved.exists():
                errors.append("missing local evidence: " + target)
    for path, expected in pins.items():
        if digest(Path(path)) != expected:
            errors.append("concurrent source change: " + path)
    answer = {"schema": "mutable_executable_traceability_link_review_v1", "pass": not errors,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "pins": pins, "links": links, "errors": errors,
              "frozen_discovery_and_source_map_mutated": False,
              "mathematical_or_compiler_reverification_claimed": False}
    (args.output / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS" if answer["pass"] else "FAIL", len(links), flush=True)
    if not answer["pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
