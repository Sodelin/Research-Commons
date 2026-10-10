#!/usr/bin/env python3
"""Check this application derivative and unchanged inherited bridge bytes."""
import hashlib
import json
from pathlib import Path
import sys

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check(row):
    relative = row["path"]
    path = ROOT / relative
    if (not isinstance(relative, str) or Path(relative).is_absolute()
            or ".." in Path(relative).parts or not path.resolve().is_relative_to(ROOT)
            or any(parent.is_symlink() for parent in (path, *path.parents))
            or not path.is_file()):
        return False
    data = path.read_bytes()
    return len(data) == row["bytes"] and sha(data) == row["sha256"]


def main():
    current = json.loads((PACKET / "APPLICATION-DERIVATIVE-PINS.json").read_text())
    previous_path = ROOT / current["inherited_manifest"]["path"]
    previous_bytes = previous_path.read_bytes()
    if sha(previous_bytes) != current["inherited_manifest"]["sha256"]:
        raise ValueError("Inherited bridge manifest identity mismatch")
    previous = json.loads(previous_bytes)
    updated = current["inherited_derivatives"] + current.get("inherited_baseline_updates", [])
    replacements = {row["path"]: row for row in updated}
    if len(replacements) != len(updated):
        raise ValueError("Duplicate derivative entry")
    failures = []
    inherited_count = 0
    for row in previous["files"]:
        if row["path"] in replacements:
            if row["sha256"] != replacements[row["path"]]["previous_sha256"]:
                raise ValueError("Derivative origin mismatch: " + row["path"])
        else:
            inherited_count += 1
            if not check(row):
                failures.append(row["path"])
    previous_names = {row["path"] for row in previous["files"]}
    if not set(replacements) <= previous_names:
        raise ValueError("Derivative has no inherited origin")
    seen = set()
    for row in current["files"]:
        if row["path"] in seen:
            raise ValueError("Duplicate current source entry")
        seen.add(row["path"])
        if not check(row):
            failures.append(row["path"])
    if not set(replacements) <= seen:
        raise ValueError("Missing derivative byte pins")
    result = {"status": "APPLICATION_BYTE_INTEGRITY_PASS" if not failures else "FAIL",
              "inherited_unchanged_files": inherited_count,
              "known_inherited_baseline_updates": len(current.get("inherited_baseline_updates", [])),
              "current_files": len(current["files"]), "failures": failures,
              "scientific_claims_verified": False, "whole_solver_refinement_verified": False}
    print(json.dumps(result, sort_keys=True))
    return bool(failures)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error)}), file=sys.stderr)
        sys.exit(1)
