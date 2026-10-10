#!/usr/bin/env python3
"""Check dated source identities and local documentation links, without proof claims."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote, urlsplit

DESIGN = Path(__file__).resolve().parent
REPOSITORY = DESIGN.parents[2]


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def pins(value, trail=""):
    if isinstance(value, dict):
        if "path" in value and "sha256" in value:
            yield trail, value
        for key, child in value.items():
            yield from pins(child, f"{trail}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from pins(child, f"{trail}[{index}]")


def local_links(path: Path):
    # Mathematical notation inside code spans is not a Markdown link.
    body = re.sub(r"```.*?```", "", path.read_text(), flags=re.S)
    body = re.sub(r"`[^`\n]*`", "", body)
    for target in re.findall(r"\[[^\]]+\]\(([^\)]+)\)", body):
        target = target.strip().strip("<>")
        if target.startswith("#") or urlsplit(target).scheme:
            continue
        filename = unquote(target.split("#", 1)[0])
        if filename:
            yield target, (path.parent / filename).resolve()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-map", type=Path, default=DESIGN / "SOURCE-MAP.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # Each invocation keeps its own evidence; never replace an earlier review.
    args.output.mkdir(parents=True, exist_ok=False)
    raw = args.source_map.read_bytes()
    source_map = json.loads(raw)
    errors, checked_pins, checked_links = [], [], []
    for trail, pin in pins(source_map):
        path = REPOSITORY / pin["path"]
        record = {"field": trail, "path": pin["path"], "expected_sha256": pin["sha256"]}
        if path.is_file():
            data = path.read_bytes()
            record.update(observed_sha256=sha(data), observed_bytes=len(data))
            record["pass"] = record["observed_sha256"] == pin["sha256"] and (
                "bytes" not in pin or pin["bytes"] == len(data))
        else:
            record["pass"] = False
        checked_pins.append(record)
        if not record["pass"]:
            errors.append(record)
    for document in sorted(DESIGN.glob("*.md")):
        for target, path in local_links(document):
            record = {"document": str(document.relative_to(REPOSITORY)),
                      "target": target, "resolved_path": str(path), "pass": path.exists()}
            checked_links.append(record)
            if not record["pass"]:
                errors.append(record)
    receipt = {
        "schema": "dated_source_map_link_review_v1",
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors,
        "source_map_sha256": sha(raw),
        "reviewer_sha256": sha(Path(__file__).read_bytes()),
        "pins_checked": len(checked_pins),
        "relative_links_checked": len(checked_links),
        "qualification": "Dated file identities and link targets only; no anchor, compiler, theorem, whole-corpus or master-closure claim.",
        "errors": errors,
        "pins": checked_pins,
        "links": checked_links,
    }
    (args.output / "SOURCE-MAP.json").write_bytes(raw)
    (args.output / "review_source_map.py").write_bytes(Path(__file__).read_bytes())
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "pins_checked", "relative_links_checked", "errors")}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
