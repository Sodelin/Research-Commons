#!/usr/bin/env python3
"""Check current explanatory links and source identities; validate no anchors."""
from datetime import datetime, timezone
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

from review_support_join import PACKET, identity

FILES = ["lean/HISTORY-CONTEXT-COVERAGE-AUDIT-20261010T210353.534731Z.md", "CHECKPOINT.md", "README.md", "design/RESEARCH-BRIEF.md", "design/LEAN-TO-RUST.md",
    "design/G6-G7-REUSE-STATUS.md", "design/DISCOVERY-DELTA-20261010T1521Z.md",
    "design/DISCOVERY-DELTA-20261010T1540Z.md", "design/CALENDAR-OBLIGATION-SUPPLEMENT-20261010T1730Z.md",
    "rust/notes/NAMED-CALENDAR-ADMISSION-ACCEPTED-REPAIR-REVIEW-20261010T1742Z.md",
    "design/GOAL-STATUS.md", "design/HISTORY-INTEGRATION-RECONCILIATION-20261010.md",
    "design/HISTORY-ASSEMBLY-AUDIT-20261010T2040Z.md", "design/DISCOVERY-DELTA-20261010T2048Z.md",
    "rust/notes/HISTORY-RUNTIME-ASSEMBLY-AUDIT-20261010T2043Z.md",
    "reuse/HISTORY-RECONCILIATION-20261010T205629Z.md"]


def main():
    errors, pins, count = [], [], 0
    for name in FILES:
        path = PACKET / name
        pins.append({"path": name, **identity(path)})
        for target in re.findall(r"\[[^\]\n]*\]\(([^)\n]+)\)", path.read_text()):
            target = target.strip().strip("<>")
            if urlsplit(target).scheme or target.startswith("#"):
                continue
            local = unquote(target.split("#", 1)[0])
            count += 1
            if not (path.parent / local).exists():
                errors.append({"file": name, "target": target})
    result = {"schema": "history_reconciled_navigation_link_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checked_links": count, "pins": pins,
        "reviewer": identity(Path(__file__)),
        "scope": "Current explanatory source identities and local link target existence only; Markdown anchors and remote URLs are not validated. Earlier dated status and navigation bytes remain in exact snapshots. No solver or compiler is run."}
    (PACKET / "quality/HISTORY-CURRENT-NAVIGATION-FINAL-REVIEW.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": result["pass"], "checked_links": count, "errors": errors}))
    return not result["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
