#!/usr/bin/env python3
"""Review staged packet raw bytes without changing archived source formatting."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PREFIX = "research/2026-10-10-codex-lean-rust-parity/"
OUTPUT = ROOT / PREFIX / "quality/HISTORY-CHECKPOINT-FINAL-BYTE-REVIEW.json"
SELF_PATH = str(OUTPUT.relative_to(ROOT))

def git(*args):
    return subprocess.check_output(["git", "-c", "gc.auto=0", *args], cwd=ROOT)

paths = git("diff", "--cached", "--name-only", "-z").decode().split("\0")
paths = [p for p in paths if p and p != SELF_PATH]
errors, files = [], []
patterns = [re.compile(rb"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
            re.compile(rb"(?<![A-Za-z0-9])gh[pousr]_[A-Za-z0-9]{30,}"),
            re.compile(rb"(?<![A-Za-z0-9])sk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{40,}")]
reader = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE)
try:
    for path in paths:
        if not path.startswith(PREFIX):
            errors.append({"path": path, "error": "outside owned packet"})
            continue
        blob = git("rev-parse", ":" + path).strip().decode()
        reader.stdin.write((blob + "\n").encode()); reader.stdin.flush()
        fields = reader.stdout.readline().decode().strip().split()
        assert len(fields) == 3 and fields[1] == "blob", fields
        size = int(fields[2]); data = reader.stdout.read(size)
        assert reader.stdout.read(1) == b"\n"
        raw = (ROOT / path).read_bytes()
        if data != raw:
            errors.append({"path": path, "error": "staged Git bytes differ from working bytes"})
        if raw.startswith(b"\x7fELF"):
            errors.append({"path": path, "error": "ELF distribution"})
        if any(pattern.search(raw) for pattern in patterns):
            errors.append({"path": path, "error": "high confidence credential signature"})
        files.append({"path": path, "bytes": size, "sha256": hashlib.sha256(raw).hexdigest(), "git_blob": blob})
finally:
    reader.stdin.close(); reader.stdout.close(); reader.wait()
result = {"schema": "history_checkpoint_final_staged_raw_byte_review_v1",
          "observed_utc": datetime.now(timezone.utc).isoformat(),
          "base_head": git("rev-parse", "HEAD").strip().decode(),
          "pass": not errors, "errors": errors, "file_count": len(files),
          "raw_bytes": sum(f["bytes"] for f in files), "files": files,
          "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          "self_manifest_exclusion": SELF_PATH,
          "scope": "Owned staged packet byte identity, ELF and high confidence credential signatures. This receipt excludes itself and is staged/read back separately after generation. Previous review remains preserved. No compiler or backend invocation."}
OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps({k: result[k] for k in ["pass", "file_count", "raw_bytes", "errors"]}))
raise SystemExit(not result["pass"])
