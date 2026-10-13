"""Authenticate this handoff's published files; no mathematical execution."""
from pathlib import Path
import hashlib
import json

p = Path(__file__).resolve().parent
manifest = json.loads((p / "MANIFEST.json").read_bytes())
for row in manifest["files"]:
    relative = Path(row["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("unsafe manifest path")
    source = p / relative
    if source.is_symlink() or not source.is_file():
        raise ValueError("missing or linked artifact")
    raw = source.read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    if (len(raw), hashlib.sha256(raw).hexdigest(), blob) != (row["bytes"], row["sha256"], row["git_blob"]):
        raise ValueError("artifact identity mismatch: " + row["path"])
print("PASS: exact handoff artifacts; no Lean/Rust execution or mathematical acceptance")
