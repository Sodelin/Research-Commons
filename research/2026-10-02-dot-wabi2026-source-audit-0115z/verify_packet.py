import hashlib, json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "publication-manifest.json").read_text())
for row in manifest["files"]:
    rel = Path(row["path"])
    assert not rel.is_absolute() and ".." not in rel.parts
    b = (root / rel).read_bytes()
    assert len(b) == row["bytes"], row["path"]
    assert hashlib.sha256(b).hexdigest() == row["sha256"], row["path"]
    assert hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest() == row["git_blob_sha"], row["path"]
original = root / "PUBLICATION-MANIFEST.json"
if original.exists():
    for row in json.loads(original.read_text())["files"]:
        b = (root / row["path"]).read_bytes()
        assert len(b) == row["bytes"] and hashlib.sha256(b).hexdigest() == row["sha256"], row["path"]
print(json.dumps({"verified_files": len(manifest["files"]), "all_sha256_and_git_blobs_match": True}))
