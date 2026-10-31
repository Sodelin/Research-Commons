"""Reconstruct the exact audit data only; no compilation or source execution."""
from pathlib import Path
import json, hashlib
root = Path(__file__).resolve().parent
manifest = json.loads((root / 'AUDIT-PARTS.json').read_text())
chunks = []
for row in manifest['parts']:
    data = (root / row['path']).read_bytes()
    assert len(data) == row['bytes']
    assert hashlib.sha256(data).hexdigest() == row['sha256']
    chunks.append(data)
data = b''.join(chunks)
assert len(data) == manifest['reconstructed_bytes']
assert hashlib.sha256(data).hexdigest() == manifest['reconstructed_sha256']
out = root / 'owned-audit.json'
if out.exists():
    assert out.read_bytes() == data
else:
    out.write_bytes(data)
print(manifest['reconstructed_sha256'])
