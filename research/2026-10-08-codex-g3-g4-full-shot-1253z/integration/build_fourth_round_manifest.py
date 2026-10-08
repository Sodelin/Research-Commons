"""Capture and verify only the previously frozen, reviewed publication whitelists."""
import hashlib
import json
from pathlib import Path

BASE = Path('research/2026-10-08-codex-g3-g4-coordinated-1000z')
OUTPUT = Path('research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/FOURTH-ROUND-PUBLICATION-MANIFEST.json')
SELECTIONS = [
    'review/REVIEW-FOURTH-ROUND-FILES.json',
    'g3-coupled/LOG-PRODUCT-ARTIFACT-MANIFEST.json',
    'g3-coupled/LOG-PRODUCT-ARTIFACT-MANIFEST-R2.json',
    'g3-coupled/LOG-PRODUCT-ARTIFACT-MANIFEST-R3.json',
    'g3-coupled/HIGH-RANK-ARTIFACT-MANIFEST-R4.json',
    'g3-singular/EXPOSED-CLOSURE-ARTIFACT-MANIFEST.json',
    'g4-forest/outside-box-continuation/PUBLIC-FILES.json',
    'g4-positive/fixed-window-transport/MANIFEST.json',
    'g4-stopping/two-insertion/MANIFEST-POST-REVIEW.json',
    'g4-stopping/marked-nonordinary/MANIFEST-POST-ACCEPTANCE.json',
]
rows = {}


def capture(path, expected=None, size=None):
    path = Path(path)
    if not path.is_relative_to(BASE) or '__pycache__' in path.parts:
        raise ValueError(f'Outside frozen packet: {path}')
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None and expected != digest:
        raise ValueError(f'Hash mismatch: {path}')
    if size is not None and size != len(data):
        raise ValueError(f'Byte-count mismatch: {path}')
    row = {'path': str(path), 'sha256': digest, 'bytes': len(data)}
    if str(path) in rows and rows[str(path)] != row:
        raise ValueError(f'Conflicting captured object: {path}')
    rows[str(path)] = row


for relative in SELECTIONS:
    manifest = BASE / relative
    capture(manifest)
    content = json.loads(manifest.read_bytes())
    for key in ('files', 'objects', 'review'):
        items = content.get(key, [])
        if isinstance(items, dict):
            items = [{'path': p, 'sha256': h} for p, h in items.items()]
        for item in items:
            name = item['path']
            path = Path(name) if name.startswith('research/') else manifest.parent / name
            capture(path, item['sha256'], item.get('bytes'))

result = {
    'schema': 'root-reviewed-fourth-round-captured-whitelist-v1',
    'scope': 'Previously reviewed source/reviews only; six new full-shot drafts excluded',
    'scientific_status': 'Scoped independent HAND/SOURCE ACCEPT; original G3/G4 OPEN',
    'files': sorted(rows.values(), key=lambda r: r['path']),
    'manifest_self_excluded': True,
    'mandatory_log_coefficient_correction': '0044b3279bee2b4c90b6dec3744139c595b27fec640370694ecc5dc0cccb0d36',
    'compiler_or_inherited_source_execution': False,
}
OUTPUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'verified_objects': len(rows), 'verified_bytes': sum(x['bytes'] for x in rows.values()), 'manifest_sha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}))
