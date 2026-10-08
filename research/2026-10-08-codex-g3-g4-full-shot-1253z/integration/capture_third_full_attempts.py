"""Capture reviewed third-round source by explicit immutable selections only."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
import subprocess

BASE = Path('research/2026-10-08-codex-g3-g4-full-shot-1253z')
OUTPUT = BASE / 'integration/THIRD-FULL-ATTEMPT-PUBLICATION-MANIFEST.json'
MANIFESTS = [
    'g3-witness-bound/attempt3/ARTIFACT-MANIFEST.json',
    'g3-impossibility/algebraic-normal-unit-level/PUBLIC-FILES.json',
    'g3-impossibility/common-whole-stopping-review/PUBLIC-FILES.json',
    'g3-complete-classification/ATTEMPT-4-FROZEN-SELECTION.json',
    'g3-complete-classification/ATTEMPT-4-FINAL-FROZEN-SELECTION.json',
    'g4-effective-stopping/attempt-3/FINAL-ACCEPTANCE-AND-SELECTION.json',
    'g4-global-forcing/attempt-3/REVIEW-MANIFEST.json',
    'g4-fixed-target/attempt-6/PUBLIC-FILES-ATTEMPT6.json',
]
KEYS = ('files', 'objects', 'artifacts', 'owned_content_rows',
        'independent_review_pins', 'independent_review_and_replay_pins',
        'mandatory_peer_bodies')
EXTRA = [
    'integration/ROOT-NEUTRAL-CRITICAL-CURVE-CATALOGUE-REVIEW.md',
    'integration/ROOT-WHOLE-COMMON-STOPPING-REVIEW.md',
    'integration/ROOT-ARC-VALUE-AND-SUPPORTED-NODES-REVIEW.md',
    'integration/ROOT-THIRD-FULL-ATTEMPT-FAILURE-REVIEW.md',
    'integration/THIRD-FULL-ATTEMPT-CHECKPOINT.md',
    'integration/capture_third_full_attempts.py',
]
rows = {}


def capture(path, expected=None, size=None):
    path = Path(path)
    if (not path.is_relative_to(BASE) or '..' in path.parts
            or '__pycache__' in path.parts or path.is_symlink()):
        raise ValueError(f'Outside frozen public source: {path}')
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None and digest != expected:
        raise ValueError(f'Frozen hash mismatch: {path}')
    if size is not None and len(data) != size:
        raise ValueError(f'Frozen size mismatch: {path}')
    row = {'path': str(path), 'sha256': digest, 'bytes': len(data)}
    if str(path) in rows and rows[str(path)] != row:
        raise ValueError(f'Conflicting frozen evidence: {path}')
    rows[str(path)] = row


for relative in MANIFESTS:
    manifest = BASE / relative
    capture(manifest)
    doc = json.loads(manifest.read_bytes())
    found = False
    for key in KEYS:
        for item in doc.get(key, []):
            found = True
            path = Path(item['path'])
            if not str(path).startswith('research/'):
                path = manifest.parent / path
            capture(path, item['sha256'], item.get('bytes'))
    if not found:
        raise ValueError(f'No recognized frozen rows: {manifest}')
    for name in doc.get('mandatory_proof_objects', []):
        if str(manifest.parent / name) not in rows:
            raise ValueError(f'Mandatory proof omitted from frozen objects: {name}')
for relative in EXTRA:
    capture(BASE / relative)
capture(BASE / 'g3-complete-classification/ATTEMPT-3-CONTINUE-HERE.md',
        'd0fbf3e528e869a6421e3be8e0a864adef2b46744b050fc0a3efce7c20679d3e', 6561)
capture(BASE / 'g3-complete-classification/ATTEMPT-4-CONTINUE-HERE.md',
        '1a087a65cdac88a42cff696f00c5811f26d631d1f66db53b6fc68f12874e53e8', 3088)

receipt = {
    'schema': 'root-six-third-full-attempts-frozen-source-v1',
    'captured_utc': datetime.now(timezone.utc).isoformat(),
    'base_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'original_masters': {'G3': 'OPEN', 'G4_general': 'OPEN'},
    'completed_branch': 'Whole original-network COMMON-only full-topology forcing and fixed finite routing-menu stopping; exact algebraic effectivity, actual representative under finite protected grammar; given-exposure COMMON-only G3',
    'completed_branch_reviews': 'Independent root review plus second complete source/hand review, requiring all four proof/details/scope/count-correction files',
    'other_scoped_hand_results': 'All-real-normal finite neutral-curve catalogue; complete divisor value-space and finite supported-node interface; precise source-valid failed whole-architecture implications',
    'verification_limits': 'No mathematical source execution, catalogue/RCF run, new Lean/compiler/native release or biological validation in this round',
    'files': sorted(rows.values(), key=lambda row: row['path']),
    'manifest_self_excluded': True,
    'live_drafts_scratch_and_caches_excluded': True,
    'previous_manifest_preserved': 'SECOND-FULL-ATTEMPT-PUBLICATION-MANIFEST.json',
}
with OUTPUT.open('x') as stream:
    stream.write(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'objects': len(rows), 'bytes': sum(r['bytes'] for r in rows.values()),
                  'sha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}))
