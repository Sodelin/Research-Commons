"""Capture the six owners' explicit frozen whitelists, never their live directories."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
import subprocess

BASE = Path('research/2026-10-08-codex-g3-g4-full-shot-1253z')
OUTPUT = BASE / 'integration/FULL-ATTEMPT-PUBLICATION-MANIFEST.json'
MANIFESTS = [
    'g4-fixed-target/PUBLIC-FILES-PHASE1.json',
    'g4-fixed-target/PUBLIC-FILES-PHASE2.json',
    'g4-fixed-target/PUBLIC-FILES-PHASE3.json',
    'g4-fixed-target/PUBLIC-FILES-PHASE4.json',
    'g4-global-forcing/PUBLIC-MANIFEST.json',
    'g4-global-forcing/attempt-2/PUBLIC-MANIFEST-INITIAL-FROZEN.json',
    'g4-effective-stopping/PUBLICATION-WHITELIST.json',
    'g3-witness-bound/ARTIFACT-MANIFEST.json',
    'g3-witness-bound/ARTIFACT-MANIFEST-R2.json',
    'g3-complete-classification/FROZEN-PUBLICATION-WHITELIST.json',
    'g3-impossibility/PUBLIC-FILES.json',
    'g3-impossibility/coupled-arithmetic/PUBLIC-FILES.json',
]
EXTRA = [
    'g4-effective-stopping/SCOPED-ACCEPTANCE-RECEIPT.json',
    'integration/ROOT-COCYCLE-AND-CHANNEL-REVIEW.md',
    'integration/ROOT-SEALED-CHANNEL-AND-RICH-MENU-REVIEW.md',
    'integration/ROOT-COMMON-JOINT-COVARIANCE-REVIEW.md',
    'integration/ROOT-GLOBAL-LOSS-AND-EXACT-FIBRE-REVIEW.md',
    'integration/ROOT-COMMON-SOURCE-BOUND-REVIEW.md',
    'integration/ROOT-COMMON-ROUTING-CONTROL-CORRECTION-REVIEW.md',
    'integration/ROOT-G3-ALTERNATIVE-PRESENTATION-REVIEW.md',
    'integration/ROOT-G3-ARITHMETIC-ENCODING-REVIEW.md',
    'integration/FULL-ATTEMPT-CHECKPOINT.md',
    'integration/capture_full_attempts.py',
]
rows = {}


def capture(path, expected=None, size=None):
    path = Path(path)
    if not path.is_relative_to(BASE) or '__pycache__' in path.parts:
        raise ValueError(f'Outside owned frozen source: {path}')
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None and expected != digest:
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
    content = json.loads(manifest.read_bytes())
    found = False
    for key in ('files', 'objects', 'artifacts', 'owned_content_rows', 'independent_review_pins'):
        for item in content.get(key, []):
            found = True
            path = Path(item['path'])
            if not str(path).startswith('research/'):
                path = manifest.parent / path
            capture(path, item['sha256'], item.get('bytes'))
    if not found:
        raise ValueError(f'No recognized frozen rows: {manifest}')
for relative in EXTRA:
    capture(BASE / relative)

result = {
    'schema': 'root-six-full-attempts-frozen-source-v1',
    'captured_utc': datetime.now(timezone.utc).isoformat(),
    'base_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'original_masters': {'G3': 'OPEN', 'G4_full_menu': 'OPEN'},
    'complete_conditional_theorem': 'Exposed-input and probe-admitted proper private COMMON natural/finite-routing-only source reconstruction and stopping',
    'verification': 'Independent scoped HAND reviews; author exact illustrative/control receipts; no new Lean/compiler/QE/census/biological validation',
    'files': sorted(rows.values(), key=lambda r: r['path']),
    'manifest_self_excluded': True,
    'live_drafts_scratch_and_caches_excluded': True,
}
OUTPUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'objects': len(rows), 'bytes': sum(r['bytes'] for r in rows.values()), 'sha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}))
