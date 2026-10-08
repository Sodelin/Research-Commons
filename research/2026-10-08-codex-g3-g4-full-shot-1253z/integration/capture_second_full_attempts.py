"""Snapshot explicit frozen selections; never traverse workers' live directories."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
import subprocess

BASE = Path('research/2026-10-08-codex-g3-g4-full-shot-1253z')
OUTPUT = BASE / 'integration/SECOND-FULL-ATTEMPT-PUBLICATION-MANIFEST.json'
MANIFESTS = [
    'g3-witness-bound/attempt2/ARTIFACT-MANIFEST.json',
    'g3-witness-bound/attempt2/ARTIFACT-MANIFEST-R2.json',
    'g3-complete-classification/FOUR-SUPPORT-FROZEN-WHITELIST.json',
    'g3-complete-classification/ATTEMPT-3-FROZEN-WHITELIST.json',
    'g3-complete-classification/ATTEMPT-3-ADDITIVE-FROZEN-WHITELIST.json',
    'g3-complete-classification/ATTEMPT-3-FINAL-CLARIFIED-SELECTION.json',
    'g3-impossibility/log-character-gate/PUBLIC-FILES.json',
    'g3-impossibility/zero-margin-continuation/PUBLIC-FILES.json',
    'g3-impossibility/nonlinear-counter-lifts/PUBLIC-FILES.json',
    'g4-effective-stopping/CHECKPOINT-MANIFEST.json',
    'g4-global-forcing/attempt-2/PUBLIC-MANIFEST-ADDITIONAL-FROZEN.json',
    'g4-fixed-target/attempt-5/PUBLIC-FILES-ATTEMPT5.json',
]
KEYS = ('files', 'objects', 'artifacts', 'owned_content_rows',
        'independent_review_and_replay_pins', 'additional_static_source_pins')
EXTRA = [
    'integration/ROOT-SECOND-ATTEMPT-SOURCE-REVIEW.md',
    'integration/ROOT-FOURTH-DIAGONAL-JENSEN-REVIEW.md',
    'integration/ROOT-ATTAINED-BOUNDARY-INDEPENDENT-REVIEW.md',
    'integration/ROOT-PRIVATE-ALL-COPY-RIGIDITY-REVIEW.md',
    'integration/ROOT-SHARP-LOSS-ATTAINABILITY-REVIEW.md',
    'integration/ROOT-SUPPLIED-NORMAL-ARITHMETIC-REVIEW.md',
    'integration/ROOT-LOCAL-RARE-FIBRE-REVIEW.md',
    'integration/check_boundary_normal_independently.py',
    'integration/INDEPENDENT-BOUNDARY-NORMAL-EXACT-RECEIPT.json',
    'integration/SECOND-FULL-ATTEMPT-CHECKPOINT.md',
    'integration/capture_second_full_attempts.py',
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
for relative in EXTRA:
    capture(BASE / relative)
capture(BASE / 'g3-complete-classification/WEAK-CELL-JENSEN-CONTROL.md',
        'b15ecfd936a063582003e3229f3e7fe8688e8b10d174bc901e61254698abe3b0', 3868)

receipt = {
    'schema': 'root-six-second-full-attempts-frozen-source-v1',
    'captured_utc': datetime.now(timezone.utc).isoformat(),
    'base_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'original_masters': {'G3': 'OPEN', 'G4_full_menu': 'OPEN'},
    'strongest_accepted_consequence': 'Actual rational attained COMMON source boundary; exact cap-eight equality forces full all-copy private survival/forest law, with calibrated natural A/B transport only',
    'other_acceptances': 'Scoped independent HAND source, arithmetic and local-fibre reviews; author exact controls distinguished from independent source-formula replay',
    'candidate_screen_status': 'Optional entropy/moment and rational-counter transfer screens preserved as failed/scoped attempts, not full source hardness or root-executed validation',
    'verification_limits': 'No new Lean/compiler/RCF census/native pipeline/biological validation; no numerical near-one cutoff or original whole-master completion',
    'files': sorted(rows.values(), key=lambda row: row['path']),
    'manifest_self_excluded': True,
    'live_drafts_scratch_and_caches_excluded': True,
    'previous_manifest_preserved': 'FULL-ATTEMPT-PUBLICATION-MANIFEST.json',
}
with OUTPUT.open('x') as stream:
    stream.write(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'objects': len(rows), 'bytes': sum(r['bytes'] for r in rows.values()),
                  'sha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest()}))
