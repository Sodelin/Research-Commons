#!/usr/bin/env python3
"""Verify newly delivered source identities without assigning proof/build passes."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
MODULAR = ROOT / 'research/2026-10-10-dot-connected-modular-lake-0855z'
RECOVERY = ROOT / 'research/2026-10-10-dot-g7-pending-codex-recovery-0952z'
EXPOSURE = ROOT / 'research/2026-10-10-dot-g6-forest-exposure-handoff-0941z'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pool(path):
    result, errors = set(), []
    for source in sorted(path.glob('*.lean')):
        if source.is_symlink() or sha(source.read_bytes()) != source.stem:
            errors.append(str(source.relative_to(ROOT)))
        result.add(source.stem)
    if not result:
        errors.append('Missing source pool: ' + str(path.relative_to(ROOT)))
    return result, errors


def manifest(path):
    errors = []
    raw = path.read_bytes()
    rows = json.loads(raw)['files']
    for row in rows:
        relative = Path(row['path'])
        source = path.parent / relative
        if (relative.is_absolute() or '..' in relative.parts or source.is_symlink()
                or not source.resolve().is_relative_to(path.parent) or not source.is_file()):
            errors.append(row['path'])
            continue
        data = source.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if (len(data) != row['bytes'] or sha(data) != row['sha256']
                or ('git_blob' in row and blob != row['git_blob'])):
            errors.append(str(source.relative_to(ROOT)))
    return {'path': str(path.relative_to(ROOT)), 'sha256': sha(raw),
            'files_checked': len(rows), 'errors': errors}


def main():
    old = {row['sha256'] for row in json.loads((PACKET / 'lean/SOURCE-MANIFEST.json').read_bytes())['sources']}
    current, current_errors = pool(MODULAR / 'source-store')
    recovery, recovery_errors = pool(RECOVERY / 'source-store')
    checks = [manifest(RECOVERY / 'MANIFEST.json'), manifest(EXPOSURE / 'MANIFEST.json')]
    errors = current_errors + recovery_errors + [x for item in checks for x in item['errors']]
    records = [ROOT / 'AGENTS.md', ROOT / 'START-HERE.md', ROOT / 'docs/RESEARCH-COMPLETION-STANDARD.md',
               ROOT / 'handoffs/2026-10-09-goal-oriented-finish-lines/20261010T094500Z-CODEX-BUILD-HANDOFF.md',
               MODULAR / 'README.md', RECOVERY / 'LATEST-CANDIDATE-STATUS.json', EXPOSURE / 'REVIEW-SCOPE.md']
    receipt = {
        'status': 'SOURCE_IDENTITY_REVIEW_PASS' if not errors else 'FAIL',
        'observed_utc': datetime.now(timezone.utc).isoformat(),
        'repository_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'fetched_main': subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=ROOT, text=True).strip(),
        'governing_records': [{'path': str(p.relative_to(ROOT)), 'sha256': sha(p.read_bytes())} for p in records],
        'source_pools': {
            'previous_public_inventory': len(old), 'new_canonical_delivery': len(current),
            'new_g7_recovery': len(recovery), 'exact_versions_shared_old_and_canonical': len(old & current),
            'canonical_versions_absent_from_old_inventory': len(current - old),
            'old_versions_outside_frozen_canonical': len(old - current),
            'recovery_versions_absent_from_old_inventory': len(recovery - old),
        },
        'manifest_checks': checks, 'errors': errors,
        'publication_hold': 'Superseded explicitly by the delivered 09:45 UTC handoff; sources now merged locally.',
        'acceptance_boundaries': {
            'frozen_required_profiles': 53, 'separately_provisional_profiles': 25,
            'historical_certificates_reassigned': False, 'fresh_canonical_replay_established': False,
            'new_g7_candidate_chains_established': False, 'new_g6_hand_proof_formalized': False,
        },
        'integration_action': 'Retain the immutable 1340-module replay; use the delivered canonical and recovery contexts for separate source-compatible compilation and proof repair.',
        'scope': 'Local source-byte/manifest identity and chronological reconciliation only. No fresh Lean compilation, universal refinement, scientific admission or master-closure claim.',
        'reviewer_sha256': sha(Path(__file__).read_bytes()),
    }
    (PACKET / 'quality/LEADING-INTEGRATION-REVIEW.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': receipt['status'], 'source_pools': receipt['source_pools'], 'errors': errors}))
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
