#!/usr/bin/env python3
"""Verify packaged bytes; this is an integrity check, not scientific proof."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
PACKET = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def entries():
    roots = [ROOT / 'applications/practical-solver',
             ROOT / 'applications/practical-solver-biology', PACKET]
    files = []
    excluded = {'RELEASE-MANIFEST.json', 'PUBLICATION.json'}
    for base in roots:
        for path in sorted(base.rglob('*')):
            if path.is_symlink():
                raise ValueError('Symlink in release: ' + str(path))
            if not path.is_file() or path.name in excluded:
                continue
            if any(part in {'__pycache__', 'target', '.venv', '.git'} for part in path.parts):
                continue
            if path.suffix == '.pyc':
                continue
            rel = str(path.relative_to(ROOT))
            files.append({'path': rel, 'bytes': path.stat().st_size,
                          'sha256': digest(path), 'origin': 'additive release artifact'})
    # The inherited application and practical baseline remain separate sources.
    inherited = [ROOT / 'applications/AGENTS.md', ROOT / 'applications/LICENSE',
                 ROOT / 'applications/MIGRATION-PROVENANCE.json',
                 ROOT / 'applications/scientific-integration/run.py']
    inherited.extend(ROOT / 'applications/molecular-analysis' / relative for relative in (
        'molecular_apps/contracts.py', 'molecular_apps/providers.py',
        'molecular_apps/rna_processing.py', 'molecular_apps/cli.py',
        'examples/synthetic-rna-processing.json'))
    source = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration'
    inherited.extend(source / relative for relative in (
        'integration_core.py', 'declared-model/DATASET.json',
        'composition-attempt1/ANALYSIS-REQUEST.json',
        'composition-attempt1/prepared/CONFIDENCE.json',
        'composition-attempt1/prepared/EXTRACTION.json'))
    inherited.append(ROOT / 'research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json')
    baseline = ROOT / 'research/2026-10-08-codex-integration-0825z/practical'
    inherited.extend(p for p in baseline.rglob('*') if p.is_file()
                     and '__pycache__' not in p.parts and 'target' not in p.parts
                     and p.suffix != '.pyc')
    for path in sorted(set(inherited)):
        files.append({'path': str(path.relative_to(ROOT)), 'bytes': path.stat().st_size,
                      'sha256': digest(path), 'origin': 'inherited dependency; preserved'})
    return sorted(files, key=lambda row: row['path'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-manifest', action='store_true',
                        help='Create the manifest once; refuses overwrite.')
    args = parser.parse_args()
    manifest = PACKET / 'RELEASE-MANIFEST.json'
    if args.write_manifest:
        rows = entries()
        value = {'schema': 'practical_release_integrity_v1',
                 'scope': 'Byte integrity only; no execution, theorem or biological certification.',
                 'manifest_and_publication_receipt_excluded_from_own_hash_list': True,
                 'files': rows}
        with manifest.open('x', encoding='utf-8') as stream:
            stream.write(json.dumps(value, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'status': 'MANIFEST_CREATED', 'files': len(rows)}))
        return 0
    value = json.loads(manifest.read_text(encoding='utf-8'))
    failures = []
    for row in value['files']:
        path = ROOT / row['path']
        if not path.resolve().is_relative_to(ROOT) or path.is_symlink() or not path.is_file():
            failures.append(row['path'])
        elif path.stat().st_size != row['bytes'] or digest(path) != row['sha256']:
            failures.append(row['path'])
    print(json.dumps({'status': 'FAIL' if failures else 'BYTE_INTEGRITY_PASS',
                      'files': len(value['files']), 'failures': failures,
                      'scientific_claims_verified': False}, sort_keys=True))
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
