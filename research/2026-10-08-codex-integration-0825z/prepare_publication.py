"""Audit the explicitly owned public checkpoint; never stage or publish files."""
from pathlib import Path
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent
REPO = BASE.parent.parent
EXCLUDED_PARTS = {'__pycache__', '.venv', 'target', '.git', 'integration-results'}
EXCLUDED_SUFFIXES = {'.pyc', '.pyo', '.sqlite', '.sqlite3', '.db'}
PATTERNS = [re.compile(rb'AIza[0-9A-Za-z_-]{35}'),
            re.compile(rb'gh[pousr]_[0-9A-Za-z]{30,}'),
            re.compile(rb'sk-(?:proj-)?[0-9A-Za-z_-]{35,}'),
            re.compile(rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----')]


def candidates():
    for directory in (BASE, REPO / 'applications'):
        for path in sorted(directory.rglob('*')):
            if not path.is_file() or path.name == 'PUBLICATION-MANIFEST.json':
                continue
            if EXCLUDED_PARTS.intersection(path.parts) or path.suffix in EXCLUDED_SUFFIXES:
                continue
            if path.is_symlink():
                raise ValueError('symlink is outside the publication contract')
            yield path


def main():
    rows = []
    for path in candidates():
        raw = path.read_bytes()
        if len(raw) > 32 * 2**20:
            raise ValueError('oversized public artifact')
        if any(pattern.search(raw) for pattern in PATTERNS):
            # Never print matching values.
            raise ValueError('credential-like bytes require an independent correction')
        if path.suffix == '.json':
            json.loads(raw)
        rows.append({'path': str(path.relative_to(REPO)), 'bytes': len(raw),
                     'sha256': hashlib.sha256(raw).hexdigest()})
    result = {'schema': 'codex-integration-publication-v1',
              'owned_roots': [str(BASE.relative_to(REPO)), 'applications'],
              'authorization': 'Nolan authorized these research artifacts and named public application migration.',
              'scope_record_modified': False, 'original_sources_modified': False,
              'compiled_executables_or_third_party_packages_included': False,
              'credentials_personal_data_or_unrelated_private_material_authorized': False,
              'scan': 'bounded file size, JSON parse, no symlinks, excluded runtime caches, common credential/private-key patterns',
              'scan_is_not_proof_of_absence_of_sensitive_information': True,
              'files': rows, 'count': len(rows),
              'bytes': sum(row['bytes'] for row in rows)}
    (BASE / 'PUBLICATION-MANIFEST.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'count': result['count'], 'bytes': result['bytes'], 'status': 'PASS'}))


if __name__ == '__main__':
    main()
