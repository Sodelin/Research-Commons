#!/usr/bin/env python3
"""Check the published bridge's pinned bytes; no scientific certification."""
from pathlib import Path
import hashlib
import json
import sys

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[1]


def main():
    manifest = json.loads((PACKET / 'BRIDGE-MANIFEST.json').read_text())
    failures = []
    seen = set()
    for row in manifest['files']:
        relative = row['path']
        path = ROOT / relative
        if (not isinstance(relative, str) or relative in seen
                or Path(relative).is_absolute() or '..' in Path(relative).parts
                or not path.resolve().is_relative_to(ROOT)
                or any(parent.is_symlink() for parent in (path, *path.parents))
                or not path.is_file()):
            failures.append(relative)
            continue
        seen.add(relative)
        data = path.read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            failures.append(relative)
    result = {'status': 'BYTE_INTEGRITY_PASS' if not failures else 'FAIL',
              'files': len(manifest['files']), 'failures': failures,
              'scientific_claims_verified': False}
    print(json.dumps(result, sort_keys=True))
    return bool(failures)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({'status': 'FAIL', 'error': str(error),
                          'scientific_claims_verified': False}), file=sys.stderr)
        sys.exit(1)
