#!/usr/bin/env python3
"""Inventory or verify this public packet; integrity is not proof acceptance.

The manifest excludes itself and local build/bytecode directories. Creation
refuses to replace an existing manifest. Verification requires the exact file
set and bytes. It does not execute compilers, reinterpret old receipts as new
runs, or certify the missing physical representative provider.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE/'PACKET-MANIFEST.json'
EXCLUDED = {'.lake', '__pycache__', 'target'}


def inventory(root=HERE):
    rows = []
    for path in sorted(root.rglob('*')):
        relative = path.relative_to(root)
        if relative.as_posix() == 'PACKET-MANIFEST.json' or any(part in EXCLUDED for part in relative.parts):
            continue
        if path.is_symlink():
            raise ValueError('symlink is outside this publication contract: '+str(relative))
        if not path.is_file():
            continue
        if path.stat().st_size > 32*1024**2:
            raise ValueError('per-file publication limit: '+str(relative))
        data = path.read_bytes()
        if data.startswith(b'\x7fELF') or path.suffix in {'.olean', '.rlib', '.so'}:
            raise ValueError('compiled runtime belongs in scratch: '+str(relative))
        rows.append(dict(path=relative.as_posix(), bytes=len(data),
                         sha256=hashlib.sha256(data).hexdigest()))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--root', type=Path, default=HERE)
    args = parser.parse_args()
    manifest = args.root.resolve()/'PACKET-MANIFEST.json'
    observed = inventory(args.root.resolve())
    if args.write:
        report = dict(schema='astra_public_packet_manifest_v1', files=observed,
                      excluded=['PACKET-MANIFEST.json', *sorted(EXCLUDED)],
                      meaning='Exact artifact integrity only; consult scoped execution receipts.',
                      original1613='Authenticated complete source selection and historical execution.',
                      original1614='Recorded acceptance/recovery; complete public physical body still missing.',
                      original1615='Recorded historical acceptance; complete recovered packet still missing.',
                      general_G3_resolved=False)
        with manifest.open('x') as output:
            output.write(json.dumps(report, indent=2, sort_keys=True)+'\n')
    else:
        report = json.loads(manifest.read_text())
        if report.get('schema') != 'astra_public_packet_manifest_v1':
            raise ValueError('unsupported manifest')
        if observed != report['files']:
            old = {row['path']: row for row in report['files']}
            new = {row['path']: row for row in observed}
            changed = sorted(k for k in old.keys() | new.keys() if old.get(k) != new.get(k))
            raise ValueError('packet differs: '+', '.join(changed[:25]))
    print(json.dumps(dict(status='INTEGRITY_VERIFIED', files=len(observed),
                          bytes=sum(row['bytes'] for row in observed),
                          manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
                          compiler_executed=False, physical_representative_certified=False)))


if __name__ == '__main__':
    main()
