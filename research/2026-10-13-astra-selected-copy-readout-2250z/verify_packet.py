#!/usr/bin/env python3
"""Read-only packet integrity check, not mathematical or native correctness."""
import hashlib
import json
from pathlib import Path


def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/'PACKET-MANIFEST.json').read_text())
    expected={row['path']:row for row in manifest['files']}
    actual={str(p.relative_to(root)):p for p in root.rglob('*') if p.is_file() and p.name!='PACKET-MANIFEST.json'}
    if set(expected)!=set(actual):raise ValueError('packet file inventory differs')
    for name,path in actual.items():
        row=expected[name]
        if path.is_symlink() or path.stat().st_size!=row['bytes']:
            raise ValueError('packet file kind/size differs: '+name)
        if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:
            raise ValueError('packet file digest differs: '+name)
    print(json.dumps(dict(status='PACKET_INTEGRITY_PASS',files=len(expected),
        manifest_sha256=hashlib.sha256((root/'PACKET-MANIFEST.json').read_bytes()).hexdigest(),
        mathematical_completeness_proved=False,native_universal_correctness_proved=False)))


if __name__=='__main__':main()
