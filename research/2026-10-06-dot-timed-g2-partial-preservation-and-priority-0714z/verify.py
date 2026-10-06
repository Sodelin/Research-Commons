#!/usr/bin/env python3
"""Verify this exact partial preservation packet; does not compile or certify a full build."""
from pathlib import Path,PurePosixPath
import json,hashlib,gzip
R=Path(__file__).resolve().parent
for p in R.rglob('*'):
 if p.is_symlink():raise SystemExit('Symlink rejected')
m=json.loads((R/'MANIFEST.json').read_bytes());actual={p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_file() and p!=R/'MANIFEST.json'}
assert actual==set(m['files']),'Allowlist mismatch'
for n,e in m['files'].items():
 p=PurePosixPath(n);assert not p.is_absolute() and '..' not in p.parts
 b=(R/n).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],n
inv=json.loads((R/'RECOVERY-INVENTORY.json').read_bytes());assert inv['exact_recovered_source_count']==17 and len(inv['unrecovered_owned_modules'])==43
for e in inv['exact_sources']:
 b=(R/'sources'/(e['module']+'.lean')).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256']
b=(R/'historical/ACTUAL-IMPORTED-ARTIFACTS.json.gz').read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==inv['preserved_inventory']['git_blob_sha1'];d=gzip.decompress(b);assert hashlib.sha256(d).hexdigest()==inv['preserved_inventory']['decoded_sha256'];assert len(json.loads(d))==20705
print('PASS: exact17-source partial preservation and historical inventory. Complete60-source build is not present; no compilation performed.')
