#!/usr/bin/env python3
"""Verify delivered bytes and decoded evidence without invoking a compiler."""
import gzip,hashlib,json,pathlib
root=pathlib.Path(__file__).resolve().parent
manifest=json.loads((root/'PUBLIC-MANIFEST.json').read_text())
for row in manifest['files']:
    b=(root/row['path']).read_bytes()
    if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:
        raise SystemExit('Delivery mismatch '+row['path'])
for row in json.loads((root/'PRIVACY-PROJECTION.json').read_text())['records']:
    b=(root/row['path']).read_bytes();decoded=gzip.decompress(b) if row['encoding']=='gzip' else b
    if len(decoded)!=row['decoded_public_bytes'] or hashlib.sha256(decoded).hexdigest()!=row['decoded_public_sha256']:
        raise SystemExit('Decoded mismatch '+row['path'])
print('PASS: delivered and decoded byte inventory; no proof replay')
