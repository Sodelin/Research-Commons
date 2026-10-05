#!/usr/bin/env python3
"""Verify archival raw identities without executing files or writing outputs."""
from pathlib import Path
import gzip,hashlib,json
root=Path(__file__).resolve().parent
data=json.loads((root/'RAW-IDENTITIES.json').read_text())
for row in data['files']:
    p=root/row['delivered_path']
    b=p.read_bytes()
    if row['encoding']=='gzip': b=gzip.decompress(b)
    if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:
        raise SystemExit('Raw identity mismatch: '+row['delivered_path'])
    h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    if h!=row['git']: raise SystemExit('Git identity mismatch: '+row['delivered_path'])
print(json.dumps({'status':'PASS','raw_files':len(data['files']),'mode':'decode-only, no execution'}))
