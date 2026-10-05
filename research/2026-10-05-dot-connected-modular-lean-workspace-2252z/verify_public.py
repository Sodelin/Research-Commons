#!/usr/bin/env python3
"""Read-only verification of the public source and complete historical evidence bytes.
Does not compile Lean, import evidence as an object cache, or extract archive files.
"""
from pathlib import Path,PurePosixPath
import hashlib,json,tarfile
ROOT=Path(__file__).resolve().parent
hashfile=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
manifest=json.loads((ROOT/'PUBLIC-MANIFEST.json').read_bytes())
expected=manifest['files']
paths=list(ROOT.rglob('*'))
assert all(not p.is_symlink() for p in paths),'Outer-package symlinks are not allowed'
actual={str(p.relative_to(ROOT)) for p in paths if p.is_file() and str(p.relative_to(ROOT))!='PUBLIC-MANIFEST.json'}
assert actual==set(expected),'Unexpected or missing public file'
for name,e in expected.items():
 p=ROOT/name;assert p.stat().st_size==e['bytes'] and hashfile(p)==e['sha256'],name
idx=json.loads((ROOT/'evidence/EVIDENCE-INDEX.json').read_bytes());rows={e['member']:e for e in idx['members']};assert len(rows)==len(idx['members'])
seen=set()
for a in idx['archives']:
 p=ROOT/'evidence'/a['file'];assert p.stat().st_size==a['bytes'] and hashfile(p)==a['sha256'];count=total=0
 with tarfile.open(p,'r|xz') as tf:
  for t in tf:
   n=t.name;parts=PurePosixPath(n).parts;assert not n.startswith('/') and '..' not in parts and t.isfile() and not t.issym() and not t.islnk(),n
   assert n in rows and n not in seen and rows[n]['archive']==a['file'];e=rows[n];assert t.size==e['public_bytes'];f=tf.extractfile(t);h=hashlib.file_digest(f,'sha256').hexdigest();assert h==e['public_sha256'],n;seen.add(n);count+=1;total+=t.size
 assert count==a['members'] and total==a['decoded_bytes'],a['file']
assert seen==set(rows)
graph=json.loads((ROOT/'package/DEPENDENCY-GRAPH.json').read_bytes());sources=ROOT/'package/source-store'
for g in graph['targets'].values():
 for e in g['modules'].values():assert hashfile(sources/(e['sha256']+'.lean'))==e['sha256']
print(json.dumps({'status':'PASS','public_files':len(expected)+1,'evidence_members':len(seen),'targets':len(graph['targets']),'lean_compilation_performed':False},sort_keys=True))
