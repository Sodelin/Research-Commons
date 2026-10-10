#!@path/21cc473fde0050ab4e99/env python3
"""Verify and unpack the G5 certificate evidence using Python's standard library."""
import base64, hashlib, io, json, lzma, pathlib, tarfile
p=pathlib.Path(__file__).resolve().parent
m=json.loads((p/'EVIDENCE-MANIFEST.json').read_text())
chunks=[]
for r in m['parts']:
 b=(p/r['path']).read_bytes(); assert hashlib.sha256(b).hexdigest()==r['sha256'];chunks.append(b)
b=base64.b64decode(b''.join(chunks));assert hashlib.sha256(b).hexdigest()==m['archive_sha256']
with tarfile.open(fileobj=io.BytesIO(lzma.decompress(b))) as t:
 expected={r['path']:r for r in m['files']}
 assert set(t.getnames())==set(expected)
 out=p/'unpacked-evidence';out.mkdir(exist_ok=True)
 for member in t.getmembers():
  assert member.isfile() and not pathlib.PurePosixPath(member.name).is_absolute() and '..' not in pathlib.PurePosixPath(member.name).parts
  data=t.extractfile(member).read(); row=expected[member.name]
  assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
  q=out/member.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==data
  else:q.write_bytes(data)
print('Verified and unpacked',len(expected),'public evidence files.')
