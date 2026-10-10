"""Verify a hash-indexed XZ evidence archive with bounded memory.
Usage: python verify_portable_archive_stream.py ARCHIVE_DIRECTORY [--extract NEW_DIRECTORY]
No downloaded source is executed. Existing files are never overwritten.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,lzma,tarfile
class HashReader:
 def __init__(self,f):self.f=f;self.h=hashlib.sha256();self.size=0
 def read(self,n=-1):
  b=self.f.read(n);self.h.update(b);self.size+=len(b);return b
 def close(self):pass
def safe(s):
 p=PurePosixPath(s);assert s and not p.is_absolute() and '..'not in p.parts and '\\'not in s;return p
sha=lambda b:hashlib.sha256(b).hexdigest()
def verify(folder,extract=None):
 index=json.loads((folder/'INDEX.json').read_text());h=hashlib.sha256();total=0
 # The full compressed file is optional; parts are the authoritative public objects.
 target=folder/'REASSEMBLED-VERIFIED.tar.xz'
 reuse=target.exists()
 if reuse:out=None
 else:out=target.open('xb')
 try:
  for row in index['parts']:
   b=(folder/str(safe(row['path']))).read_bytes();assert len(b)==row['bytes']and sha(b)==row['sha256'];h.update(b);total+=len(b)
   if out:out.write(b)
 finally:
  if out:out.close()
 assert h.hexdigest()==index['compressed_sha256']and total==index['compressed_bytes']
 hh=hashlib.sha256()
 with target.open('rb')as f:
  while b:=f.read(1024*1024):hh.update(b)
 assert hh.hexdigest()==index['compressed_sha256']
 if extract:extract.mkdir(parents=True,exist_ok=False)
 seen={};manifest=None
 with lzma.open(target,'rb')as f:
  reader=HashReader(f)
  with tarfile.open(fileobj=reader,mode='r|')as tar:
   for member in tar:
    path=safe(member.name);assert member.isfile() and member.name not in seen
    data=tar.extractfile(member).read();seen[member.name]={'path':member.name,'bytes':len(data),'sha256':sha(data)}
    if member.name=='CONTENTS.json':assert sha(data)==index['contents_manifest_sha256'];manifest=json.loads(data)
    if extract:
     p=extract/str(path);p.parent.mkdir(parents=True,exist_ok=True)
     with p.open('xb')as out:out.write(data)
  while reader.read(1024*1024):pass
  assert reader.h.hexdigest()==index['tar_sha256']and reader.size==index['tar_bytes']
 assert manifest is not None;seen.pop('CONTENTS.json');assert {r['path']:r for r in manifest['files']}==seen
 assert len(seen)==index['text_file_count']
 result={'status':'PASS_STREAMING_ARCHIVE_ROUNDTRIP','file_count':len(seen),'compressed_sha256':index['compressed_sha256'],'tar_sha256':index['tar_sha256'],'projection_not_raw_logs':index.get('projection_not_raw_logs',False)}
 print(json.dumps(result));return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('archive_directory',type=Path);p.add_argument('--extract',type=Path);a=p.parse_args();verify(a.archive_directory,a.extract)
