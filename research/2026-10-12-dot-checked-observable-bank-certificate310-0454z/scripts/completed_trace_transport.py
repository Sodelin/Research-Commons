"""Lossless transport of completed PASS loader traces; never active or failed traces."""
from pathlib import Path
import gzip,hashlib,json,os,time
_verified={}
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def restored(p):
 h=hashlib.sha256();n=0
 with gzip.open(p,'rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
def identity(p):
 s=p.stat();return (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
def save(p,d):
 tmp=p.with_name(p.name+'.tmp')
 with tmp.open('w') as f:f.write(json.dumps(d,indent=2)+'\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,p)
 fd=os.open(p.parent,os.O_RDONLY)
 try:os.fsync(fd)
 finally:os.close(fd)
def validate(root,entry,force=False):
 raw=root/entry['raw_path'];archive=root/entry['archive_path']
 assert raw.resolve().is_relative_to(root.resolve()) and archive.resolve().is_relative_to(root.resolve())
 assert archive.is_file(),('MISSING_ARCHIVE',archive)
 receipt=root/entry['receipt_path']
 assert receipt.resolve().is_relative_to(root.resolve()/'.build/runs')
 assert sha(receipt)==entry['receipt_sha256'],('RECEIPT_BINDING_DRIFT',receipt)
 r=json.loads(receipt.read_text())
 assert r.get('status')=='PASS_FRESH_KERNEL_CHECK' and r.get('exit_code')==0 and r.get('source_and_imports_stable') is True
 assert raw.resolve().is_relative_to(receipt.parent.resolve()) and raw.name.startswith('NATIVE-LOADER.')
 assert any(Path(x['path']).resolve()==raw.resolve() and x['sha256']==entry['raw_sha256'] for x in r.get('native_loader_outputs',[])),('DETACHED_TRACE_MAPPING',raw)
 ident=identity(archive);key=(str(archive),entry['raw_sha256'],entry['archive_sha256'],entry['raw_bytes'])
 if force or _verified.get(key)!=ident:
  assert sha(archive)==entry['archive_sha256'],('CORRUPT_ARCHIVE',archive)
  assert restored(archive)==(entry['raw_sha256'],entry['raw_bytes']),('RESTORED_BYTES_MISMATCH',archive)
  _verified[key]=ident
 if raw.exists():assert sha(raw)==entry['raw_sha256'],('RAW_COPY_DRIFT',raw)
 return True
def compress_completed(root,force=False):
 root=Path(root).resolve();folder=root/'trace-transport';folder.mkdir(exist_ok=True)
 index=folder/'INDEX.json';data=json.loads(index.read_text()) if index.exists() else {'schema':'completed_loader_trace_lossless_v1','entries':[]}
 for e in data['entries']:validate(root,e,force)
 known={e['raw_path'] for e in data['entries']}
 for receipt in sorted((root/'.build/runs').glob('*/attempts/*/receipt.json')):
  # Defer the current write window. Receipts are immutable after completed invocation.
  if not force and time.time()-receipt.stat().st_mtime<5:continue
  r=json.loads(receipt.read_text())
  if r.get('status')!='PASS_FRESH_KERNEL_CHECK' or r.get('exit_code')!=0:continue
  assert r.get('source_and_imports_stable') is True
  for spec in r.get('native_loader_outputs',[]):
   raw=Path(spec['path']).resolve();assert raw.is_relative_to(root/'.build/runs')
   assert raw.name.startswith('NATIVE-LOADER.')
   rel=str(raw.relative_to(root))
   if rel in known:continue
   assert raw.is_file(),('UNMAPPED_MISSING_COMPLETED_TRACE',raw)
   before=identity(raw);digest=sha(raw);assert digest==spec['sha256'],('RECEIPT_TRACE_MISMATCH',raw)
   out=folder/(hashlib.sha256(rel.encode()).hexdigest()+'.gz');assert not out.exists(),('UNMAPPED_ARCHIVE_EXISTS',out)
   tmp=out.with_suffix('.gz.tmp')
   with raw.open('rb') as src,tmp.open('wb') as target:
    with gzip.GzipFile(filename='',fileobj=target,mode='wb',mtime=0,compresslevel=6) as gz:
     for b in iter(lambda:src.read(1024*1024),b''):gz.write(b)
    target.flush();os.fsync(target.fileno())
   assert restored(tmp)==(digest,before[2]);assert identity(raw)==before
   os.replace(tmp,out)
   entry={'raw_path':rel,'raw_bytes':before[2],'raw_sha256':digest,'archive_path':str(out.relative_to(root)),'archive_bytes':out.stat().st_size,'archive_sha256':sha(out),'receipt_path':str(receipt.relative_to(root)),'receipt_sha256':sha(receipt),'receipt_status':'PASS_FRESH_KERNEL_CHECK','gzip_mtime':0,'all_original_bytes_recoverable':True}
   validate(root,entry,True);data['entries'].append(entry);save(index,data)
   # Only remove the redundant raw representation after full restoration proof and durable mapping.
   assert identity(raw)==before;raw.unlink();known.add(rel)
 return len(data['entries'])
if __name__=='__main__':
 import sys
 root=Path(sys.argv[1]);print(compress_completed(root,force=True))
