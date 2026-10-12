"""Audit-only FIFO transport. No proof source or compiler flag is changed.
A failed/interrupted attempt never produces an admitted complete archive.
"""
from pathlib import Path
import gzip,hashlib,json,os,selectors,signal,stat,subprocess,time,zlib
CHUNK=1024*1024
MAX_RAW=512*2**20
sha=lambda b:hashlib.sha256(b).hexdigest()
def require(x,msg):
 if not x:raise ValueError(msg)
def fsyncdir(p):
 f=os.open(p,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(f)
 finally:os.close(f)
def save(p,x):
 with p.open('x') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 fsyncdir(p.parent)
def digest_file(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(CHUNK):h.update(b);n+=len(b)
 return h.hexdigest(),n
def read_bytes(meta):
 require(meta.get('status')=='COMPLETE_VERIFIED_AUDIT_BYTES','unadmitted audit transport')
 a=Path(meta['archive_path']);require(not a.is_symlink() and a.is_file(),'missing/symlink audit archive')
 h,n=digest_file(a);require(h==meta['gzip_sha256'] and n==meta['gzip_bytes'],'compressed audit identity mismatch')
 require(0<meta['raw_bytes']<=MAX_RAW,'invalid raw length')
 out=bytearray()
 with gzip.open(a,'rb') as f:
  while b:=f.read(CHUNK):
   out.extend(b);require(len(out)<=meta['raw_bytes'],'raw bound exceeded')
 require(len(out)==meta['raw_bytes'] and sha(out)==meta['raw_sha256'],'raw audit identity mismatch')
 return bytes(out)
def capture(cmd,work,env,out,err,seconds):
 """Call only for the unchanged OwnedAudit source in a new isolated work dir."""
 work=Path(work);fifo=work/'AUDIT-RESULT.json';partial=work/'AUDIT-RESULT.partial.gz';archive=work/'AUDIT-RESULT.json.gz';mp=work/'AUDIT-TRANSPORT.json'
 require(all(not p.exists() and not p.is_symlink() for p in [fifo,partial,archive,mp]),'audit output path already exists')
 require(isinstance(cmd,list) and cmd[-1]=='OwnedAudit.lean' and (work/'OwnedAudit.lean').is_file(),'not an OwnedAudit invocation')
 require(0<seconds<=300,'audit timeout exceeds inherited cap')
 os.mkfifo(fifo,0o600);inode=fifo.stat().st_ino;reader=os.open(fifo,os.O_RDONLY|os.O_NONBLOCK);guard=os.open(fifo,os.O_WRONLY|os.O_NONBLOCK);sel=selectors.DefaultSelector();sel.register(reader,selectors.EVENT_READ)
 process=None;h=hashlib.sha256();count=0;started=time.monotonic();code=None;failure=None;complete=False;raw=None;gz=None;last_checkpoint=0
 def checkpoint():
  nonlocal last_checkpoint
  gz.flush(zlib.Z_SYNC_FLUSH);raw.flush();os.fsync(raw.fileno());gh,gn=digest_file(partial)
  with (work/'AUDIT-STREAM-CHECKPOINTS.jsonl').open('a') as f:
   f.write(json.dumps({'status':'DURABLE_PREFIX_NOT_ACCEPTED','raw_prefix_bytes':count,'raw_prefix_sha256':h.hexdigest(),'gzip_prefix_bytes':gn,'gzip_prefix_sha256':gh})+'\n');f.flush();os.fsync(f.fileno())
  fsyncdir(work);last_checkpoint=count
 try:
  raw=partial.open('xb');gz=gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0);checkpoint()
  save(work/'AUDIT-STREAM-START.json',{'status':'STARTED_NOT_ACCEPTED','command':cmd,'source_sha256':sha((work/'OwnedAudit.lean').read_bytes()),'raw_path':str(fifo),'fifo_inode':inode,'cap_seconds':seconds,'raw_limit_bytes':MAX_RAW})
  process=subprocess.Popen(cmd,cwd=work,env=env,stdout=out,stderr=err)
  while True:
   if time.monotonic()-started>seconds:raise TimeoutError('audit capture deadline')
   code=process.poll()
   if code is not None and guard is not None:os.close(guard);guard=None
   ready=sel.select(0.05)
   if ready:
    try:b=os.read(reader,CHUNK)
    except BlockingIOError:continue
    if b:
     require(count+len(b)<=MAX_RAW,'raw audit exceeds unchanged per-file cap');count+=len(b);h.update(b);gz.write(b)
     if count-last_checkpoint>=8*CHUNK:checkpoint()
    elif code is not None:break
   elif code is not None:
    try:b=os.read(reader,CHUNK)
    except BlockingIOError:continue
    if b:
     require(count+len(b)<=MAX_RAW,'raw audit exceeds unchanged per-file cap');count+=len(b);h.update(b);gz.write(b)
     if count-last_checkpoint>=8*CHUNK:checkpoint()
    else:break
  gz.close();gz=None;raw.flush();os.fsync(raw.fileno());raw.close();raw=None;fsyncdir(work)
  require(code==0,'audit process did not exit zero')
  gh,gn=digest_file(partial)
  meta={'status':'COMPLETE_VERIFIED_AUDIT_BYTES','raw_path':str(fifo),'raw_sha256':h.hexdigest(),'raw_bytes':count,'archive_path':str(partial),'gzip_sha256':gh,'gzip_bytes':gn,'child_exit_code':code,'eof_after_child_exit':True,'raw_limit_bytes':MAX_RAW,'cap_seconds':seconds,'capture_seconds':time.monotonic()-started,'audit_source_unchanged':True}
  b=read_bytes(meta);j=json.loads(b);require(isinstance(j,dict) and isinstance(j.get('declarations'),list) and isinstance(j.get('selected_modules'),list),'invalid audit JSON schema')
  require(j['declaration_count']==len(j['declarations']),'audit declaration count mismatch')
  # Existing target validation still checks exact selected order and all axioms.
  os.link(partial,archive);fsyncdir(work);partial.unlink();fsyncdir(work);meta['archive_path']=str(archive);save(mp,meta);complete=True
  return code,meta
 except Exception as ex:
  failure=type(ex).__name__+': '+str(ex)
  if process is not None and process.poll() is None:
   process.terminate()
   try:process.wait(timeout=10)
   except subprocess.TimeoutExpired:process.kill();process.wait()
  code=process.returncode if process is not None else None
  return 124 if isinstance(ex,TimeoutError) else (code if code not in [0,None] else 125),None
 finally:
  if process is not None and process.poll() is None:
   process.terminate()
   try:process.wait(timeout=10)
   except subprocess.TimeoutExpired:process.kill();process.wait()
  if gz is not None:gz.close()
  if raw is not None:raw.flush();os.fsync(raw.fileno());raw.close()
  if guard is not None:os.close(guard)
  sel.close();os.close(reader)
  require(fifo.is_fifo() and fifo.stat().st_ino==inode,'audit FIFO identity changed')
  fifo.unlink();fsyncdir(work)
  if not complete:save(work/'AUDIT-STREAM-FAILED.json',{'status':'FAILED_PARTIAL_NEVER_ADMITTED','error':failure,'child_exit_code':code,'raw_prefix_sha256':h.hexdigest(),'raw_prefix_bytes':count,'partial_archive':str(partial),'retained_archives':[{ 'path':str(p),'sha256':digest_file(p)[0],'bytes':digest_file(p)[1]} for p in [partial,archive] if p.is_file()],'elapsed_seconds':time.monotonic()-started})

def recover_durable_prefix(work):
 """Read-only failed/interrupted evidence recovery; never confers acceptance."""
 work=Path(work);log=work/'AUDIT-STREAM-CHECKPOINTS.jsonl';require(log.is_file() and not log.is_symlink(),'missing checkpoint log');rows=[]
 for line in log.read_bytes().splitlines():
  try:rows.append(json.loads(line))
  except json.JSONDecodeError:break # incomplete final journal write remains preserved
 require(rows,'no durable checkpoint')
 p=work/'AUDIT-RESULT.partial.gz';require(p.is_file() and not p.is_symlink(),'missing partial archive')
 e=rows[-1];require(e['status']=='DURABLE_PREFIX_NOT_ACCEPTED' and 0<=e['raw_prefix_bytes']<=MAX_RAW,'invalid prefix checkpoint')
 with p.open('rb') as f:z=f.read(e['gzip_prefix_bytes'])
 require(len(z)==e['gzip_prefix_bytes'] and sha(z)==e['gzip_prefix_sha256'],'gzip prefix mismatch')
 dec=zlib.decompressobj(16+zlib.MAX_WBITS);b=dec.decompress(z,MAX_RAW+1)
 require(len(b)==e['raw_prefix_bytes'] and sha(b)==e['raw_prefix_sha256'],'raw prefix mismatch')
 return b,e
