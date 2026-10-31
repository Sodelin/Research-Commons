#!/usr/bin/env python3
"""Deterministic immutable Git-tree inventory and deduplicated UTF-8 body shards."""
import argparse,collections,gzip,hashlib,json,pathlib,subprocess,os
ROOTS=['research','handoffs','communications']
DEPENDENCIES={'.git','.lake','node_modules','__pycache__','target'}
BINARY={'.gz','.xz','.zip','.tar','.pdf','.png','.jpg','.jpeg','.gif','.webp','.olean','.private','.server','.ir','.sig','.pyc','.wasm','.so','.a','.bin','.b64'}
def digest(b):return hashlib.sha256(b).hexdigest()
def encode(x):return (json.dumps(x,ensure_ascii=False,separators=(',',':'))+'\n').encode()
def read_manifest(index):
 path=index/'manifest.json'
 return json.loads(path.read_bytes() if path.exists() else gzip.decompress((index/'manifest.json.gz').read_bytes()))
def build(repo,commit,output,base=None):
 def git(*a):return subprocess.check_output(['git','-C',str(repo),*a])
 origin=git('remote','get-url','origin').decode().strip()
 if origin not in ['https://github.com/Sodelin/Research-Commons.git','https://github.com/Sodelin/Research-Commons','git@github.com:Sodelin/Research-Commons.git']:raise ValueError('Unsupported repository origin')
 pin=git('rev-parse',commit+'^{commit}').decode().strip();assert len(pin)==40
 prior=read_manifest(base) if base else None
 prior_rows={r['path']:r for r in prior['inventory']} if prior else {}
 tree=git('ls-tree','-rlz','--full-tree',pin,*ROOTS);inventory=[];groups=collections.defaultdict(list);retained_paths=set()
 for raw in tree.split(b'\0'):
  if not raw:continue
  meta,path=raw.split(b'\t',1);mode,kind,blob,size=meta.decode().split();path=path.decode();row={'path':path,'git_blob':blob,'bytes':int(size) if size!='-' else None};inventory.append(row)
  reason='nonregular Git entry' if mode not in ['100644','100755'] or kind!='blob' else 'dependency/cache subtree' if set(path.split('/'))&DEPENDENCIES else 'binary/archive representation' if pathlib.PurePosixPath(path).suffix.lower() in BINARY else 'body exceeds 16MiB' if int(size)>16*1024*1024 else None
  old=prior_rows.get(path)
  if old and old['git_blob']==blob and old['bytes']==row['bytes'] and (reason==old.get('reason') or reason is None and (old['coverage']=='full_text' or old.get('reason')=='non-UTF8 or NUL-containing body')):
   row.update(old);retained_paths.add(path);continue
  if reason:row.update(coverage='path_only',reason=reason)
  else:groups[blob].append(row)
 obsolete_paths=set(prior_rows)-retained_paths
 current_paths={r['path'] for r in inventory}
 delta={'added_paths':len(current_paths-set(prior_rows)), 'changed_paths':len((current_paths & set(prior_rows))-retained_paths), 'removed_paths':len(set(prior_rows)-current_paths)} if prior else None
 output.mkdir(parents=True,exist_ok=False);shards=list(prior['shards']) if prior else [];documents=[];total=0
 if prior:
  for shard in shards:
   source=base/shard['path'];packed=source.read_bytes();assert digest(packed)==shard['sha256']
   payload=json.loads(gzip.decompress(packed));old_docs=payload['documents']
   if not any(obsolete_paths.intersection(doc['source_paths']) for doc in old_docs):
    os.link(source,output/shard['path']);continue
   # Rewrite only affected shards. Prior immutable caches and their bodies stay
   # untouched; obsolete aliases cannot resolve to stale bytes in this view.
   kept=[]
   for doc in old_docs:
    paths=[path for path in doc['source_paths'] if path not in obsolete_paths]
    if not paths:continue
    if paths!=doc['source_paths']:
     if doc['title'] in doc['source_paths']:doc['title']=paths[0]
     doc['source_paths']=paths
     doc['bindings']=[{'role':'published_source_body_status_not_inferred','label':' '.join(paths)}]
    kept.append(doc)
   packed=gzip.compress(encode({'schema':1,'documents':kept}),mtime=0)
   (output/shard['path']).write_bytes(packed)
   shard.update(sha256=digest(packed),documents=len(kept),body_bytes=sum(doc['bytes'] for doc in kept))
 def flush():
  nonlocal documents,total
  if not documents:return
  data=encode({'schema':1,'documents':documents});packed=gzip.compress(data,mtime=0);name=f'bodies-{len(shards):04d}.json.gz';(output/name).write_bytes(packed);shards.append({'path':name,'sha256':digest(packed),'documents':len(documents),'body_bytes':total});documents=[];total=0
 proc=subprocess.Popen(['git','-C',str(repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for blob,rows in sorted(groups.items()):
  proc.stdin.write((blob+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().decode().split();assert header[:2]==[blob,'blob'];size=int(header[2]);body=proc.stdout.read(size);assert len(body)==size and proc.stdout.read(1)==b'\n';assert hashlib.sha1(f'blob {size}\0'.encode()+body).hexdigest()==blob
  try:
   text=body.decode('utf-8');assert '\0' not in text
  except (UnicodeDecodeError,AssertionError):
   for row in rows:row.update(coverage='path_only',reason='non-UTF8 or NUL-containing body')
   continue
  if total+size>8*1024*1024:flush()
  shard=f'bodies-{len(shards):04d}.json.gz';paths=[r['path'] for r in rows];url=f'https://github.com/Sodelin/Research-Commons/blob/{pin}/{paths[0]}'
  for row in rows:row.update(coverage='full_text',sha256=digest(body),shard=shard,document_url=url)
  documents.append({'url':url,'title':next((line[2:] for line in text.splitlines() if line.startswith('# ')),paths[0]),'body':text,'bytes':size,'sha256':digest(body),'git_blob':blob,'source_paths':paths,'bindings':[{'role':'published_source_body_status_not_inferred','label':' '.join(paths)}]});total+=size
 proc.stdin.close();assert proc.wait()==0;flush()
 manifest={'schema':1,'source_commits':list(dict.fromkeys((prior.get('source_commits',[prior['commit']]) if prior else [])+[pin])),'repository':'Sodelin/Research-Commons','commit':pin,'roots':ROOTS,'incremental_delta':delta,'git_tree_inventory_sha256':digest(tree),'coverage':{'paths':len(inventory),'full_text_paths':sum(r['coverage']=='full_text' for r in inventory),'path_only_paths':sum(r['coverage']=='path_only' for r in inventory),'unique_text_bodies':len({r['git_blob'] for r in inventory if r['coverage']=='full_text'}),'indexed_documents':sum(s['documents'] for s in shards)},'limitation':'Published tree at the exact pin only; no private tasks, deleted historical commits or linked external repositories. Path-only reasons are explicit. Authorship, review, Lean, execution, novelty and supersession must be read from the original source; no acceptance is inferred. Generated local CLI index is not a deployed website refresh.','shards':shards,'inventory':inventory};(output/'manifest.json').write_bytes(encode(manifest));print(json.dumps({'commit':pin,'coverage':manifest['coverage'],'shards':len(shards)}))
def check(repo,index,expected):
 m=read_manifest(index);raw=subprocess.check_output(['git','-C',str(repo),'ls-tree','-rlz','--full-tree',m['commit'],*m['roots']]);assert digest(raw)==m['git_tree_inventory_sha256'],'tree differs';current=subprocess.check_output(['git','-C',str(repo),'ls-tree','-rlz','--full-tree',expected,*m['roots']]);assert digest(current)==m['git_tree_inventory_sha256'],'Published research changed: rebuild the index before claiming freshness';expected={r['path'] for r in m['inventory']};actual={r.split(b'\t',1)[1].decode() for r in raw.split(b'\0') if r};assert expected==actual and len(expected)==len(m['inventory']);seen={}
 for shard in m['shards']:
  data=(index/shard['path']).read_bytes();assert digest(data)==shard['sha256'];docs=json.loads(gzip.decompress(data))['documents'];assert len(docs)==shard['documents']
  for d in docs:
   b=d['body'].encode();assert digest(b)==d['sha256'] and len(b)==d['bytes'] and hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==d['git_blob']
   for path in d['source_paths']:assert path not in seen;seen[path]=(d['git_blob'],d['sha256'],shard['path'])
 original={}
 for r in raw.split(b'\0'):
  if r:
   meta,path=r.split(b'\t',1);fields=meta.decode().split();original[path.decode()]=(fields[2],int(fields[3]) if fields[3]!='-' else None)
 for row in m['inventory']:
  assert (row['git_blob'],row['bytes'])==original[row['path']]
  if row['coverage']=='full_text':assert seen[row['path']]==(row['git_blob'],row['sha256'],row['shard'])
  else:assert row['reason']
 assert len(seen)==m['coverage']['full_text_paths'];print(json.dumps({'verified':True,'commit':m['commit'],'coverage':m['coverage']}))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--repo',type=pathlib.Path,default=pathlib.Path('.'));p.add_argument('--commit',default='HEAD');p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--check',action='store_true');p.add_argument('--base',type=pathlib.Path);a=p.parse_args();check(a.repo,a.output,a.commit) if a.check else build(a.repo,a.commit,a.output,a.base)
