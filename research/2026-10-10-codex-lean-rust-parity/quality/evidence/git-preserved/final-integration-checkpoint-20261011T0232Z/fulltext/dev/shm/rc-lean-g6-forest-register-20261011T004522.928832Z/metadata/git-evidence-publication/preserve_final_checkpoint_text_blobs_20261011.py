"""Publish a frozen, bounded final metadata set as full regular Git blobs."""
import os,json,pathlib,subprocess,hashlib,datetime
R=pathlib.Path('/workspace/Research-Commons')
B=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
O=pathlib.Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z')
I=pathlib.Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
E={**os.environ,'GIT_OBJECT_DIRECTORY':str(O),'GIT_ALTERNATE_OBJECT_DIRECTORIES':str(R/'.git/objects'),'GIT_INDEX_FILE':str(I),'GIT_OPTIONAL_LOCKS':'0'}
M=B/'FINAL-CHECKPOINT-FULLTEXT-MANIFEST.json'
OUT=B/'FINAL-CHECKPOINT-FULLTEXT-PUBLICATION.json'
def git(*a,data=None):return subprocess.check_output(['git',*a],cwd=R,env=E,input=data)
def sha(b):return hashlib.sha256(b).hexdigest()
def free(p):s=os.statvfs(p);return s.f_bavail*s.f_frsize
def pool():return sum(p.stat().st_size for p in O.rglob('*') if p.is_file())
def allocation(roots):
 seen=set();n=0
 for root in roots:
  for d,ds,fs in os.walk(root):
   for p in [pathlib.Path(d),*(pathlib.Path(d)/f for f in fs)]:
    s=p.lstat();k=(s.st_dev,s.st_ino)
    if k not in seen:seen.add(k);n+=s.st_blocks*512
 return n
def main():
 assert not OUT.exists()
 data=M.read_bytes();j=json.loads(data);rows=[dict(x) for x in j['files']]
 assert sha(pathlib.Path(__file__).read_bytes())==j['publisher_sha256']
 rows.append({'source_path':str(M),'git_tree_path':j['prefix']+'/INPUT-MANIFEST.json','sha256':sha(data),'bytes':len(data)})
 assert 30<=len(rows)<=100 and len({x['git_tree_path'] for x in rows})==len(rows)
 before=git('ls-files','--stage','-z')
 existing={x.split(b'\t',1)[1] for x in before.split(b'\0') if x}
 for row in rows:
  p=pathlib.Path(row['source_path']);assert p.is_file() and not p.is_symlink()
  b=p.read_bytes();b.decode('utf-8');assert not b.startswith(b'\x7fELF')
  assert len(b)==row['bytes'] and sha(b)==row['sha256']
  assert row['git_tree_path'].encode() not in existing and not (R/row['git_tree_path']).exists()
  row['git_blob']=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 payload=sum(x['bytes'] for x in rows);assert payload<6*1024**2
 config=json.loads(pathlib.Path(j['resource_config']).read_bytes())
 assert len(config['allocation_roots'])==26
 allocated=allocation(config['allocation_roots']);mem=dict(x.split() for x in pathlib.Path('/sys/fs/cgroup/memory.stat').read_text().splitlines());nr=sum(int(mem[x]) for x in ['anon','shmem','kernel'])
 reserve=payload+len(rows)*4096+4*1024**2
 assert pool()+reserve<96*1024**2
 assert allocated+reserve<config['scratch_abort_bytes']
 assert nr<config['memory_abort_bytes'] and config['scratch_abort_bytes']==2013265920
 assert config['scratch_hard_limit_bytes']==2147483648 and config['memory_abort_bytes']==16106127360
 assert free('/tmp')>I.stat().st_size+2*1024**2 and free('/workspace')>8*1024**2
 resource={'pool_bytes':pool(),'distinct_allocated_bytes':allocated,'nonreclaimable_bytes':nr,'tmp_free_bytes':free('/tmp'),'overlay_free_bytes':free('/workspace'),'future_tree_reserve_bytes':4*1024**2,'global_caps_unchanged':True}
 for row in rows:
  b=pathlib.Path(row['source_path']).read_bytes();assert sha(b)==row['sha256']
  blob=git('hash-object','-w','--stdin',data=b).decode().strip();assert blob==row['git_blob'];assert git('cat-file','blob',blob)==b
 updates=b''.join(('100644 '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in rows)
 git('update-index','-z','--index-info',data=updates)
 git('update-index','--skip-worktree','--',*(x['git_tree_path'] for x in rows))
 current=git('ls-files','--stage','-z');added={x['git_tree_path'].encode() for x in rows}
 assert b''.join(x+b'\0' for x in current.split(b'\0') if x and x.split(b'\t',1)[1] not in added)==before
 for row in rows:
  assert git('ls-files','-v','--',row['git_tree_path']).decode().startswith('S ')
  assert git('show',':'+row['git_tree_path'])==pathlib.Path(row['source_path']).read_bytes()
 assert pool()<96*1024**2 and allocation(config['allocation_roots'])<config['scratch_abort_bytes']
 assert free('/workspace')>8*1024**2
 receipt={'status':'PASS_FULL_FROZEN_METADATA_BYTES_INDEXED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_path':str(M),'manifest_sha256':sha(data),'publisher_sha256':j['publisher_sha256'],'files':rows,'files_count':len(rows),'payload_bytes':payload,'all_full_git_blob_readbacks':True,'all_preexisting_index_entries_exact':True,'regular_100644_stage0_sparse_only_new_metadata':True,'no_original_evidence_deleted_hidden_or_modified':True,'no_compiler_native_cache_or_kernel_acceptance':True,'before_resource':resource,'after_pool_bytes':pool(),'remote_publication_not_yet_checked':True}
 OUT.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'receipt':str(OUT),'sha256':sha(OUT.read_bytes()),'files':len(rows),'payload_bytes':payload,'pool_bytes':pool()}))
if __name__=='__main__':main()
