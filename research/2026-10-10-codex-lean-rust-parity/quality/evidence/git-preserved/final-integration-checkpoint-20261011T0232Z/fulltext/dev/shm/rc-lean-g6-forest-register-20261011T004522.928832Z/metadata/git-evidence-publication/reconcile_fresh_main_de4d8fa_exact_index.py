import os,json,pathlib,subprocess,hashlib,datetime
R=pathlib.Path('/workspace/Research-Commons')
B=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
E={**os.environ,'GIT_OBJECT_DIRECTORY':'/tmp/rc-cloud-git-objects-20261010T223739.438030Z','GIT_ALTERNATE_OBJECT_DIRECTORIES':str(R/'.git/objects'),'GIT_INDEX_FILE':'/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT','GIT_OPTIONAL_LOCKS':'0'}
OLD='f8120b1e413b64303891f7f2f8007169856c03f3'
NEW='de4d8fa1b3c56997df1b2a2e07b4ebc6e237ef6d'
OUT=B/'FRESH-MAIN-DE4D8FA-EXACT-INDEX-INTEGRATION.json'
def git(*a,data=None):return subprocess.check_output(['git',*a],cwd=R,env=E,input=data)
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 assert not OUT.exists()
 assert git('merge-base',OLD,NEW).decode().strip()==OLD
 raw=git('diff','--name-status','-z',OLD,NEW).split(b'\0')
 assert raw[-1]==b''
 paths=[]
 for i in range(0,len(raw)-1,2):
  assert raw[i]==b'A',raw[i]
  paths.append(raw[i+1].decode())
 assert len(paths)==300 and len(set(paths))==300
 pre=git('ls-files','--stage','-z')
 existing={x.split(b'\t',1)[1] for x in pre.split(b'\0') if x}
 assert not (set(x.encode() for x in paths)&existing)
 assert all(not (R/p).exists() for p in paths)
 entries=git('ls-tree','-r','-z',NEW,'--',*paths)
 rows=[]
 for item in entries.split(b'\0'):
  if not item:continue
  attrs,p=item.split(b'\t',1);mode,kind,blob=attrs.decode().split();p=p.decode()
  assert mode=='100644' and kind=='blob'
  b=git('cat-file','blob',blob)
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
  rows.append({'git_tree_path':p,'git_blob':blob,'mode':mode,'bytes':len(b),'sha256':sha(b)})
 assert set(x['git_tree_path'] for x in rows)==set(paths)
 idx=pathlib.Path(E['GIT_INDEX_FILE']);tmp=os.statvfs('/tmp');over=os.statvfs('/workspace')
 assert tmp.f_bavail*tmp.f_frsize>idx.stat().st_size+2*1024**2
 assert over.f_bavail*over.f_frsize>8*1024**2
 data=b''.join((x['mode']+' '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in rows)
 git('update-index','-z','--index-info',data=data)
 git('update-index','--skip-worktree','--',*paths)
 current=git('ls-files','--stage','-z');added={x.encode() for x in paths}
 filtered=b''.join(x+b'\0' for x in current.split(b'\0') if x and x.split(b'\t',1)[1] not in added)
 assert filtered==pre
 for row in rows:
  assert git('ls-files','-v','--',row['git_tree_path']).decode().startswith('S ')
  assert sha(git('show',':'+row['git_tree_path']))==row['sha256']
 receipt={'status':'PASS_EXACT_UPSTREAM_ADDITIONS_INDEXED_REGULAR_BLOBS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'upstream_from':OLD,'upstream_to':NEW,'source_reader_sha256':sha(pathlib.Path(__file__).read_bytes()),'files_count':len(rows),'files':rows,'old_index_entries_identical':True,'original_bytes_read_back':True,'sparse_new_files':300,'working_tree_copies_created':0,'new_compiler_or_kernel_acceptance':False,'g4_selected219_is_separate_from_accepted1568':True,'existing_files_hidden_moved_or_deleted':False,'index_bytes':idx.stat().st_size,'current_index_entries':len([x for x in current.split(b'\0') if x])}
 OUT.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({'receipt':str(OUT),'sha256':sha(OUT.read_bytes()),'files':len(rows),'payload_bytes':sum(x['bytes'] for x in rows),'index_bytes':idx.stat().st_size}))
if __name__=='__main__':main()
