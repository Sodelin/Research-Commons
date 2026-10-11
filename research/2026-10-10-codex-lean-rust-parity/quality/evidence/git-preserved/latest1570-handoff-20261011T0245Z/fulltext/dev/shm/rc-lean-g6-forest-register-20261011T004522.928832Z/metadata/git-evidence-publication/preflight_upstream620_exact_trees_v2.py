import os,pathlib,subprocess,json,hashlib,zlib,datetime
R=pathlib.Path('/workspace/Research-Commons')
B=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
E={**os.environ,'GIT_OBJECT_DIRECTORY':'/tmp/rc-cloud-git-objects-20261010T223739.438030Z','GIT_ALTERNATE_OBJECT_DIRECTORIES':str(R/'.git/objects'),'GIT_INDEX_FILE':'/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT','GIT_OPTIONAL_LOCKS':'0'}
def git(*a,data=None):return subprocess.check_output(['git',*a],cwd=R,env=E,input=data)
def sha(b):return hashlib.sha256(b).hexdigest()
def tree_of(entries):
 trie={}
 for p,v in entries.items():
  t=trie;parts=p.split(b'/')
  for name in parts[:-1]:t=t.setdefault(name,{})
  assert parts[-1] not in t;t[parts[-1]]=v
 trees=[]
 def visit(t):
  items=[]
  for n,v in t.items():
   if isinstance(v,dict):blob=visit(v);items.append((n,b'40000',blob,True))
   else:mode,blob=v;items.append((n,mode.encode(),blob,False))
  data=b''.join(mode+b' '+n+b'\0'+bytes.fromhex(blob) for n,mode,blob,isdir in sorted(items,key=lambda x:x[0]+(b'/' if x[3] else b'')))
  full=b'tree '+str(len(data)).encode()+b'\0'+data;blob=hashlib.sha1(full).hexdigest();trees.append({'git_object':blob,'uncompressed_bytes':len(data),'compressed_level6_bytes':len(zlib.compress(full,6))});return blob
 return visit(trie),trees
def main():
 out=B/'UPSTREAM-62020166-EXACT-BYTE-PREFLIGHT-V2.json';assert not out.exists()
 old='de4d8fa1b3c56997df1b2a2e07b4ebc6e237ef6d';new='62020166e3e7ef690838f50b13caa149ede419ec'
 d=git('diff','--name-status','-z',old,new).split(b'\0');assert d[-1]==b'';changes=[]
 for i in range(0,len(d)-1,2):
  status=d[i].decode();p=d[i+1].decode();assert status in ['A','M'];assert status=='A' or p=='research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md';changes.append((status,p))
 change_by_path={p:s for s,p in changes}
 raw=git('ls-files','--stage','-z');entries={}
 for item in raw.split(b'\0'):
  if item:
   attr,p=item.split(b'\t',1);mode,blob,stage=attr.decode().split();assert stage=='0';entries[p]=(mode,blob)
 current_tree,_=tree_of(entries);assert current_tree=='cb1a2771a31637f8a411f7584848d237fd3f601c'
 up=git('ls-tree','-r','-z',new,'--',*(p for s,p in changes));rows=[]
 for item in up.split(b'\0'):
  if not item:continue
  attr,p=item.split(b'\t',1);mode,kind,blob=attr.decode().split();assert mode=='100644' and kind=='blob';p=p.decode();status=change_by_path[p];data=git('cat-file','blob',blob)
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob
  if status=='A':assert p.encode() not in entries and not (R/p).exists()
  else:
   om,ob=entries[p.encode()];before=git('cat-file','blob',ob);assert (R/p).read_bytes()==before and git('show',old+':'+p)==before
  rows.append({'status':status,'git_tree_path':p,'git_blob':blob,'mode':mode,'bytes':len(data),'sha256':sha(data)})
  entries[p.encode()]=(mode,blob)
 assert len(rows)==len(changes)
 future_tree,trees=tree_of(entries);checks=git('cat-file','--batch-check=%(objectname) %(objecttype) %(objectsize)',data=('\n'.join(x['git_object'] for x in trees)+'\n').encode()).decode().splitlines();missing=[x for x,c in zip(trees,checks) if c.endswith(' missing')]
 j={'status':'PASS_READONLY_EXACT_UPSTREAM_BYTES_AND_PREDICTED_TREE','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reader_sha256':sha(pathlib.Path(__file__).read_bytes()),'from':old,'to':new,'rows':rows,'files_count':len(rows),'new_files':sum(x['status']=='A' for x in rows),'modified_files':sum(x['status']=='M' for x in rows),'old_live_scope_equals_old_index_and_base':True,'all_git_blob_fullbytes_authenticated':True,'no_git_or_tree_mutation':True,'current_tree_prediction_matches_exact_prior_git_write_tree':current_tree,'future_tree_without_ordinary_notes':future_tree,'missing_trees':missing,'missing_tree_count':len(missing),'predicted_new_tree_content_bytes':sum(x['compressed_level6_bytes'] for x in missing),'future_full_entries':len(entries),'own_initial_failure_preserved':'UPSTREAM-62020166-PREFLIGHT-ATTEMPT1-OWN-READER-FAILURE.json'}
 out.write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({'path':str(out),'sha256':sha(out.read_bytes()),'files':len(rows),'new':j['new_files'],'modified':j['modified_files'],'future_tree':future_tree,'new_tree_objects':len(missing),'new_tree_bytes':j['predicted_new_tree_content_bytes']}))
if __name__=='__main__':main()
