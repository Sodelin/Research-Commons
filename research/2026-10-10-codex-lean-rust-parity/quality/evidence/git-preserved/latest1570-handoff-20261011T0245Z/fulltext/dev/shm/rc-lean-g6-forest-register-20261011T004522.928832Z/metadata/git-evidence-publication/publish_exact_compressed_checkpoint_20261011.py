"""Preserve frozen text and upstream bytes with exact zlib6 object funding.

prepare is read-only to Git; apply requires independent review of the frozen gate.
The post-result/gate reserve is bounded separately to avoid recursive self hashes.
"""
import os, pathlib, subprocess, json, hashlib, zlib, stat, datetime, sys
R = pathlib.Path('/workspace/Research-Commons')
B = pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
O = pathlib.Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z')
I = pathlib.Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
C = pathlib.Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json')
E = {**os.environ, 'GIT_OBJECT_DIRECTORY': str(O), 'GIT_ALTERNATE_OBJECT_DIRECTORIES': str(R/'.git/objects'), 'GIT_INDEX_FILE': str(I), 'GIT_OPTIONAL_LOCKS': '0'}
M = B/'EXACT-COMPRESSED-CHECKPOINT-INPUTS.json'
G = B/'EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json'
OUT = B/'EXACT-COMPRESSED-CHECKPOINT-PUBLICATION.json'
U = B/'UPSTREAM-62020166-EXACT-BYTE-PREFLIGHT-V2.json'
HEAD = '2347f1c16bfaf649da33ef0a42d693b97f46a161'
NEW = '62020166e3e7ef690838f50b13caa149ede419ec'
NATIVE = pathlib.Path('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver')
NATIVE_SHA = '443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00'
CONFIG_SHA = '2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c'
POOL_LIMIT = 96*1024**2
LATE_BLOB_RESERVE = 192*1024
LATE_TREE_RESERVE = 128*1024
COMMIT_RESERVE = 16*1024
LATE_ALLOC_RESERVE = 2*1024**2
def git(*args, data=None):
    return subprocess.check_output(['git', '-c', 'core.looseCompression=6', '-c', 'gc.auto=0', *args], cwd=R, env=E, input=data)
def sha(b): return hashlib.sha256(b).hexdigest()
def dump(p,j):
    assert not p.exists(); p.write_text(json.dumps(j,indent=2)+'\n')
def free(p):
    s=os.statvfs(p); return s.f_bavail*s.f_frsize
def pool(): return sum(p.stat().st_size for p in O.rglob('*') if p.is_file())
def allocated(roots,follow=False):
    seen=set(); total=0
    for root in roots:
        for d,ds,fs in os.walk(root,followlinks=False):
            for p in [pathlib.Path(d),*(pathlib.Path(d)/f for f in fs)]:
                before=p.lstat(); s=p.stat() if follow and stat.S_ISLNK(before.st_mode) else before
                key=(s.st_dev,s.st_ino)
                if key not in seen: seen.add(key); total+=s.st_blocks*512
    return total
def metrics():
    cfgdata=C.read_bytes(); assert sha(cfgdata)==CONFIG_SHA
    c=json.loads(cfgdata); roots=c['allocation_roots']; assert len(roots)==26 and all(pathlib.Path(p).exists() for p in roots)
    assert (c['scratch_abort_bytes'],c['scratch_hard_limit_bytes'],c['memory_abort_bytes'])==(2013265920,2147483648,16106127360)
    assert any(O.resolve().is_relative_to(pathlib.Path(p).resolve()) for p in roots)
    mem=dict(x.split() for x in pathlib.Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
    a=allocated(roots);f=allocated(roots,True);nr=sum(int(mem[k]) for k in ('anon','shmem','kernel'))
    assert nr<c['memory_abort_bytes'] and max(a,f)<c['scratch_abort_bytes'] and pool()<POOL_LIMIT
    assert free('/tmp')>I.stat().st_size+2*1024**2 and free('/workspace')>8*1024**2
    assert sha(NATIVE.read_bytes())==NATIVE_SHA
    return {'pool_bytes':pool(),'guard_lstat_bytes':a,'conservative_followed_file_bytes':f,'nonreclaimable_bytes':nr,'tmp_free_bytes':free('/tmp'),'index_bytes':I.stat().st_size,'overlay_free_bytes':free('/workspace'),'resource_config_sha256':CONFIG_SHA,'ordered26_roots':roots,'native_sha256':NATIVE_SHA,'scratch_abort_bytes':c['scratch_abort_bytes'],'memory_abort_bytes':c['memory_abort_bytes']}
def index():
    raw=git('ls-files','--stage','-z');entries={}
    for x in raw.split(b'\0'):
        if x:
            attr,p=x.split(b'\t',1);mode,oid,stage=attr.decode().split();assert stage=='0';entries[p]=(mode,oid)
    return raw,entries
def trees(entries):
    trie={};saved={}
    for path,v in entries.items():
        t=trie;parts=path.split(b'/')
        for n in parts[:-1]:t=t.setdefault(n,{})
        assert parts[-1] not in t;t[parts[-1]]=v
    def visit(t):
        items=[]
        for n,v in t.items():
            if isinstance(v,dict):items.append((n,b'40000',visit(v),True))
            else:items.append((n,v[0].encode(),v[1],False))
        body=b''.join(mode+b' '+n+b'\0'+bytes.fromhex(oid) for n,mode,oid,dr in sorted(items,key=lambda x:x[0]+(b'/' if x[3] else b'')))
        raw=b'tree '+str(len(body)).encode()+b'\0'+body;oid=hashlib.sha1(raw).hexdigest();saved[oid]=(body,len(zlib.compress(raw,6)));return oid
    return visit(trie),saved
def missing(oids):
    oids=list(oids)
    if not oids:return set()
    lines=git('cat-file','--batch-check=%(objectname) %(objecttype) %(objectsize)',data=('\n'.join(oids)+'\n').encode()).decode().splitlines()
    assert len(lines)==len(oids);return {oid for oid,line in zip(oids,lines) if line.endswith(' missing')}
def blob_info(row):
    p=pathlib.Path(row['source_path']);assert p.is_file() and not p.is_symlink()
    b=p.read_bytes();b.decode('utf-8');assert not b.startswith(b'\x7fELF')
    assert len(b)==row['bytes'] and sha(b)==row['sha256']
    full=b'blob '+str(len(b)).encode()+b'\0'+b
    return {**row,'git_blob':hashlib.sha1(full).hexdigest(),'zlib6_content_bytes':len(zlib.compress(full,6))}
def inputs():
    mb=M.read_bytes();j=json.loads(mb);assert j['publisher_sha256']==sha(pathlib.Path(__file__).read_bytes())
    rows=[blob_info(x) for x in j['files']]
    rows.append(blob_info({'source_path':str(M),'git_tree_path':j['prefix']+'/INPUT-MANIFEST.json','bytes':len(mb),'sha256':sha(mb),'ordinary_working_file':False}))
    assert len({x['git_tree_path'] for x in rows})==len(rows)
    return j,rows
def upstream():
    data=U.read_bytes();assert sha(data)=='dc91c9f43ded02823d6254e8405fc42bb77e78849ba6220345c9ce504e832dce'
    j=json.loads(data);assert j['to']==NEW and len(j['rows'])==1642
    for x in j['rows']:
        b=git('cat-file','blob',x['git_blob']);assert len(b)==x['bytes'] and sha(b)==x['sha256'] and x['mode']=='100644'
    return j
def prepare():
    assert not G.exists() and git('rev-parse','HEAD').decode().strip()==HEAD
    j,rows=inputs();raw,entries=index();current,t=trees(entries);assert current=='cb1a2771a31637f8a411f7584848d237fd3f601c'
    up=upstream()
    for x in up['rows']:
        p=x['git_tree_path'].encode()
        if x['status']=='A':assert p not in entries and not (R/x['git_tree_path']).exists()
        else:assert (R/x['git_tree_path']).read_bytes()==git('cat-file','blob',entries[p][1])
        entries[p]=(x['mode'],x['git_blob'])
    upstream_tree,_=trees(entries);assert upstream_tree==up['future_tree_without_ordinary_notes']
    for x in rows:
        p=x['git_tree_path'].encode()
        if not x.get('ordinary_working_file'):assert p not in entries and not (R/x['git_tree_path']).exists()
        else:assert pathlib.Path(x['source_path'])==R/x['git_tree_path']
        entries[p]=('100644',x['git_blob'])
    future,ts=trees(entries);mb=missing(x['git_blob'] for x in rows);mt=missing(ts)
    unique={x['git_blob']:x for x in rows if x['git_blob'] in mb}
    blobbytes=sum(x['zlib6_content_bytes'] for x in unique.values());treebytes=sum(ts[o][1] for o in mt)
    # Loose file blocks plus one possible fanout directory per new object; conservative.
    filealloc=sum(((x['zlib6_content_bytes']+4095)//4096)*4096 for x in unique.values())+sum(((ts[o][1]+4095)//4096)*4096 for o in mt)
    objectalloc=filealloc+4096*(len(unique)+len(mt))+LATE_ALLOC_RESERVE
    contentfunding=blobbytes+treebytes+LATE_BLOB_RESERVE+LATE_TREE_RESERVE+COMMIT_RESERVE
    resources=metrics()
    assert resources['pool_bytes']+contentfunding<POOL_LIMIT
    assert max(resources['guard_lstat_bytes'],resources['conservative_followed_file_bytes'])+objectalloc<2013265920
    scope=next(x for x in up['rows'] if x['status']=='M')
    assert resources['overlay_free_bytes']>((scope['bytes']+4095)//4096)*4096+8*1024**2
    dump(G,{'status':'READY_EXACT_COMPRESSED_FIXED_CAP_GATE_REQUIRES_INDEPENDENT_REVIEW','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publisher_sha256':sha(pathlib.Path(__file__).read_bytes()),'input_manifest_sha256':sha(M.read_bytes()),'prior_index_sha256':sha(raw),'prior_head':HEAD,'upstream_cutoff':NEW,'upstream_preflight_sha256':sha(U.read_bytes()),'current_tree':current,'upstream_only_tree':upstream_tree,'future_frozen_tree':future,'missing_blob_objects':list(unique.values()),'missing_tree_objects':[{'git_object':o,'zlib6_content_bytes':ts[o][1]} for o in sorted(mt)],'exact_missing_blob_content_bytes':blobbytes,'exact_missing_tree_content_bytes':treebytes,'late_blob_reserve_bytes':LATE_BLOB_RESERVE,'late_tree_reserve_bytes':LATE_TREE_RESERVE,'commit_reserve_bytes':COMMIT_RESERVE,'complete_object_content_funding_bytes':contentfunding,'new_loose_files_dirs_and_late_alloc_funding_bytes':objectalloc,'resource':resources,'prefix':j['prefix'],'files_count_including_manifest':len(rows),'no_further_fetch_cap_raise_deletion_or_scientific_admission':True})
    print(json.dumps({'gate':str(G),'sha256':sha(G.read_bytes()),'known_blob_bytes':blobbytes,'known_tree_bytes':treebytes,'total_content_funding':contentfunding,'pool_after_bound':resources['pool_bytes']+contentfunding,'future_tree':future}))
def write_blob(x):
    b=pathlib.Path(x['source_path']).read_bytes();assert sha(b)==x['sha256']
    oid=git('hash-object','-w','--stdin',data=b).decode().strip();assert oid==x['git_blob'] and git('cat-file','blob',oid)==b
    path=O/oid[:2]/oid[2:]
    if path.exists():assert path.stat().st_size==x['zlib6_content_bytes']
def apply(review_path):
    assert not OUT.exists();gatebytes=G.read_bytes();g=json.loads(gatebytes)
    review=json.loads(pathlib.Path(review_path).read_bytes());assert review['status'].startswith('PASS') and review['funding_gate_sha256']==sha(gatebytes)
    assert g['publisher_sha256']==sha(pathlib.Path(__file__).read_bytes()) and g['input_manifest_sha256']==sha(M.read_bytes())
    before,oldentries=index();assert sha(before)==g['prior_index_sha256'] and git('rev-parse','HEAD').decode().strip()==HEAD
    j,rows=inputs();up=upstream();resource=metrics()
    assert resource['pool_bytes']+g['complete_object_content_funding_bytes']<POOL_LIMIT
    assert max(resource['guard_lstat_bytes'],resource['conservative_followed_file_bytes'])+g['new_loose_files_dirs_and_late_alloc_funding_bytes']<2013265920
    modified=[x for x in up['rows'] if x['status']=='M'];assert len(modified)==1
    scope=modified[0];dest=R/scope['git_tree_path'];oldscope=dest.read_bytes();assert oldscope==git('cat-file','blob',oldentries[scope['git_tree_path'].encode()][1])
    data=git('cat-file','blob',scope['git_blob']);assert free('/workspace')>((len(data)+4095)//4096)*4096+8*1024**2
    temporary=dest.with_name(dest.name+'.codex-620-exact-tmp');assert not temporary.exists()
    with temporary.open('xb') as f:f.write(data);f.flush();os.fsync(f.fileno())
    os.chmod(temporary,0o644);os.replace(temporary,dest)
    for x in rows:write_blob(x)
    updates=[{'git_tree_path':x['git_tree_path'],'git_blob':x['git_blob'],'mode':x['mode']} for x in up['rows']]+[{'git_tree_path':x['git_tree_path'],'git_blob':x['git_blob'],'mode':'100644'} for x in rows]
    git('update-index','-z','--index-info',data=b''.join((x['mode']+' '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in updates))
    sparse=[x['git_tree_path'] for x in up['rows'] if x['status']=='A']+[x['git_tree_path'] for x in rows if not x.get('ordinary_working_file')]
    git('update-index','--skip-worktree','--',*sparse)
    after,entries=index();changed={x['git_tree_path'].encode() for x in updates}
    assert {p:v for p,v in oldentries.items() if p not in changed}=={p:v for p,v in entries.items() if p not in changed}
    for x in updates:assert entries[x['git_tree_path'].encode()]==(x['mode'],x['git_blob'])
    for x in sparse:assert git('ls-files','-v','--',x).decode().startswith('S ')
    for x in rows:assert git('show',':'+x['git_tree_path'])==pathlib.Path(x['source_path']).read_bytes()
    assert dest.read_bytes()==data
    predicted,_=trees(entries);assert predicted==g['future_frozen_tree']
    tree=git('write-tree').decode().strip();assert tree==predicted
    resource_after=metrics();assert resource_after['pool_bytes']<=resource['pool_bytes']+g['exact_missing_blob_content_bytes']+g['exact_missing_tree_content_bytes']
    dump(OUT,{'status':'PASS_EXACT_COMPRESSED_CHECKPOINT_BYTES_AND_UPSTREAM_INDEX_TREE','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'funding_gate_sha256':sha(gatebytes),'independent_funding_review_path':review_path,'independent_funding_review_sha256':sha(pathlib.Path(review_path).read_bytes()),'input_manifest_sha256':sha(M.read_bytes()),'upstream_preflight_sha256':sha(U.read_bytes()),'all1642_upstream_full_blobs_and_index_modes_exact':True,'old_scope_to_exact_upstream_atomic_replace':True,'all_other_prior_index_entries_exact':True,'all_frozen_full_text_blobs_and_index_readbacks_exact':True,'regular_stage0_100644_all_additions':True,'sparse_only_new_evidence_and_upstream_additions':True,'files_count_including_manifest':len(rows),'frozen_tree':tree,'resource_before':resource,'resource_after':resource_after,'no_original_evidence_deleted_or_hidden':True,'no_compiler_native_cache_or_kernel_acceptance':True,'remote_readback_pending':True})
    print(json.dumps({'receipt':str(OUT),'sha256':sha(OUT.read_bytes()),'tree':tree,'pool_bytes':resource_after['pool_bytes']}))
if __name__=='__main__':
    if sys.argv[1]=='prepare':prepare()
    elif sys.argv[1]=='apply':apply(sys.argv[2])
    else:raise ValueError('Expected prepare or apply')
