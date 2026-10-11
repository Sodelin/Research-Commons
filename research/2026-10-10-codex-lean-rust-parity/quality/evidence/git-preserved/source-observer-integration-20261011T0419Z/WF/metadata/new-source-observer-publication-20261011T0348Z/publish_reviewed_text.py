"""One separately funded text checkpoint; no compiler, cache or remote changes."""
import pathlib, importlib.util, hashlib, json, zlib, datetime, sys
D=pathlib.Path(__file__).resolve().parent
OLD=D.parent/'git-evidence-publication/publish_exact_compressed_checkpoint_20261011.py'
def sha(b):return hashlib.sha256(b).hexdigest()
assert sha(OLD.read_bytes())=='c3479b7fcc3cc57e7485c7fdd6fa6fb4beef3b89c0a0ae046737ff879eeb6a24'
spec=importlib.util.spec_from_file_location('fixed_helpers',OLD)
A=importlib.util.module_from_spec(spec);spec.loader.exec_module(A)
HEAD='4862b9618ca422da4ad5381b5dec0a3fcac56e76'
TREE='145eefb4baaec4eafca16622ed9fdfb538313922'
BASE_POOL=99789839
BLOB_RESERVE=512*1024
TREE_RESERVE=128*1024
COMMIT_RESERVE=16*1024
ALLOCATION_RESERVE=6*1024**2
M=D/'INPUTS.json';G=D/'FUNDING-GATE.json';OUT=D/'ACTUAL-PUBLICATION.json'
GUARD=D.parent/'source-only-observer-execution-guard-20261011T0338Z/guard_erased_selected_observer_v1.py'
GUARD_SHA='e7416c8012edf64a4f84cf24c98bc79d22d070cf8f71008f9a080462edf3e723'
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def row(p,path):
    b=p.read_bytes();return A.blob_info({'source_path':str(p),'git_tree_path':path,'sha256':sha(b),'bytes':len(b)})
def resource():
    # Retain the original fixed 26-root / scratch / nonreclaimable / native gates.
    r=A.metrics()
    assert sha(GUARD.read_bytes())==GUARD_SHA
    sp=importlib.util.spec_from_file_location('new_fixed_accounting',GUARD)
    q=importlib.util.module_from_spec(sp);sp.loader.exec_module(q)
    roots=r['ordered26_roots'];counter=q.allocation_details(roots)
    assert not q.active_markers(roots)
    r['inclusive_regular_symlink_accounting']=counter
    r['global_conservative_max_bytes']=max(counter['conservative_max_bytes'],r['guard_lstat_bytes'],r['conservative_followed_file_bytes'])
    assert r['global_conservative_max_bytes']<2013265920
    return r
def base():
    assert A.git('rev-parse','HEAD').decode().strip()==HEAD
    assert A.git('rev-parse','HEAD^{tree}').decode().strip()==TREE
    raw,entries=A.index();current,_=A.trees(entries)
    assert current==TREE and A.pool()==BASE_POOL
    return raw,entries
def inputs():
    m=json.loads(M.read_bytes());assert m['publisher_sha256']==sha(pathlib.Path(__file__).read_bytes())
    assert m['base_head']==HEAD and m['base_tree']==TREE
    rows=[A.blob_info(x) for x in m['files']]
    rows.append(row(M,m['prefix']+'/INPUT-MANIFEST.json'))
    assert len({x['git_tree_path'] for x in rows})==len(rows)
    raw,entries=base()
    for x in rows:
        p=x['git_tree_path'];parts=pathlib.PurePosixPath(p).parts
        assert not p.startswith('/') and '\\' not in p and '..' not in parts
        assert p.encode() not in entries and not (A.R/p).exists()
        entries[p.encode()]=('100644',x['git_blob'])
    return m,rows,raw,entries
def costs(rows,entries):
    missing=A.missing(x['git_blob'] for x in rows)
    unique={x['git_blob']:x for x in rows if x['git_blob'] in missing}
    tree,ts=A.trees(entries);mt=A.missing(ts)
    b=sum(x['zlib6_content_bytes'] for x in unique.values())
    t=sum(ts[o][1] for o in mt)
    allocated=sum(((x['zlib6_content_bytes']+4095)//4096)*4096+4096 for x in unique.values())+sum(((ts[o][1]+4095)//4096)*4096+4096 for o in mt)
    return b,t,allocated,tree
def funding(r,b,t,allocated):
    assert b<=BLOB_RESERVE and t<=TREE_RESERVE
    assert r['pool_bytes']==BASE_POOL
    assert BASE_POOL+BLOB_RESERVE+TREE_RESERVE+COMMIT_RESERVE<A.POOL_LIMIT
    assert allocated+256*1024<=ALLOCATION_RESERVE
    assert r['global_conservative_max_bytes']+ALLOCATION_RESERVE<2013265920
def prepare():
    assert not G.exists() and not OUT.exists()
    m,rows,raw,entries=inputs();r=resource();b,t,a,future=costs(rows,entries)
    funding(r,b,t,a)
    A.dump(G,{'status':'READY_SEPARATELY_FUNDED_TEXT_REQUIRES_INDEPENDENT_QC','utc':stamp(),'publisher_sha256':sha(pathlib.Path(__file__).read_bytes()),'manifest_sha256':sha(M.read_bytes()),'base_head':HEAD,'base_tree':TREE,'base_pool_bytes':BASE_POOL,'base_index_sha256':sha(raw),'known_rows':len(rows),'known_blob_content_bytes':b,'known_tree_content_bytes':t,'known_loose_allocation_bytes':a,'blob_reserve':BLOB_RESERVE,'tree_reserve':TREE_RESERVE,'commit_reserve':COMMIT_RESERVE,'allocation_reserve':ALLOCATION_RESERVE,'resource':r,'exact_costs_of_gate_review_and_actual_receipt_recomputed_before_apply':True,'no_object_index_head_or_cache_mutations':True})
    print(json.dumps({'status':'READY','gate':str(G),'gate_sha256':sha(G.read_bytes()),'known_rows':len(rows),'known_blobs':b,'known_trees':t,'future_without_gate_review_actual_receipt':future}))
def write_blob(x):
    b=pathlib.Path(x['source_path']).read_bytes()
    assert len(b)==x['bytes'] and sha(b)==x['sha256']
    if x['git_blob'] not in A.missing([x['git_blob']]):
        # Existing encoding can differ; authenticate and retain full bytes.
        assert A.git('cat-file','blob',x['git_blob'])==b;return
    oid=A.git('hash-object','-w','--stdin',data=b).decode().strip()
    assert oid==x['git_blob'] and A.git('cat-file','blob',oid)==b
    assert (A.O/oid[:2]/oid[2:]).stat().st_size==x['zlib6_content_bytes']
def stage(rows):
    A.git('update-index','-z','--index-info',data=b''.join(('100644 '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in rows))
    A.git('update-index','--skip-worktree','--',*(x['git_tree_path'] for x in rows))
def apply(review_path):
    assert not OUT.exists()
    g=json.loads(G.read_bytes());review=json.loads(pathlib.Path(review_path).read_bytes())
    assert review['status'].startswith('PASS')
    assert review['publisher_sha256']==sha(pathlib.Path(__file__).read_bytes())
    assert review['manifest_sha256']==sha(M.read_bytes()) and review['funding_gate_sha256']==sha(G.read_bytes())
    assert g['publisher_sha256']==sha(pathlib.Path(__file__).read_bytes()) and g['manifest_sha256']==sha(M.read_bytes())
    m,rows,raw,entries=inputs();assert sha(raw)==g['base_index_sha256'];r=resource()
    rows.extend([row(G,m['prefix']+'/FUNDING-GATE.json'),row(pathlib.Path(review_path),m['prefix']+'/INDEPENDENT-PUBLICATION-QC.json')])
    for x in rows:
        assert x['git_tree_path'].encode() not in entries;entries[x['git_tree_path'].encode()]=('100644',x['git_blob'])
    verified_tree,_=A.trees(entries)
    receipt={'status':'PASS_FULL_LISTED_INPUT_BYTES_INDEXED','utc':stamp(),'publisher_sha256':sha(pathlib.Path(__file__).read_bytes()),'manifest_sha256':sha(M.read_bytes()),'funding_gate_sha256':sha(G.read_bytes()),'independent_review_sha256':sha(pathlib.Path(review_path).read_bytes()),'base_head':HEAD,'base_tree':TREE,'verified_inputs_tree_excluding_this_receipt':verified_tree,'listed_input_rows_excluding_this_receipt':len(rows),'full_original_utf8_bytes_and_100644_stage0_skip_worktree_verified':True,'all_old_entries_preserved':True,'one_final_physical_tree_write':True,'resource_before':r,'scope':'This full receipt is written only after all listed original input/index readbacks. Final receipt readback and final tree/resource result are returned by invocation; no recursive self hash, compiler/kernel/master/cache/remote acceptance.'}
    rb=(json.dumps(receipt,indent=2)+'\n').encode();full=b'blob '+str(len(rb)).encode()+b'\0'+rb
    rx={'source_path':str(OUT),'git_tree_path':m['prefix']+'/ACTUAL-PUBLICATION.json','sha256':sha(rb),'bytes':len(rb),'git_blob':hashlib.sha1(full).hexdigest(),'zlib6_content_bytes':len(zlib.compress(full,6))}
    assert rx['git_tree_path'].encode() not in entries
    entries[rx['git_tree_path'].encode()]=('100644',rx['git_blob'])
    b,t,a,future=costs(rows+[rx],entries);funding(r,b,t,a)
    for x in rows:write_blob(x)
    stage(rows);current,observed=A.index();added={x['git_tree_path'].encode() for x in rows}
    assert b''.join(x+b'\0' for x in current.split(b'\0') if x and x.split(b'\t',1)[1] not in added)==raw
    for x in rows:
        assert observed[x['git_tree_path'].encode()]==('100644',x['git_blob'])
        assert A.git('show',':'+x['git_tree_path'])==pathlib.Path(x['source_path']).read_bytes()
        assert A.git('ls-files','-v','--',x['git_tree_path']).decode().startswith('S ')
    with OUT.open('xb') as f:f.write(rb)
    write_blob(rx);stage([rx]);finalraw,observed=A.index();assert observed==entries
    assert A.git('show',':'+rx['git_tree_path'])==rb
    assert A.git('ls-files','-v','--',rx['git_tree_path']).decode().startswith('S ')
    assert A.git('write-tree').decode().strip()==future
    after=resource();assert after['pool_bytes']<=BASE_POOL+b+t
    print(json.dumps({'status':'PASS_FULL_TEXT_AND_FINAL_RECEIPT_ONE_TREE_READBACK','final_tree':future,'receipt_sha256':sha(rb),'manifest_sha256':sha(M.read_bytes()),'input_rows_including_actual_receipt':len(rows)+1,'new_blob_content_bytes':b,'new_tree_content_bytes':t,'pool_bytes':after['pool_bytes'],'remaining_commit_reserve':COMMIT_RESERVE,'resource_after':after}))
if __name__=='__main__':
    if sys.argv[1]=='prepare':prepare()
    elif sys.argv[1]=='apply':apply(sys.argv[2])
    else:raise ValueError('Expected prepare or apply')
