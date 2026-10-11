"""Preserve final full texts within the ORIGINAL remaining reserves; one tree write."""
import pathlib, json, importlib.util, datetime, sys
B=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
def digest(p):
    import hashlib
    return hashlib.sha256(p.read_bytes()).hexdigest()
V=B/'recover_exact_compressed_checkpoint_v3_20261011.py'
assert digest(V)=='d7bc29eafca8f53e4231f880c0d13061c79d7d69ba27c1ed1a886697f327ed7e'
spec=importlib.util.spec_from_file_location('preserved_v3',V)
Q=importlib.util.module_from_spec(spec);spec.loader.exec_module(Q);Q.original_pins();A=Q.A
M=B/'FINAL-REMAINING-FULLTEXT-INPUTS.json'
G=B/'FINAL-REMAINING-FIXED-RESERVE-GATE.json'
OUT=B/'FINAL-REMAINING-FULLTEXT-PUBLICATION.json'
BASE_TREE='c47535d42987f807b097125fb31966ee353b253c'
BASE_POOL=99707172
BLOB_LEFT=95096
TREE_LEFT=91206
COMMIT_LEFT=16384
FUNDED_MAX=99909858
assert BASE_POOL+BLOB_LEFT+TREE_LEFT+COMMIT_LEFT==FUNDED_MAX

def row(p,path):
    data=p.read_bytes()
    return A.blob_info({'source_path':str(p),'git_tree_path':path,'sha256':A.sha(data),'bytes':len(data)})
def inputs():
    mb=M.read_bytes();m=json.loads(mb)
    assert m['publisher_sha256']==digest(pathlib.Path(__file__))
    rows=[A.blob_info(x) for x in m['files']]
    rows.append(row(M,m['prefix']+'/FINAL-INPUT-MANIFEST.json'))
    assert len({x['git_tree_path'] for x in rows})==len(rows)
    raw,entries=A.index();tree,_=A.trees(entries)
    assert tree==BASE_TREE and A.git('rev-parse','HEAD').decode().strip()==A.HEAD
    assert A.pool()==BASE_POOL
    for x in rows:
        p=x['git_tree_path'].encode()
        assert p not in entries and not (A.R/x['git_tree_path']).exists()
        entries[p]=('100644',x['git_blob'])
    return m,rows,raw,entries

def costs(rows,entries):
    missing=A.missing(x['git_blob'] for x in rows)
    unique={x['git_blob']:x for x in rows if x['git_blob'] in missing}
    tree,ts=A.trees(entries);mt=A.missing(ts)
    blobs=sum(x['zlib6_content_bytes'] for x in unique.values())
    trees=sum(ts[x][1] for x in mt)
    allocation=sum(((x['zlib6_content_bytes']+4095)//4096)*4096+4096 for x in unique.values())+sum(((ts[x][1]+4095)//4096)*4096+4096 for x in mt)
    return blobs,trees,allocation,tree

def funding(resource,blobs,trees,allocation):
    assert blobs<=BLOB_LEFT and trees<=TREE_LEFT
    assert resource['pool_bytes']+blobs+trees+COMMIT_LEFT<=FUNDED_MAX<A.POOL_LIMIT
    original=json.loads(A.G.read_bytes())
    assert allocation<=original['new_loose_files_dirs_and_late_alloc_funding_bytes']
    assert max(resource['guard_lstat_bytes'],resource['conservative_followed_file_bytes'])+allocation<2013265920

def prepare():
    assert not G.exists() and not OUT.exists()
    m,rows,raw,entries=inputs();resource=A.metrics()
    blobs,trees,allocation,tree=costs(rows,entries)
    # Reserve full remaining amounts, not an arbitrary new tree subpartition.
    funding(resource,BLOB_LEFT,TREE_LEFT,allocation+256*1024)
    A.dump(G,{'status':'READY_ORIGINAL_REMAINING_FIXED_RESERVES_SOURCE_REVIEW_REQUIRED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publisher_sha256':digest(pathlib.Path(__file__)),'manifest_sha256':digest(M),'base_index_entries_sha256':A.sha(raw),'base_tree':BASE_TREE,'base_pool_bytes':BASE_POOL,'original_funding_gate_sha256':digest(A.G),'remaining_blob_content_bytes':BLOB_LEFT,'remaining_tree_content_bytes':TREE_LEFT,'commit_content_bytes':COMMIT_LEFT,'original_funded_max_pool_bytes':FUNDED_MAX,'known_rows_blob_bytes':blobs,'known_rows_tree_bytes':trees,'known_rows_count':len(rows),'resource':resource,'policy':'Apply rechecks gate and independent source review, then computes exact costs INCLUDING this gate and the complete actual post-index receipt before any mutation; writes only one final tree. All preexisting index entries retained. No compiler/native/cache changes or scientific acceptance.'})
    print(json.dumps({'gate':str(G),'sha256':digest(G),'known_blobs':blobs,'known_trees':trees,'known_rows':len(rows)}))

def apply(review_path):
    assert not OUT.exists()
    review=json.loads(pathlib.Path(review_path).read_bytes())
    assert review['status'].startswith('PASS') and review['finalizer_source_sha256']==digest(pathlib.Path(__file__))
    gate=json.loads(G.read_bytes())
    assert gate['publisher_sha256']==digest(pathlib.Path(__file__)) and gate['manifest_sha256']==digest(M)
    m,rows,raw,entries=inputs();assert gate['base_index_entries_sha256']==A.sha(raw)
    rows.append(row(G,m['prefix']+'/FINAL-FIXED-RESERVE-GATE.json'))
    for x in rows:entries[x['git_tree_path'].encode()]=('100644',x['git_blob'])
    pre_receipt,_=A.trees(entries);resource=A.metrics()
    # This receipt reports all fixed input rows, explicitly excluding itself.
    # It is authenticated and indexed only after those stated readbacks pass.
    receipt={'status':'PASS_COMPLETE_FINAL_FIXED_INPUT_BYTES_INDEXED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publisher_sha256':digest(pathlib.Path(__file__)),'manifest_sha256':digest(M),'gate_sha256':digest(G),'independent_source_review_sha256':digest(pathlib.Path(review_path)),'input_rows_count_excluding_this_receipt':len(rows),'all_original_full_utf8_bytes_read_back':True,'all_preexisting_index_entries_exact':True,'all_added_files_regular_100644_stage0_skip_worktree':True,'pure_tree_of_verified_inputs_before_this_receipt':pre_receipt,'resource_before':resource,'original_remaining_blob_bytes':BLOB_LEFT,'original_remaining_tree_bytes':TREE_LEFT,'commit_reserve_bytes':COMMIT_LEFT,'one_final_tree_write_only':True,'receipt_scope':'Full listed input blob/index checks before receipt is written; final receipt readback/tree/resource checks returned separately by invocation. No recursive self hash.','no_compiler_native_cache_kernel_or_remote_acceptance':True}
    receipt_bytes=(json.dumps(receipt,indent=2)+'\n').encode()
    import hashlib,zlib
    full=b'blob '+str(len(receipt_bytes)).encode()+b'\0'+receipt_bytes
    rx={'source_path':str(OUT),'git_tree_path':m['prefix']+'/FINAL-REMAINING-FULLTEXT-PUBLICATION.json','sha256':A.sha(receipt_bytes),'bytes':len(receipt_bytes),'git_blob':hashlib.sha1(full).hexdigest(),'zlib6_content_bytes':len(zlib.compress(full,6))}
    assert rx['git_tree_path'].encode() not in entries
    entries[rx['git_tree_path'].encode()]=('100644',rx['git_blob'])
    blobs,trees,allocation,future=costs(rows+[rx],entries)
    funding(resource,blobs,trees,allocation+256*1024)
    for x in rows:Q.write_blob_preserving_existing(x)
    def stage(rr):
        A.git('update-index','-z','--index-info',data=b''.join(('100644 '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in rr))
        A.git('update-index','--skip-worktree','--',*(x['git_tree_path'] for x in rr))
    stage(rows)
    current,actual=A.index();added={x['git_tree_path'].encode() for x in rows}
    assert b''.join(x+b'\0' for x in current.split(b'\0') if x and x.split(b'\t',1)[1] not in added)==raw
    for x in rows:
        assert actual[x['git_tree_path'].encode()]==('100644',x['git_blob'])
        assert A.git('show',':'+x['git_tree_path'])==pathlib.Path(x['source_path']).read_bytes()
        assert A.git('ls-files','-v','--',x['git_tree_path']).decode().startswith('S ')
    with OUT.open('xb') as f:f.write(receipt_bytes)
    Q.write_blob_preserving_existing(rx);stage([rx])
    finalraw,actual=A.index();assert actual==entries
    assert A.git('show',':'+rx['git_tree_path'])==receipt_bytes
    assert A.git('ls-files','-v','--',rx['git_tree_path']).decode().startswith('S ')
    assert A.git('write-tree').decode().strip()==future
    after=A.metrics();assert after['pool_bytes']<=BASE_POOL+blobs+trees
    print(json.dumps({'status':'PASS_FINAL_FULLTEXT_RECEIPT_AND_ONE_TREE_WRITE_READBACK','final_tree':future,'manifest_sha256':digest(M),'full_actual_receipt_sha256':digest(OUT),'full_actual_receipt_git_path':rx['git_tree_path'],'new_blob_content_bytes':blobs,'new_tree_content_bytes':trees,'pool_bytes':after['pool_bytes'],'remaining_commit_reserve_bytes':COMMIT_LEFT,'resource_after':after}))
if __name__=='__main__':
    if sys.argv[1]=='prepare':prepare()
    elif sys.argv[1]=='apply':apply(sys.argv[2])
    else:raise ValueError('Expected prepare or apply')
