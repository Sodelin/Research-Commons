"""Recover the exact frozen publication after an old-encoding size assertion.

Preserve prior source/gates/failure. Existing objects are read and authenticated,
never rewritten; exact Python zlib6 size applies only to newly created objects.
"""
import pathlib, json, datetime, importlib.util, sys
B=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
spec=importlib.util.spec_from_file_location('frozen_a',B/'publish_exact_compressed_checkpoint_20261011.py')
A=importlib.util.module_from_spec(spec);spec.loader.exec_module(A)
RECOVERY_GATE=B/'EXACT-COMPRESSED-CHECKPOINT-RECOVERY-V2-GATE.json'
PARTIAL=B/'EXACT-COMPRESSED-CHECKPOINT-PARTIAL-FAILURE-STATE.json'
SOURCE_SHA='c3479b7fcc3cc57e7485c7fdd6fa6fb4beef3b89c0a0ae046737ff879eeb6a24'
GATE_SHA='b1a260456c2c09673e8d811235f5778bdcb57e530948e12b82163cee87c1cce4'
PARTIAL_SHA='11fec1822e2abdafb3b776547171205b8ffaf179fce7fa1f462576808fa70595'
LATE_SHA='a769096c38dc32a9567c939cf8f15283629b8b43ca9693e33c6d4b2672fd28a2'
def original_pins():
    assert A.sha((B/'publish_exact_compressed_checkpoint_20261011.py').read_bytes())==SOURCE_SHA
    assert A.sha(A.G.read_bytes())==GATE_SHA and A.sha(PARTIAL.read_bytes())==PARTIAL_SHA
    assert A.sha((B/'preserve_bounded_late_receipts_20261011.py').read_bytes())==LATE_SHA
def write_blob_preserving_existing(x):
    b=pathlib.Path(x['source_path']).read_bytes();assert A.sha(b)==x['sha256'] and len(b)==x['bytes']
    if x['git_blob'] not in A.missing([x['git_blob']]):
        assert A.git('cat-file','blob',x['git_blob'])==b
        return
    oid=A.git('hash-object','-w','--stdin',data=b).decode().strip()
    assert oid==x['git_blob'] and A.git('cat-file','blob',oid)==b
    path=A.O/oid[:2]/oid[2:];assert path.is_file() and path.stat().st_size==x['zlib6_content_bytes']
def recovery_inputs():
    original_pins();g=json.loads(A.G.read_bytes());j,rows=A.inputs();before,entries=A.index()
    assert A.sha(before)==g['prior_index_sha256'] and A.git('rev-parse','HEAD').decode().strip()==A.HEAD
    up=A.upstream();scope=next(x for x in up['rows'] if x['status']=='M')
    # Exact partial state: complete upstream physical scope, old authenticated index.
    assert (A.R/scope['git_tree_path']).read_bytes()==A.git('cat-file','blob',scope['git_blob'])
    assert entries[scope['git_tree_path'].encode()][1]!=scope['git_blob']
    current,_=A.trees(entries);assert current==g['current_tree']
    for x in up['rows']:
        if x['status']=='A':assert x['git_tree_path'].encode() not in entries and not (A.R/x['git_tree_path']).exists()
        entries[x['git_tree_path'].encode()]=(x['mode'],x['git_blob'])
    for x in rows:
        if not x.get('ordinary_working_file'):assert x['git_tree_path'].encode() not in entries and not (A.R/x['git_tree_path']).exists()
        entries[x['git_tree_path'].encode()]=('100644',x['git_blob'])
    future,ts=A.trees(entries);assert future==g['future_frozen_tree']
    mb=A.missing(x['git_blob'] for x in rows);mt=A.missing(ts)
    unique={x['git_blob']:x for x in rows if x['git_blob'] in mb}
    blobs=sum(x['zlib6_content_bytes'] for x in unique.values());trees=sum(ts[o][1] for o in mt)
    assert blobs<=g['exact_missing_blob_content_bytes'] and trees<=g['exact_missing_tree_content_bytes']
    resource=A.metrics();content=blobs+trees+g['late_blob_reserve_bytes']+g['late_tree_reserve_bytes']+g['commit_reserve_bytes']
    assert resource['pool_bytes']+content<A.POOL_LIMIT
    assert max(resource['guard_lstat_bytes'],resource['conservative_followed_file_bytes'])+g['new_loose_files_dirs_and_late_alloc_funding_bytes']<2013265920
    return g,j,rows,before,up,future,blobs,trees,resource
def prepare():
    assert not RECOVERY_GATE.exists() and not A.OUT.exists()
    g,j,rows,before,up,future,blobs,trees,resource=recovery_inputs()
    A.dump(RECOVERY_GATE,{'status':'READY_SAME_FROZEN_PUBLICATION_V2_RECOVERY_INDEPENDENT_REVIEW_REQUIRED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'recovery_source_sha256':A.sha(pathlib.Path(__file__).read_bytes()),'original_source_sha256':SOURCE_SHA,'funding_gate_sha256':GATE_SHA,'input_manifest_sha256':A.sha(A.M.read_bytes()),'partial_failure_state_sha256':PARTIAL_SHA,'prior_index_entries_sha256':A.sha(before),'future_frozen_tree':future,'remaining_new_blob_content_bytes':blobs,'remaining_new_tree_content_bytes':trees,'unchanged_late_blob_reserve_bytes':g['late_blob_reserve_bytes'],'unchanged_late_tree_reserve_bytes':g['late_tree_reserve_bytes'],'unchanged_commit_reserve_bytes':g['commit_reserve_bytes'],'resource':resource,'scope_workingtree_already_exact620_index_still_original':True,'old_held_objects_fullbytes_authenticated_never_rewritten':True,'new_objects_still_require_exact_zlib6_size':True,'prior_failure_source_gate_and_all_encodings_retained':True,'no_further_scope_or_source_change_no_fetch_no_cap_raise_no_scientific_admission':True})
    print(json.dumps({'gate':str(RECOVERY_GATE),'sha256':A.sha(RECOVERY_GATE.read_bytes()),'remaining_blobs':blobs,'remaining_trees':trees,'pool_bytes':resource['pool_bytes']}))
def recover(review_path):
    assert not A.OUT.exists();rgbytes=RECOVERY_GATE.read_bytes();rg=json.loads(rgbytes);review=json.loads(pathlib.Path(review_path).read_bytes())
    assert review['status'].startswith('PASS') and review['recovery_gate_sha256']==A.sha(rgbytes)
    assert rg['recovery_source_sha256']==A.sha(pathlib.Path(__file__).read_bytes())
    g,j,rows,before,up,future,blobs,trees,resource=recovery_inputs()
    assert blobs==rg['remaining_new_blob_content_bytes'] and trees==rg['remaining_new_tree_content_bytes']
    for x in rows:write_blob_preserving_existing(x)
    updates=[{'git_tree_path':x['git_tree_path'],'git_blob':x['git_blob'],'mode':x['mode']} for x in up['rows']]+[{'git_tree_path':x['git_tree_path'],'git_blob':x['git_blob'],'mode':'100644'} for x in rows]
    A.git('update-index','-z','--index-info',data=b''.join((x['mode']+' '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in updates))
    sparse=[x['git_tree_path'] for x in up['rows'] if x['status']=='A']+[x['git_tree_path'] for x in rows if not x.get('ordinary_working_file')]
    A.git('update-index','--skip-worktree','--',*sparse)
    after,entries=A.index();changed={x['git_tree_path'].encode() for x in updates}
    assert b''.join(x+b'\0' for x in after.split(b'\0') if x and x.split(b'\t',1)[1] not in changed)==b''.join(x+b'\0' for x in before.split(b'\0') if x and x.split(b'\t',1)[1] not in changed)
    for x in updates:assert entries[x['git_tree_path'].encode()]==(x['mode'],x['git_blob'])
    for x in sparse:assert A.git('ls-files','-v','--',x).decode().startswith('S ')
    for x in rows:assert A.git('show',':'+x['git_tree_path'])==pathlib.Path(x['source_path']).read_bytes()
    assert A.git('write-tree').decode().strip()==future
    resource_after=A.metrics();assert resource_after['pool_bytes']<=resource['pool_bytes']+blobs+trees
    A.dump(A.OUT,{'status':'PASS_EXACT_COMPRESSED_CHECKPOINT_BYTES_AND_UPSTREAM_INDEX_TREE_AFTER_V2_RECOVERY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'funding_gate_sha256':GATE_SHA,'recovery_gate_sha256':A.sha(rgbytes),'recovery_source_sha256':A.sha(pathlib.Path(__file__).read_bytes()),'independent_recovery_review_path':review_path,'independent_recovery_review_sha256':A.sha(pathlib.Path(review_path).read_bytes()),'input_manifest_sha256':A.sha(A.M.read_bytes()),'upstream_preflight_sha256':A.sha(A.U.read_bytes()),'all1642_upstream_full_blobs_and_index_modes_exact':True,'old_scope_replaced_atomically_in_preserved_first_attempt_now_indexed_exact620':True,'all_other_prior_index_entries_exact':True,'all_frozen_full_text_blobs_and_index_readbacks_exact':True,'regular_stage0_100644_all_additions':True,'sparse_only_new_evidence_and_upstream_additions':True,'files_count_including_manifest':len(rows),'frozen_tree':future,'resource_before':resource,'resource_after':resource_after,'old_and_new_encodings_preserved_existing_fullbytes_authenticated_without_recompression':True,'earlier_failed_source_gate_trace_and_partial_state_retained':True,'no_original_evidence_deleted_or_hidden':True,'no_compiler_native_cache_or_kernel_acceptance':True,'remote_readback_pending':True})
    print(json.dumps({'receipt':str(A.OUT),'sha256':A.sha(A.OUT.read_bytes()),'tree':future,'pool_bytes':resource_after['pool_bytes']}))
def late():
    original_pins()
    spec=importlib.util.spec_from_file_location('late_frozen',B/'preserve_bounded_late_receipts_20261011.py');L=importlib.util.module_from_spec(spec);spec.loader.exec_module(L)
    L.A.write_blob=write_blob_preserving_existing
    L.main()
if __name__=='__main__':
    if sys.argv[1]=='prepare':prepare()
    elif sys.argv[1]=='recover':recover(sys.argv[2])
    elif sys.argv[1]=='late':late()
    else:raise ValueError('Expected prepare, recover or late')
