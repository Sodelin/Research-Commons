"""Fully preserve late reviews/results within the already frozen compressed reserve."""
import pathlib, json, importlib.util, datetime
B=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
spec=importlib.util.spec_from_file_location('funded',B/'publish_exact_compressed_checkpoint_20261011.py')
A=importlib.util.module_from_spec(spec);spec.loader.exec_module(A)
M=B/'BOUNDED-LATE-RECEIPTS-INPUTS.json'
OUT=B/'BOUNDED-LATE-RECEIPTS-PUBLICATION.json'
def main():
    assert not OUT.exists()
    gatebytes=A.G.read_bytes();g=json.loads(gatebytes);base=json.loads(A.OUT.read_bytes())
    assert base['status'].startswith('PASS') and base['funding_gate_sha256']==A.sha(gatebytes)
    before,entries=A.index();prior_tree,_=A.trees(entries);assert prior_tree==base['frozen_tree']
    mbytes=M.read_bytes();j=json.loads(mbytes);assert j['publisher_sha256']==A.sha(pathlib.Path(__file__).read_bytes())
    rows=[A.blob_info(x) for x in j['files']]
    rows.append(A.blob_info({'source_path':str(M),'git_tree_path':j['prefix']+'/LATE-INPUT-MANIFEST.json','sha256':A.sha(mbytes),'bytes':len(mbytes)}))
    assert len({x['git_tree_path'] for x in rows})==len(rows)
    for x in rows:
        p=x['git_tree_path'].encode();assert p not in entries and not (A.R/x['git_tree_path']).exists();entries[p]=('100644',x['git_blob'])
    future,ts=A.trees(entries);mb=A.missing(x['git_blob'] for x in rows);mt=A.missing(ts)
    unique={x['git_blob']:x for x in rows if x['git_blob'] in mb}
    blobs=sum(x['zlib6_content_bytes'] for x in unique.values());trees=sum(ts[o][1] for o in mt)
    # Full actual receipt below has a small final blob/tree allowance inside each reserve.
    assert blobs+32*1024<=g['late_blob_reserve_bytes']
    assert trees+32*1024<=g['late_tree_reserve_bytes']
    r=A.metrics();allocation=sum(((x['zlib6_content_bytes']+4095)//4096)*4096+4096 for x in unique.values())+sum(((ts[o][1]+4095)//4096)*4096+4096 for o in mt)+512*1024
    assert allocation<=g['new_loose_files_dirs_and_late_alloc_funding_bytes']
    assert r['pool_bytes']+blobs+trees+64*1024+g['commit_reserve_bytes']<A.POOL_LIMIT
    assert max(r['guard_lstat_bytes'],r['conservative_followed_file_bytes'])+allocation<2013265920
    for x in rows:A.write_blob(x)
    A.git('update-index','-z','--index-info',data=b''.join(('100644 '+x['git_blob']+'\t'+x['git_tree_path']+'\0').encode() for x in rows))
    A.git('update-index','--skip-worktree','--',*(x['git_tree_path'] for x in rows))
    current,after=A.index();added={x['git_tree_path'].encode() for x in rows}
    assert b''.join(x+b'\0' for x in current.split(b'\0') if x and x.split(b'\t',1)[1] not in added)==before
    for x in rows:
        assert after[x['git_tree_path'].encode()]==('100644',x['git_blob'])
        assert A.git('show',':'+x['git_tree_path'])==pathlib.Path(x['source_path']).read_bytes()
        assert A.git('ls-files','-v','--',x['git_tree_path']).decode().startswith('S ')
    actual=A.git('write-tree').decode().strip();assert actual==future
    rafter=A.metrics();assert rafter['pool_bytes']<=r['pool_bytes']+blobs+trees
    A.dump(OUT,{'status':'PASS_FULL_BOUNDED_LATE_REVIEW_AND_RESULT_BYTES_INDEXED','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'funding_gate_sha256':A.sha(gatebytes),'manifest_sha256':A.sha(mbytes),'files_count_including_manifest':len(rows),'complete_original_blob_index_readbacks':True,'all_preexisting_index_entries_exact':True,'regular_100644_stage0_S':True,'exact_new_blob_content_bytes':blobs,'exact_new_tree_content_bytes':trees,'reserved_final_receipt_blob_bytes':32768,'reserved_final_receipt_tree_bytes':32768,'tree_without_this_receipt':actual,'resource_before':r,'resource_after':rafter,'receipt_preservation_next':'Store this complete actual result as a regular sparse Git blob using the remaining32KiB blob/tree allowance, then write final tree and two-parent checkpoint commit.','no_compiler_native_cache_scientific_or_remote_acceptance':True})
    receipt=A.blob_info({'source_path':str(OUT),'git_tree_path':j['prefix']+'/BOUNDED-LATE-RECEIPTS-PUBLICATION.json','sha256':A.sha(OUT.read_bytes()),'bytes':OUT.stat().st_size})
    assert receipt['zlib6_content_bytes']<32768
    after[receipt['git_tree_path'].encode()]=('100644',receipt['git_blob']);final,fs=A.trees(after);fm=A.missing(fs);ft=sum(fs[o][1] for o in fm);assert ft<32768
    assert A.pool()+receipt['zlib6_content_bytes']+ft+g['commit_reserve_bytes']<A.POOL_LIMIT
    A.write_blob(receipt)
    A.git('update-index','-z','--index-info',data=('100644 '+receipt['git_blob']+'\t'+receipt['git_tree_path']+'\0').encode())
    A.git('update-index','--skip-worktree','--',receipt['git_tree_path'])
    assert A.git('show',':'+receipt['git_tree_path'])==OUT.read_bytes()
    assert A.git('write-tree').decode().strip()==final;A.metrics()
    print(json.dumps({'receipt':str(OUT),'receipt_sha256':A.sha(OUT.read_bytes()),'full_receipt_git_tree_path':receipt['git_tree_path'],'final_tree':final,'pool_bytes':A.pool()}))
if __name__=='__main__':main()
