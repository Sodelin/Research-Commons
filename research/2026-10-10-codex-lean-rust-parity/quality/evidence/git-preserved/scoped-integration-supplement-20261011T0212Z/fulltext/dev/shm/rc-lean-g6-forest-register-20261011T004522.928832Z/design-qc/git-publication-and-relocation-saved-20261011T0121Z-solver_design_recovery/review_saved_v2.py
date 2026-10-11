#!/usr/bin/env python3
"""Own saved-byte reader. No Git commands, target imports, or producer processes."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import struct
import sys
import zlib

REPO=Path('/workspace/Research-Commons')
P=REPO/'research/2026-10-10-codex-lean-rust-parity'
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
B=W/'metadata/git-evidence-publication'
POOLS=[Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z'), REPO/'.git/objects']
INDEX=Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
COMMIT='5e154441fc764b020d3212e70534ef674238ad59'
OBJECT_CACHE={}
TREE_CACHE={}

def require(ok,why):
    if not ok: raise AssertionError(why)

def digest(data): return hashlib.sha256(data).hexdigest()

def pin(path,expected=None,size=None):
    path=Path(path); data=path.read_bytes(); h=digest(data)
    require(expected is None or h==expected,'file hash '+str(path))
    require(size is None or len(data)==size,'file size '+str(path))
    return {'path':str(path),'bytes':len(data),'sha256':h},data

def obj(oid):
    if oid in OBJECT_CACHE:return OBJECT_CACHE[oid]
    for pool in POOLS:
        path=pool/oid[:2]/oid[2:]
        if not path.is_file():continue
        raw=zlib.decompress(path.read_bytes())
        require(hashlib.sha1(raw).hexdigest()==oid,'Git object SHA1 '+oid)
        header,body=raw.split(b'\0',1); kind,length=header.split(b' ',1)
        require(int(length)==len(body),'Git object raw size '+oid)
        result=(kind.decode('ascii'),body)
        OBJECT_CACHE[oid]=result
        return result
    raise AssertionError('preserved loose object unavailable '+oid)

def tree(oid):
    if oid in TREE_CACHE:return TREE_CACHE[oid]
    kind,data=obj(oid); require(kind=='tree','tree object kind')
    result={}; p=0
    while p<len(data):
        stop=data.index(b' ',p); zero=data.index(b'\0',stop)
        mode=data[p:stop].decode('ascii'); name=data[stop+1:zero].decode('utf-8','surrogateescape')
        require(name not in result and '/' not in name,'unique tree child')
        require(zero+21<=len(data),'tree object entry range')
        result[name]=(mode,data[zero+1:zero+21].hex());p=zero+21
    require(p==len(data),'tree exact EOF');TREE_CACHE[oid]=result
    return result

def tree_path(root,path):
    parts=path.split('/'); current=root
    for n,part in enumerate(parts):
        entry=tree(current).get(part)
        if entry is None:return None
        mode,oid=entry
        if n==len(parts)-1:return entry
        require(mode=='40000','intermediate tree mode '+path);current=oid
    raise AssertionError('empty tree path')

def commit_tree(oid):
    kind,data=obj(oid);require(kind=='commit','commit object kind')
    fields=data.split(b'\n\n',1)[0].splitlines(); roots=[r[5:].decode() for r in fields if r.startswith(b'tree ')]; parents=[r[7:].decode() for r in fields if r.startswith(b'parent ')]
    require(len(roots)==1,'one commit tree')
    return roots[0],parents

def index_entries(data):
    require(len(data)>32 and hashlib.sha1(data[:-20]).digest()==data[-20:],'whole-index trailing SHA1')
    magic,version,count=struct.unpack('>4sII',data[:12]);require(magic==b'DIRC' and version==4,'exact current v4 Git index')
    p=12;previous=b'';entries={}
    for _ in range(count):
        require(p+62<=len(data)-20,'index fixed entry range')
        mode=struct.unpack('>I',data[p+24:p+28])[0];oid=data[p+40:p+60].hex();flags=struct.unpack('>H',data[p+60:p+62])[0];p+=62
        extended=0
        if flags&0x4000:
            require(p+2<=len(data)-20,'extended index flags range');extended=struct.unpack('>H',data[p:p+2])[0];p+=2
        byte=data[p];p+=1;remove=byte&0x7f
        while byte&0x80:
            byte=data[p];p+=1;remove=((remove+1)<<7)+(byte&0x7f)
        require(remove<=len(previous),'v4 remove-prefix bounds')
        zero=data.index(b'\0',p);suffix=data[p:zero];p=zero+1
        path=previous[:len(previous)-remove]+suffix;previous=path
        label=path.decode('utf-8','surrogateescape')
        require(label not in entries,'unique stage0/index path '+label)
        entries[label]={'mode':mode,'git_blob':oid,'stage':(flags>>12)&3,'skip_worktree':bool(extended&0x4000)}
    require(p<=len(data)-20,'index extension boundary')
    return entries,{'version':version,'entry_count':count,'extension_bytes':len(data)-20-p,'bytes':len(data),'sha256':digest(data),'sha1_checksum_verified':True}

def check():
    records=[
        ('metadata12',P/'quality/NEW-METADATA-LOSSLESS-RELOCATION-20261011T0100Z.json','67f84ca4c5f034e6293eaef640c1e631284b64ecbb683a7a1934fe5f359bf3e8','files',12,1193640),
        ('failure1cf54',B/'NEW-1CF-EVIDENCE-LOSSLESS-RELOCATION-20261011T0110Z.json','72cdd1f4b92d4a31ab0bccfaba48b04b3e3bc1d68d898157fd93a946a0432fc9','rows',54,891516),
        ('fourth_fcad57',B/'PUBLICATION-V3.json','698c046d07ed4d798d2fce1f8015f24d6e43a78eefdd63903b899985ec62f7df','files',57,1178107),
        ('forest101_66',B/'FOREST101-PUBLICATION.json','799b4af01125f1d7c23379bff972fd704bc4cdd6c3cbb995ebd817eefd0631ec','files',66,4401726),
    ]
    idx_data=INDEX.read_bytes();idx,idx_pin=index_entries(idx_data)
    idx_pin['path']=str(INDEX)
    root,parents=commit_tree(COMMIT);require(len(parents)==1,'one previous Commons commit')
    parent_root,_=commit_tree(parents[0])
    all_paths=set();checked=[];blob_count=set();total=0;relocations=0;sparse=0
    for label,path,expected,rowkey,count,size in records:
        receipt_pin,data=pin(path,expected);j=json.loads(data);rows=j[rowkey]
        require(j['files_count']==len(rows)==count and sum(r['bytes'] for r in rows)==size,'exact saved row/byte inventory '+label)
        require(j.get('scientific_content_deleted',False) is False and j.get('scientific_content_lost',False) is False and j.get('scientific_acceptance_promoted',False) is False,'byte-only saved scope '+label)
        evidence=[]
        for row in rows:
            path=row['git_tree_path'];require(path not in all_paths,'disjoint new tree paths');all_paths.add(path)
            require(path.startswith('research/2026-10-10-codex-lean-rust-parity/'),'bounded packet tree path')
            original=row.get('preserved_path',row.get('original_path'));require(original is not None,'retained original binding')
            original_pin,data=pin(original,row['sha256'],row['bytes'])
            kind,blob=obj(row['git_blob']);require(kind=='blob' and blob==data,'full raw regular Git blob byte equality '+path)
            require(idx.get(path)=={'mode':0o100644,'git_blob':row['git_blob'],'stage':0,'skip_worktree':True},'current index regular bytes+skip-worktree '+path)
            require(tree_path(root,path)==('100644',row['git_blob']),'preserved commit regular tree/blob binding '+path)
            require(tree_path(parent_root,path) is None,'new path absent from immediately preceding commit '+path)
            materialized=REPO/path
            if 'local_path' in row:
                require(Path(row['local_path'])==materialized and materialized.is_symlink(),'only recorded relocated path uses local readthrough symlink')
                require(materialized.resolve()==Path(original).resolve(),'exact counted shared-memory readthrough destination')
                require(materialized.read_bytes()==data,'local readthrough full bytes')
                relocations+=1
            else:
                require(not materialized.exists() and not materialized.is_symlink(),'explicit sparse publication remains unmaterialized')
                sparse+=1
            evidence.append({'git_tree_path':path,'git_blob':row['git_blob'],'sha256':row['sha256'],'bytes':len(data),'original_path':str(original),'regular_commit_and_index_verified':True,'parent_commit_absence_verified':True,'local_readthrough_verified':('local_path' in row)})
            blob_count.add(row['git_blob']);total+=len(data)
        checked.append({'receipt':receipt_pin,'label':label,'file_count':count,'content_bytes':size,'rows':evidence})
    require(len(all_paths)==189 and relocations==66 and sparse==123,'189 disjoint bytes paths/66readthrough/123sparse')
    result_pins=[]
    for path,expected in [
        (P/'lean/G6-NATURAL-COMMON-FACTORIZATION-MAIN-FCAD-FAILED-20261011T003950.153734Z-RESULT.json','1939fe2afec3c55f50406556c07a9181acb44881091897659bb1962803f6c83b'),
        (P/'lean/G6-FOREST-REGISTER-COMPRESSION-PROOF101-20261011T005209.997288Z-RESULT.json','a5db64c7116fe8d6c33f2014f6ccfe7f5b2e2e8ba1227eb17933635fdd9f745c'),
        (P/'lean/G6-NATURAL-COMMON-FACTORIZATION-MAIN-1CF-FAILED-20261011T010231.626199Z-RESULT.json','b8d2be40c66bfeeb15c1300fbd391fad7e3c87da262a377149db92b39fbf442d')]:
        row,data=pin(path,expected);j=json.loads(data);result_pins.append(row)
        if expected.startswith(('1939','a5db')):
            require(j['packet_distribution_complete'] is False,'historical fixed-shmem fallback flag unchanged')
        else:require(j['packet_distribution_complete'] is True,'original completed packet-export flag preserved before separately qualified readthrough relocation')
    return {'status':'PASS_SAVED_NEW_PATH_PUBLICATION_AND_LOSSLESS_RELOCATION_BYTES','checked_receipts':checked,'counts':{'disjoint_regular_commit_index_paths':189,'local_same_byte_readthrough_symlinks':66,'unmaterialized_sparse_paths':123,'distinct_blob_objects':len(blob_count),'full_content_bytes':total},'current_index_snapshot':idx_pin,'commit_sha1':COMMIT,'commit_tree_sha1':root,'parent_commit_sha1':parents[0],'parent_tree_sha1':parent_root,'unchanged_original_results':result_pins,'qualifications':['Own standard-library reads only; no Git command, publisher, target/helper/compiler/native process imported or executed.','All189 listed paths are regular100644 blobs in the preserved local commit and current index, absent from its immediate parent commit. This supports the new-path scope of these receipts, not an audit of every unrelated filesystem change.','The66 relocated paths retain exact bytes through symlinks into already-counted fixed shared-memory originals;123 publication paths remain explicitly sparse. Historical packet-complete flags remain unchanged.','Local commit and retained loose-object bytes were independently checked. Remote push/readback is root-owned and is not verified here.','No original source/cache/attempt deletion, mathematical admission, master closure, source factor, biological PMF or runtime/native refinement is inferred from Git publication.']}

def main():
    out=Path(sys.argv[1]);report={'schema':'saved_byte_new_evidence_publication_relocation_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':digest(Path(__file__).read_bytes()),'target_imports_or_producer_processes':0,'git_commands_or_mutations':0}
    try:report.update(check())
    except Exception as exc:report.update(status='FAIL_SAVED_PUBLICATION_RELOCATION_QC',error_type=type(exc).__name__,error=str(exc))
    with out.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'path':str(out),'status':report['status'],'sha256':digest(out.read_bytes())}))
    return int(report['status'].startswith('FAIL'))
if __name__=='__main__':raise SystemExit(main())
