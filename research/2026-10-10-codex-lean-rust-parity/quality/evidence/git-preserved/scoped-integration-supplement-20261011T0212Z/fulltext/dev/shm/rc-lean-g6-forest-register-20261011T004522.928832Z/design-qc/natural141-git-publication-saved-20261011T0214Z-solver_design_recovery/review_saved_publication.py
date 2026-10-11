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
    result=packed_obj(oid)
    OBJECT_CACHE[oid]=result
    return result


PACK_INDEX_CACHE={}
PACK_OBJECT_CACHE={}
PACK_INDEX_PINS={}
MAX_PACKED_BODY=2*1024*1024

def packed_index(path):
    if path in PACK_INDEX_CACHE:return PACK_INDEX_CACHE[path]
    data=path.read_bytes()
    require(hashlib.sha1(data[:-20]).digest()==data[-20:],'packed index checksum')
    require(data[:8]==b'\xfftOc\0\0\0\2','saved Git pack index v2')
    count=struct.unpack('>I',data[1028:1032])[0]
    names=1032;offsets=names+24*count
    require(offsets+4*count+40<=len(data),'pack-index table bounds')
    result=(data,count,names,offsets)
    PACK_INDEX_CACHE[path]=result
    PACK_INDEX_PINS[str(path)]={'path':str(path),'bytes':len(data),'sha256':digest(data),'sha1_checksum_verified':True}
    return result

def lookup_offset(path,oid):
    data,count,names,offsets=packed_index(path);key=bytes.fromhex(oid);lo=0;hi=count
    while lo<hi:
        mid=(lo+hi)//2;value=data[names+20*mid:names+20*(mid+1)]
        if value<key:lo=mid+1
        else:hi=mid
    if lo==count or data[names+20*lo:names+20*(lo+1)]!=key:return None
    offset=struct.unpack('>I',data[offsets+4*lo:offsets+4*(lo+1)])[0]
    if offset&0x80000000:
        pos=offsets+4*count+8*(offset&0x7fffffff)
        require(pos+8<=len(data)-40,'wide pack-index offset bounds');offset=struct.unpack('>Q',data[pos:pos+8])[0]
    return offset

def apply_delta(base,delta):
    p=0
    def variable():
        nonlocal p
        value=0;shift=0
        while True:
            require(p<len(delta) and shift<=63,'Git delta size varint bounds')
            b=delta[p];p+=1;value|=(b&127)<<shift
            if not b&128:return value
            shift+=7
    require(variable()==len(base),'Git delta exact base length')
    target=variable();require(target<=MAX_PACKED_BODY,'bounded saved tree delta output')
    output=bytearray()
    while p<len(delta):
        op=delta[p];p+=1
        if op&128:
            offset=length=0
            for i in range(4):
                if op&(1<<i):require(p<len(delta),'delta offset bytes');offset|=delta[p]<<(8*i);p+=1
            for i in range(3):
                if op&(1<<(i+4)):require(p<len(delta),'delta length bytes');length|=delta[p]<<(8*i);p+=1
            length=length or 65536
            require(offset+length<=len(base),'Git delta source range')
            chunk=base[offset:offset+length]
        else:
            require(op!=0 and p+op<=len(delta),'Git delta literal bounds');chunk=delta[p:p+op];p+=op
        require(len(output)+len(chunk)<=target,'Git delta target bounds');output.extend(chunk)
    require(len(output)==target,'Git delta final size');return bytes(output)

def pack_at(path,offset,depth=0):
    require(depth<=128,'bounded saved Git delta depth')
    key=(str(path),offset)
    if key in PACK_OBJECT_CACHE:return PACK_OBJECT_CACHE[key]
    with path.open('rb') as f:
        head=f.read(12);require(head[:4]==b'PACK' and struct.unpack('>I',head[4:8])[0] in (2,3),'saved Git pack header')
        require(12<=offset<path.stat().st_size-20,'saved pack object offset bounds');f.seek(offset)
        first=f.read(1)[0];kind=(first>>4)&7;size=first&15;shift=4;b=first
        while b&128:
            b=f.read(1)[0];size|=(b&127)<<shift;shift+=7;require(shift<=64,'pack object size bounds')
        require(size<=MAX_PACKED_BODY,'bounded saved tree/commit compressed representation')
        base_offset=None;base_oid=None
        if kind==6:
            b=f.read(1)[0];distance=b&127
            while b&128:
                b=f.read(1)[0];distance=((distance+1)<<7)+(b&127)
            base_offset=offset-distance;require(12<=base_offset<offset,'Git offset delta base bounds')
        elif kind==7:base_oid=f.read(20).hex()
        else:require(kind in (1,2,3,4),'saved Git object type')
        decoder=zlib.decompressobj();parts=[];produced=0
        while not decoder.eof:
            block=f.read(65536);require(block,'compressed packed object EOF')
            decoded=decoder.decompress(block,MAX_PACKED_BODY+1-produced);produced+=len(decoded)
            require(produced<=MAX_PACKED_BODY and not decoder.unconsumed_tail,'bounded packed object decode')
            parts.append(decoded)
        body=b''.join(parts);require(len(body)==size,'Git pack representation size')
    if kind==6:
        base_kind,base=pack_at(path,base_offset,depth+1);result=(base_kind,apply_delta(base,body))
    elif kind==7:
        base_kind,base=obj(base_oid);result=(base_kind,apply_delta(base,body))
    else:result=({1:'commit',2:'tree',3:'blob',4:'tag'}[kind],body)
    PACK_OBJECT_CACHE[key]=result;return result

def packed_obj(oid):
    for pool in POOLS:
        for idx in sorted((pool/'pack').glob('*.idx')):
            offset=lookup_offset(idx,oid)
            if offset is None:continue
            kind,body=pack_at(idx.with_suffix('.pack'),offset)
            raw=kind.encode()+b' '+str(len(body)).encode()+b'\0'+body
            require(hashlib.sha1(raw).hexdigest()==oid,'reconstructed packed Git object SHA1 '+oid)
            return kind,body
    raise AssertionError('saved Git object unavailable in loose or indexed packs '+oid)

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

def check_publication():
    N=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
    pub=B/'NATURAL141-PASS-PUBLICATION-V2-96MIB.json'
    publication_pin,data=pin(pub,'ef0771f9759a5702c4100fca5c56fdb826fbc563d47767d54048a9289c0000f5')
    j=json.loads(data);require(j['files_count']==len(j['files'])==73 and j['payload_bytes']==sum(r['bytes'] for r in j['files'])==4672092,'exact73 payload inventory')
    require(j['status']=='INDEXED_COMPLETE_EXPORT_BYTES_WITH_EXPLICIT_LOCAL_SPARSE_MATERIALIZATION' and j['every_blob_byte_readback'] and j['only_new_evidence_paths_skip_worktree'] and j['preexisting_index_entries_identical'],'actualpublisher result flags')
    require(not j['working_tree_materialized'] and not j['existing_files_deleted_or_hidden'] and not j['scientific_acceptance_promoted'] and not j['original_packet_distribution_complete'] and j['original_result_unchanged'],'byte publication only/historicfixedexport scope')
    source_pin,_=pin(B/'publish_natural141_pass_fixed_shmem_to_git_20261011_v2_96mib.py','7b464ff41bd45bca4a9356ebbb00c0193f8e8af3d34da9fc5ef023a07eac2218')
    gate_pin,gdata=pin(B/'ROOT-NATURAL141-96MIB-PUBLICATION-GATE.json');gate=json.loads(gdata)
    capacity_qc,cdata=pin(W/'design-qc/natural141-96mib-publisher-source-20261011T0209Z-solver_design_recovery/NATURAL141-96MIB-PUBLISHER-SOURCE-CAPACITY-QC-ATTEMPT1.json','b65b48b44adfde1361e83666a4eea7942b9f45971d2a3eedee590b008ca08c85');qc=json.loads(cdata)
    require(gate['source_sha256']==source_pin['sha256'] and gate['independent_source_capacity_review_sha256']==capacity_qc['sha256'] and gate['new_evidence_pool_limit_bytes']==96*1024*1024 and gate['scientific_global_limits_unchanged'] and not gate['scientific_scope_promoted'],'actual scoped gate/exact96MiB source')
    resultpin,rdata=pin(j['original_result_path'],'6db53e2eba1679cae6841cf1e2c6ffc37cd3d985873d0f8d73a8e2c17094bf30');result=json.loads(rdata)
    certpin,_=pin(N/'G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-CERTIFICATE-20261011T014055.249073Z.json','15525987280d430dcb83585aaf76f5a33042ece6f1a781eeb2ed51949bd78934')
    savedpin,_=pin(N/'design-qc/natural141-saved-20261011T0152Z-solver_design_recovery/NATURAL141-SAVED-QC-ATTEMPT2.json','6ed6b44b114704fb39a236a126b1f2a36197a6b443d53da5a2816a7efa5a19c4')
    acceptance=P/'lean/G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-ACCEPTANCE-20261011T0202Z.json'
    acceptpin,acceptbytes=pin(acceptance,'4b38e92700caa3ec2bd853b119fb2aa90d5cbf49af71081a1e6cfbbbcd73514d')
    require(gate['formal_scoped_acceptance_sha256']==acceptpin['sha256'],'separateformalacceptance binding')
    export=Path(j['export']);require(export==N/'lossless-export/proof141-20261011T014055.249073Z' and result['complete_lossless_export_original']==str(export),'retainedfixedexport')
    require((export/'PRESERVATION-MANIFEST.json').read_bytes()==rdata and not result['packet_distribution_complete'],'oldresultbytes/falsepacketflag preserved')
    expected_files={str(p) for p in export.rglob('*') if p.is_file()}
    require(expected_files=={r['original_path'] for r in j['files']},'all73actualexport files exactly represented')
    idx,index_pin=index_entries(INDEX.read_bytes());index_pin['path']=str(INDEX)
    checked=[];blobset=set()
    newprefix='research/2026-10-10-codex-lean-rust-parity/lean/evidence/git-preserved/natural141-pass-20261011T014055.249073Z/'
    for row in j['files']:
        original=Path(row['original_path']);treepath=row['git_tree_path']
        require(treepath==newprefix+str(original.relative_to(export)),'boundedexactnewtreepath')
        original_pin,raw=pin(original,row['sha256'],row['bytes']);require(not original.is_symlink(),'retainedregularoriginal')
        oid=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();require(oid==row['git_blob'],'rawblobobject identity')
        kind,body=obj(oid);require(kind=='blob' and body==raw,'completeGitblobreadback exact retainedoriginal')
        require(idx.get(treepath)=={'mode':0o100644,'git_blob':oid,'stage':0,'skip_worktree':True},'actualindexed100644stage0S')
        require(not (REPO/treepath).exists() and not (REPO/treepath).is_symlink(),'newpublished evidence intentionallysparse/unmaterialized')
        checked.append({'git_tree_path':treepath,'git_blob':oid,'original':original_pin,'indexed_regular_100644_stage0_S':True,'full_raw_Git_blob_bytes_equal_retained_original':True});blobset.add(oid)
    require(len({r['git_tree_path'] for r in checked})==73,'73uniqueactualstagedpaths')
    pool=POOLS[0];require(pool.is_symlink() and pool.resolve()==W/'metadata/git-object-pool-preserved-20261011','incomingandoldpoolcountedredirect unchanged')
    for row in qc['pool_current_files']:
        f=pool/row['relative'];pin(f,row['sha256'],row['bytes'])
    incoming=[]
    for row in qc['incoming_pack_files']:
        pp,_=pin(row['path'],row['sha256'],row['bytes']);incoming.append(pp)
    require(len(incoming)==3 and sum(x['bytes'] for x in incoming)==16568966,'all3incomingpeerpackwirebytes preserved')
    peer=qc['incoming_peer_commit_reported_by_policy'];peerroot,peerparents=commit_tree(peer)
    pool_content=sum(p.stat().st_size for p in pool.rglob('*') if p.is_file())
    require(j['before']['object_pool_bytes']==73080592 and j['after']['object_pool_bytes']==77396317 and j['after']['object_pool_bytes']<96*1024*1024,'actualopaque pool before/afterfundedquota')
    require(pool_content>=j['after']['object_pool_bytes'] and pool_content<96*1024*1024,'currentpool preservation/growth within96MiB')
    require(j['before']['overlay_free_bytes']>8*1024*1024 and j['after']['overlay_free_bytes']>8*1024*1024,'executedunchanged8MiBfloors')
    plan=json.loads((N/'RESOURCE-AND-RUN-PLAN.json').read_bytes())
    require((plan['scratch_hard_limit_bytes'],plan['scratch_abort_bytes'],plan['memory_abort_bytes'])==(2*1024**3,15*1024**3//8,15*1024**3),'scientificlimitsunchanged')
    # Previous189pathsremainindexed exactly. No unsaved before-index snapshot is invented.
    oldqc= W/'design-qc/git-publication-and-relocation-saved-20261011T0121Z-solver_design_recovery/NEW-PATH-PUBLICATION-AND-RELOCATION-SAVED-QC-ATTEMPT2.json'
    oldpin,olddata=pin(oldqc,'88ffb5e583fb78e0b4e76d9e35a4d19abe914c367281798506e4d2e618540226');old=json.loads(olddata)
    previous_checked=0
    for group in old['checked_receipts']:
        for row in group['rows']:
            require(idx.get(row['git_tree_path'])=={'mode':0o100644,'git_blob':row['git_blob'],'stage':0,'skip_worktree':True},'prior189newpathindexbindings retained');previous_checked+=1
    require(previous_checked==189,'completeprevious189index bindings')
    return {'schema':'natural141_complete73_git_publication_independent_saved_byte_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'status':'PASS_SAVED_COMPLETE73_REGULAR_GIT_BLOBS_INDEX_SPARSE_ORIGINALS_AND_PRESERVED_PEER_PACK','reviewer_sha256':digest(Path(__file__).read_bytes()),'publication':publication_pin,'source':source_pin,'actual_root_gate':gate_pin,'source_capacity_qc':capacity_qc,'formal_separate_natural_acceptance':acceptpin,'unchanged_result':resultpin,'unchanged_certificate':certpin,'full_saved_scientific_qc':savedpin,'counts':{'exportfiles':73,'content_bytes':4672092,'distinct_blobs':len(blobset),'exactoldopaque_pool_files_rehashed':qc['pool_current_file_count'],'prior189indexbindingsretained':previous_checked},'checked_rows':checked,'current_index_snapshot':index_pin,'incoming_peer_pack_files':incoming,'incoming_peer_commit_object':{'sha1':peer,'tree':peerroot,'parents':peerparents,'all_raw_object_SHA1_checks_passed':True},'opaque_pool_content_bytes_current':pool_content,'global_caps_unchanged':{'scratchhard':plan['scratch_hard_limit_bytes'],'scratchabort':plan['scratch_abort_bytes'],'memorynonreclaimabort':plan['memory_abort_bytes']},'qualification':['Current73index100644stage0S/fullrawblob/originalbytes independentlychecked; no commit/remote publication is asserted for these new paths.','All2349prepublicationopaque objects and incomingpeer3packfiles remain literal bytes; Git commit/tree identity alone supplies no new mathematical or private loader replay acceptance.','The pinned executedpublisher asserts complete preexisting-indexstage equality; independent saved reviewer verifies allprior189 recordednewpath bindings and current73. No unsaved all-indexbefore snapshot or arbitrary preexisting identity claim synthesized.','Originalfixed-shmemcapacity receipt and certificate unchanged. Evidencetransport never widens1504/coherentunion, native/source provenance, biological constructor/calibrated decoder or master scope.'],'git_commands_or_mutations':0,'target_imports_or_producer_processes':0,'overlay_writes':0}

if __name__=='__main__':
    output=Path(sys.argv[1])
    try:result=check_publication()
    except Exception as e:
        result={'schema':'natural141_complete73_git_publication_independent_saved_byte_qc_v1','contributor':'Codex / solver_design_recovery','status':'FAIL_OWN_SAVED_PUBLICATION_READER','observed_utc':datetime.now(timezone.utc).isoformat(),'error_type':type(e).__name__,'error':str(e),'reviewer_sha256':digest(Path(__file__).read_bytes()),'git_commands_or_mutations':0,'target_imports_or_producer_processes':0,'overlay_writes':0}
        with output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
        print(json.dumps({'receipt':str(output),'sha256':digest(output.read_bytes()),'status':result['status']}));sys.exit(1)
    with output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'receipt':str(output),'sha256':digest(output.read_bytes()),'status':result['status'],'counts':result['counts'],'index':result['current_index_snapshot']}))
