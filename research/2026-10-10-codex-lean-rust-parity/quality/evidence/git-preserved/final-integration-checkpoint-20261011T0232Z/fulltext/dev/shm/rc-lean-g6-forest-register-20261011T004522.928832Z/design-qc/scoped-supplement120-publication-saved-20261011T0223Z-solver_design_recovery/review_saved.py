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

import os
import traceback
Q=W/'design-qc/scoped-supplement120-publication-saved-20261011T0223Z-solver_design_recovery'

def check():
    pubinfo,pubdata=pin(B/'FULL-SCOPED-SUPPLEMENT-PUBLICATION.json','02cca07d2e1ff6d2fafc3ccf3e1f4f297092b833e5728ec90a90c86a98c5e45b');pub=json.loads(pubdata)
    gateinfo,gatedata=pin(B/'ROOT-FULL-SUPPLEMENT-PUBLICATION-GATE.json','7e73d27242459ca13986becd9b95f6fee605b247b87c66cf532378ec4388a440');gate=json.loads(gatedata)
    sourceinfo,sourcedata=pin(B/'publish_full_scoped_supplement_20261011.py','58ac463496e55fc8ae9d67ac5bb4731d1275e5c92b0de759d83c8925aaa20e8e')
    qinfo,qdata=pin(W/'design-qc/scoped-supplement-publisher-source-20261011T0220Z-solver_design_recovery/SCOPED-SUPPLEMENT-PUBLISHER-SOURCE-CAPACITY-QC-ATTEMPT1.json','a7dd534579861f336ecbe0e59ca3fd16d0b3993d6823de7161fd1f53c28f6364');sourceqc=json.loads(qdata)
    minfo,mdata=pin(B/'SUPPLEMENTAL-PUBLICATION-INPUTS-V2.json','bbb443e9fbfb61a157b6dc24d5d0995791fb562b9381a41e7bb886ce72cab26c');manifest=json.loads(mdata)
    require(gate['source_sha256']==sourceinfo['sha256'] and gate['independent_source_capacity_review_sha256']==qinfo['sha256'] and gate['global_limits_unchanged'] and not gate['scientific_scope_promoted'],'exact root fixed-publication gate')
    require(pub['files_count']==120 and len(pub['files'])==120 and pub['payload_bytes']==6848926,'actual120 count/bytes')
    require(pub['input_manifest_sha256']==minfo['sha256'] and pub['input_manifest_path']==str(B/'SUPPLEMENTAL-PUBLICATION-INPUTS-V2.json'),'input manifest exact')
    require(pub['preexisting_index_entries_identical'] and pub['every_blob_byte_readback'] and pub['only_new_evidence_paths_skip_worktree'] and not pub['existing_files_deleted_or_hidden'] and not pub['scientific_acceptance_promoted'],'exact saved protocol flags')
    expected=[dict(x) for x in manifest['files']]
    for name,path,data in [('INPUT-MANIFEST.json',B/'SUPPLEMENTAL-PUBLICATION-INPUTS-V2.json',mdata),('PUBLISHER.py',B/'publish_full_scoped_supplement_20261011.py',sourcedata)]:
        expected.append({'source_path':str(path),'git_tree_path':manifest['prefix']+'/'+name,'bytes':len(data),'sha256':digest(data)})
    idxdata=INDEX.read_bytes();entries,idxmeta=index_entries(idxdata)
    require(idxmeta['entry_count']==sourceqc['checks']['current_index']['entry_count']+120==103092,'current index102972+120')
    require(len(idxdata)==pub['after']['index_bytes']==9678380,'actual after index bytes')
    require(pub['before']['index_bytes']==sourceqc['checks']['current_index']['bytes']==9664711,'dated before index bound')
    checked=[]
    for row,exp in zip(pub['files'],expected):
        require(all(row[k]==v for k,v in exp.items()),'full saved row matches fixed source manifest')
        info,data=pin(row['source_path'],row['sha256'],row['bytes']);data.decode('utf8');require(not data.startswith(b'\x7fELF'),'full text excludesELF')
        oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();require(oid==row['git_blob'],'rawGitblobSHA1')
        require(entries.get(row['git_tree_path'])=={'mode':0o100644,'git_blob':oid,'stage':0,'skip_worktree':True},'exact current regular stage0 S '+row['git_tree_path'])
        kind,body=obj(oid);require(kind=='blob' and body==data,'independent full Gitblob readback '+row['git_tree_path'])
        require(not os.path.lexists(REPO/row['git_tree_path']),'new path remains explicitly sparse')
        checked.append({**row,'regular_stage0_S':True,'full_original_equals_Git_bytes':True})
    old=[];oldpins=[]
    for name,h,count in [('NATURAL-5F-FAILURE-PUBLICATION.json','91c3398ff7cb9167d4efacdcd835da5ab831ad5f17a165c624d675fb6ed642d3',53),('PRIVATE-SELECTED-PREFIX-PUBLICATION-20261011T0136Z.json','61defdc7615c744da487f12c47528d49f9bb070ea7850866d0ac40107f3d874a',87),('NATURAL141-PASS-PUBLICATION-V2-96MIB.json','ef0771f9759a5702c4100fca5c56fdb826fbc563d47767d54048a9289c0000f5',73)]:
        info,data=pin(B/name,h);j=json.loads(data);oldpins.append(info);require(j['files_count']==len(j['files'])==count,'prior exact count')
        for row in j['files']:
            _,original=pin(row['original_path'],row['sha256'],row['bytes']);kind,body=obj(row['git_blob']);require(kind=='blob' and body==original,'prior full blob retained')
            require(entries.get(row['git_tree_path'])=={'mode':0o100644,'git_blob':row['git_blob'],'stage':0,'skip_worktree':True},'prior recorded index retained')
            old.append((row['git_tree_path'],row['git_blob'],row['sha256'],row['bytes']))
    require(len(old)==len({x[0] for x in old})==213,'all213 prior recorded paths retained')
    upinfo,updata=pin(B/'UPSTREAM-F8120B1-EXACT-INDEX-INTEGRATION-RECEIPT.json','9718621759fe5ccef37acbcf6952b571e8932d12e4c390974d312a02a9e48acd');up=json.loads(updata)
    require(up['peer_head']=='f8120b1e413b64303891f7f2f8007169856c03f3' and up['upstream_paths']==len(up['rows'])==1625,'exact recorded upstream1625')
    root,parents=commit_tree(up['peer_head']);up_rows=[];new_sparse=0;new_physical=0
    for row in up['rows']:
        target=row['path'];entry=entries.get(target);require(entry is not None and entry['mode']==0o100644 and entry['stage']==0 and entry['git_blob']==row['git_blob'],'upstream index retained '+target)
        require(tree_path(root,target)==(row['mode'],row['git_blob']),'exact peer tree row '+target)
        kind,body=obj(row['git_blob']);require(kind=='blob' and len(body)==row['bytes'] and digest(body)==row['sha256'],'recorded upstream full raw bytes '+target)
        path=REPO/target
        if path.exists():
            require(path.is_file() and path.read_bytes()==body,'exact materialized incoming bytes')
            new_physical+=int(row['upstream_status']=='A')
        else:
            require(entry['skip_worktree'] and row['upstream_status']=='A','incoming absence explicit new sparse')
            new_sparse+=1
        up_rows.append((target,row['mode'],row['git_blob'],row['sha256'],row['bytes']))
    require((new_sparse,new_physical)==(1619,5),'incoming1619new sparse+5small new physical')
    require(INDEX.read_bytes()==idxdata,'current index remained frozen throughout readback')
    poolbytes=sum(p.stat().st_size for p in POOLS[0].rglob('*') if p.is_file());require(poolbytes==pub['after']['object_pool_bytes']==79335125 and poolbytes<96*1024*1024,'actual96MiB pool receipt unchanged')
    ov=os.statvfs('/workspace');overlay=ov.f_bavail*ov.f_frsize;require(overlay>=pub['after']['overlay_free_bytes']>8*1024*1024,'current overlay floor remains')
    return {'publication':pubinfo,'root_gate':gateinfo,'exact_executed_source':sourceinfo,'fixed_manifest':minfo,'independent_source_capacity_review':qinfo,'all120_original_index_Git_bytes_checked':checked,'total_bytes':sum(x['bytes'] for x in checked),'current_index':idxmeta,'prior_recorded213_publications':oldpins,'all213_original_and_blob_bytes_and_index_bindings_retained':True,'prior213_canonical_bindings_sha256':digest(json.dumps(old,sort_keys=True,separators=(',',':')).encode()),'upstream_receipt':upinfo,'upstream_peer_commit':up['peer_head'],'upstream_peer_root':root,'all1625_recorded_peer_tree_index_full_bytes_retained':True,'upstream1625_canonical_bindings_sha256':digest(json.dumps(up_rows,sort_keys=True,separators=(',',':')).encode()),'incoming1619_new_sparse_and5_small_materialized':True,'actual_pool_bytes':poolbytes,'overlay_free_bytes_readback':overlay,'whole_preexisting102972_stage_byte_identity':'The pinned executed publisher checks exact preexisting stage-byte equality. This independent reader verifies all213 recorded prior paths and all1625 upstream rows; it does not assert an unavailable independent complete before-stage snapshot.','peer_acceptance_or_native_trace_replayed':False,'scientific_source_proof_acceptance_changed':False,'no_Git_commands_mutations_target_imports_or_producer_invocation':True,'remote_commit_push_acceptance_claimed':False}
report={'schema':'INDEPENDENT_FIXED_SUPPLEMENT120_SAVED_GIT_BYTES_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes())}
try:report['checks']=check();report['status']='PASS_ALL120_FULL_TEXT_GIT_BYTES_WITH_PRIOR213_AND_UPSTREAM1625_RETAINED'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
out=Q/'SCOPED-SUPPLEMENT120-SAVED-GIT-BYTE-QC-ATTEMPT1.json';require(not out.exists(),'immutable own receipt');out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(out.read_bytes()),'bytes':out.stat().st_size,'error':report.get('error'),'index':report.get('checks',{}).get('current_index')}))
