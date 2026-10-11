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
MAX_PACKED_BODY=4*1024*1024

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


import stat
Q=W/'design-qc/fetch620-resource-hold-20261011T0244Z-solver_design_recovery'
PARENT_READER_SHA256='d38a29eb2c2546eccd30ff45321f2805eadab2b9061d1984f343cf51f6897a0d'
MAX_OWN_DIRECTORY_BYTES=65536


def canonical_hash(value):return digest(json.dumps(value,sort_keys=True,separators=(',',':')).encode())

def load_json(path,sha256,size=None):
    info,data=pin(path,sha256,size);return info,json.loads(data)

def free_bytes(path):
    s=os.statvfs(path);return s.f_bavail*s.f_frsize

def allocation(roots,follow_file_symlinks=False):
    seen=set();total=0;symlinks=0
    for root in roots:
        for directory,dirs,files in os.walk(root,followlinks=False):
            for path in [Path(directory),*(Path(directory)/f for f in files)]:
                before=path.lstat();symlinks+=int(stat.S_ISLNK(before.st_mode))
                s=path.stat() if follow_file_symlinks and stat.S_ISLNK(before.st_mode) else before
                key=(s.st_dev,s.st_ino)
                if key not in seen:seen.add(key);total+=s.st_blocks*512
    return {'distinct_allocated_bytes':total,'distinct_inodes':len(seen),'file_symlink_occurrences':symlinks,'follows_directory_symlinks':False,'follows_file_symlinks':follow_file_symlinks}

def flatten_tree(root):
    rows={}
    def visit(oid,prefix):
        for name,(mode,child) in tree(oid).items():
            path=prefix+name
            if mode=='40000':visit(child,path+'/')
            else:
                require(path not in rows,'unique flattened tree path');rows[path]=(mode,child)
    visit(root,'');return rows

def encode_tree(entries):
    trie={}
    for path,value in entries.items():
        node=trie;names=path.encode('utf8','surrogateescape').split(b'/')
        for name in names[:-1]:
            require(name not in node or isinstance(node[name],dict),'tree file/directory collision');node=node.setdefault(name,{})
        require(names[-1] not in node,'tree unique file');node[names[-1]]=value
    encoded=[]
    def visit(node):
        children=[]
        for name,value in node.items():
            if isinstance(value,dict):children.append((name,'40000',visit(value),True))
            else:mode,oid=value;children.append((name,mode,oid,False))
        body=b''.join(mode.encode()+b' '+name+b'\0'+bytes.fromhex(oid) for name,mode,oid,isdir in sorted(children,key=lambda x:x[0]+(b'/' if x[3] else b'')))
        full=b'tree '+str(len(body)).encode()+b'\0'+body;oid=hashlib.sha1(full).hexdigest()
        encoded.append((oid,body,len(zlib.compress(full,6))))
        return oid
    return visit(trie),encoded

def object_present(oid):
    for pool in POOLS:
        if (pool/oid[:2]/oid[2:]).is_file():return True
        for idx in sorted((pool/'pack').glob('*.idx')):
            if lookup_offset(idx,oid) is not None:return True
    return False

def check():
    pins=[]
    def lj(name,h,size=None):
        info,j=load_json(B/name,h,size);pins.append(info);return j
    result=lj('FRESH-MAIN-62020166-FETCH-RESULT.json','7b749f5cc6de951a36ace7db07014a22a1cf543dafacd8deaef0a72099dd004d',796)
    admission=lj('FRESH-MAIN-62020166-FETCH-ADMISSION.json','d4b86ee68df49e232dcae09dc39b1c8c4bdce87c83633df6c6bbd838fbd16df1',2084)
    require(result['exit_code']==0 and result['gate_sha256']==pins[-1]['sha256'],'successful Git fetch exact admission binding')
    require(len(result['new_pack_files'])==3 and len(admission['before_pack_inventory'])==6,'three new/six prior pack files')
    pack_rows=[]
    for group,rows in [('old_preserved',admission['before_pack_inventory']),('new_preserved',result['new_pack_files'])]:
        for rel,row in sorted(rows.items()):
            require(rel.startswith('pack/') and '..' not in Path(rel).parts,'bounded saved pack path')
            info,data=pin(POOLS[0]/rel,row['sha256'],row['bytes'])
            if rel.endswith('.pack'):
                require(data[:4]==b'PACK' and hashlib.sha1(data[:-20]).digest()==data[-20:],'full Git pack trailer checksum')
            pack_rows.append({**info,'classification':group,'full_pack_trailer_sha1_checked':rel.endswith('.pack')})
    new_bytes=sum(x['bytes'] for x in pack_rows if x['classification']=='new_preserved')
    require(new_bytes==result['new_pack_bytes']==17494055,'actual new pack bytes')
    require(admission['fetch_envelope_bytes']==16777216 and admission['missing_raw_blob_bytes']==14034446,'historical estimate and missing raw-byte inventory')
    require(new_bytes>admission['fetch_envelope_bytes'],'estimate overrun actually occurred')
    pool_inventory=[]
    logical_pool=POOLS[0];resolved_pool=logical_pool.resolve()
    require(logical_pool.is_symlink() and resolved_pool==W/'metadata/git-object-pool-preserved-20261011','retained logical pool redirects to counted forest context')
    for path in sorted(logical_pool.rglob('*')):
        if path.is_file():
            require(not path.is_symlink(),'regular compressed object/pack files retained')
            pool_inventory.append((str(path.relative_to(logical_pool)),path.stat().st_size))
    pool_bytes=sum(x[1] for x in pool_inventory)
    require(pool_bytes==result['pool_bytes']==admission['pool_bytes']+new_bytes==99267430,'exact actual pool arithmetic after fetch')
    require(pool_bytes<100663296,'fixed96MiB pool current cap')
    captures=[]
    for n,h,size in [('FRESH-MAIN-62020166-FETCH.stdout','e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',0),('FRESH-MAIN-62020166-FETCH.stderr','296e93c16a5092aa8c14098740e858736798df53146e938afe86beeb3d90e952',129)]:
        info,data=pin(B/n,h,size);captures.append(info)
    minfo,manifest=load_json(B/'FINAL-CHECKPOINT-FULLTEXT-MANIFEST.json','6da6de0eae650f8095106ab6aae21b2099789bc1e9c7511098d3ad438aadb25e',38464)
    pinfo,publication=load_json(B/'FINAL-CHECKPOINT-FULLTEXT-PUBLICATION.json','6e1909adedb0fe627e2d0e0a693bf10fdc9636de5da19fdf68cfa0b200dc7ec2',41168)
    gateinfo,gate=load_json(B/'ROOT-FINAL-CHECKPOINT-MANIFEST-CONFIG-GATE.json','3ff8c50c87fe513c242cb7c7dd382386c2320af8996126ae5d47c583676998db',2864)
    sourceinfo,source=pin(B/'preserve_final_checkpoint_text_blobs_20261011.py','a1d507d36383d9e7614b1fc2166e77210d730f18ee9b2d818fc82750d7f8b791')
    configinfo,config=load_json(manifest['resource_config'],'2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c',4477)
    require(manifest['publisher_sha256']==publication['publisher_sha256']==sourceinfo['sha256'],'fixed source and receipt exact binding')
    require(manifest['resource_config_sha256']==configinfo['sha256'] and manifest['ordered_allocation_roots']==config['allocation_roots'],'exact ordered resource configuration roots')
    roots=config['allocation_roots'];require(len(roots)==len(set(roots))==26 and all(Path(p).is_dir() for p in roots),'all exact26 unique roots present')
    require((config['scratch_abort_bytes'],config['scratch_hard_limit_bytes'],config['memory_abort_bytes'])==(2013265920,2147483648,16106127360),'unchanged global fixed caps')
    require(manifest['files_count']==len(manifest['files'])==58 and manifest['payload_bytes']==4879819,'fixed58 original metadata inputs')
    require(publication['files_count']==len(publication['files'])==59 and publication['payload_bytes']==4918283,'saved59 final metadata payload')
    require(publication['manifest_sha256']==minfo['sha256'] and publication['manifest_path']==minfo['path'],'exact input manifest in saved publication')
    expected=[dict(r) for r in manifest['files']]
    expected.append({'source_path':minfo['path'],'git_tree_path':manifest['prefix']+'/INPUT-MANIFEST.json','bytes':minfo['bytes'],'sha256':minfo['sha256']})
    idxdata=INDEX.read_bytes();entries,idxmeta=index_entries(idxdata)
    checked=[]
    for row,exp in zip(publication['files'],expected):
        require(all(row[k]==v for k,v in exp.items()),'all59 exact source-row bindings')
        path=Path(row['source_path']);require(path.is_file() and not path.is_symlink(),'all59 current original regular files retained')
        info,data=pin(path,row['sha256'],row['bytes']);data.decode('utf8');require(not data.startswith(b'\x7fELF'),'UTF8 complete metadata excludesELF')
        oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(oid==row['git_blob'],'all59 rawGitblobSHA1')
        require(entries.get(row['git_tree_path'])=={'mode':0o100644,'git_blob':oid,'stage':0,'skip_worktree':True},'all59 current exact regular100644 stage0 S')
        kind,body=obj(oid);require(kind=='blob' and body==data,'all59 independent full blob readback')
        require(not os.path.lexists(REPO/row['git_tree_path']),'only recorded new59 metadata paths explicitly sparse')
        checked.append((row['source_path'],row['git_tree_path'],oid,row['sha256'],row['bytes']))
    require(sum(r[4] for r in checked)==4918283,'all59 payload sum')
    preinfo,preflight=load_json(B/'UPSTREAM-62020166-EXACT-BYTE-PREFLIGHT-V2.json','dc91c9f43ded02823d6254e8405fc42bb77e78849ba6220345c9ce504e832dce',653286)
    readerinfo,readerdata=pin(B/'preflight_upstream620_exact_trees_v2.py','92bb5a29fbd832be1bbeb8c500a3c08c970f794e5308f024e5cac26d9e5f01d5',4439)
    old_root,_=commit_tree(preflight['from']);new_root,_=commit_tree(preflight['to'])
    old_tree=flatten_tree(old_root);new_tree=flatten_tree(new_root)
    changes={p:('A' if p not in old_tree else 'M') for p,v in new_tree.items() if old_tree.get(p)!=v}
    require(not (set(old_tree)-set(new_tree)),'upstream no deletion')
    rows=preflight['rows'];require(len(rows)==len(changes)==1642 and sum(s=='A' for s in changes.values())==1641,'exact full tree1641A+1M diff')
    require({r['git_tree_path']:r['status'] for r in rows}==changes,'saved V2 rows complete exact upstream difference')
    incoming=[];future={p:(format(v['mode'],'o'),v['git_blob']) for p,v in entries.items()}
    current_tree,current_encoded=encode_tree(future)
    require(current_tree==preflight['current_tree_prediction_matches_exact_prior_git_write_tree']=='cb1a2771a31637f8a411f7584848d237fd3f601c','independent current full index pure tree matches prior actual write-tree')
    require(obj(current_tree)==('tree',current_encoded[-1][1]),'current serialized root body equals saved object')
    for row in rows:
        path=row['git_tree_path'];require(new_tree[path]==(row['mode'],row['git_blob']) and row['mode']=='100644','all1642 exact new commit mode/blob')
        kind,data=obj(row['git_blob']);require(kind=='blob' and len(data)==row['bytes'] and digest(data)==row['sha256'],'all1642 captured upstream full bytes')
        if row['status']=='A':require(path not in entries and not os.path.lexists(REPO/path),'all1641 genuinely new absent paths before rollforward')
        else:
            require(path=='research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md','only old physical scope modified')
            require((format(entries[path]['mode'],'o'),entries[path]['git_blob'])==old_tree[path],'old live scope index equalsoldcommit')
            require((REPO/path).read_bytes()==obj(old_tree[path][1])[1],'old live scope exact original before rollforward')
        future[path]=(row['mode'],row['git_blob']);incoming.append((path,row['status'],row['mode'],row['git_blob'],row['sha256'],row['bytes']))
    future_root,encoded=encode_tree(future)
    missing=[{'git_object':oid,'uncompressed_bytes':len(body),'compressed_level6_bytes':compressed} for oid,body,compressed in encoded if not object_present(oid)]
    require(future_root==preflight['future_tree_without_ordinary_notes']=='5481499b6738ad04919b661ee6792910605bbcfb','independent future tree identity')
    require(missing==preflight['missing_trees'] and len(missing)==2 and sum(r['compressed_level6_bytes'] for r in missing)==25827,'exact2 new tree objects level6 content25827bytes')
    require(len(future)==preflight['future_full_entries']==105092,'full future index entries conditional upstream only')
    require(INDEX.read_bytes()==idxdata,'current index remained fixed during independent byte/tree readback')
    logical=allocation(roots);followed=allocation(roots,True)
    mem={k:int(v) for k,v in (line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())}
    nonreclaim=sum(mem[k] for k in ('anon','shmem','kernel'))
    tmp_free=free_bytes('/tmp');overlay_free=free_bytes('/workspace')
    require(max(logical['distinct_allocated_bytes'],followed['distinct_allocated_bytes'])+MAX_OWN_DIRECTORY_BYTES<config['scratch_abort_bytes'],'current global allocations plus bounded QC below fixed abort')
    require(nonreclaim<config['memory_abort_bytes'],'actual nonreclaim below15GiB')
    require(tmp_free>len(idxdata)+2097152,'current tmp fits fullindexlock+2MiB')
    require(overlay_free>8388608,'actual overlay8MiB floor')
    require(sum(p.stat().st_size for p in logical_pool.rglob('*') if p.is_file())==pool_bytes,'pool content size remains fixed throughout readback')
    require(pool_bytes+4194304>100663296,'old4MiB future-tree reserve publisher now held by fixed pool preflight')
    resources={'pool_bytes':pool_bytes,'pool_fixed_limit_bytes':100663296,'pool_remaining_bytes':100663296-pool_bytes,'pool_files':len(pool_inventory),'pool_inventory_path_size_sha256':canonical_hash(pool_inventory),'logical_pool':str(logical_pool),'resolved_counted_pool':str(resolved_pool),'config':configinfo,'ordered26_roots':roots,'guard_lstat':logical,'conservative_followed_file_targets':followed,'scratch_abort_bytes':2013265920,'scratch_hard_limit_bytes':2147483648,'bounded_own_QC_reserve_bytes':MAX_OWN_DIRECTORY_BYTES,'memory_components':{k:mem[k] for k in ('anon','shmem','kernel')},'nonreclaimable_bytes':nonreclaim,'memory_abort_bytes':16106127360,'tmp_free_bytes':tmp_free,'index_lock_plus2MiB_requirement_bytes':len(idxdata)+2097152,'overlay_free_bytes':overlay_free,'overlay_floor_bytes':8388608,'instantaneous_measurement_only':True}
    return {'fetch_result':pins[0],'historical_admission':pins[1],'Git_fetch_exit_code':0,'admission_estimate_bytes':16777216,'actual_new_pack_bytes':new_bytes,'estimate_overrun_bytes':new_bytes-16777216,'missing_raw_blob_inventory_bytes':14034446,'missing_raw_inventory_is_not_a_Git_wire_or_pack_size_bound':True,'historical_admission_does_not_authorize_more_fetch_or_publication':'Actual fetch succeeded; its estimate and post-fetch envelope assertion failed. Git negotiation may transfer objects already present but not reachable from advertised refs. This reader verifies the actual preserved files and does not infer the mechanism of each duplicate object.','all3_new_and6_prior_complete_pack_files_authenticated':pack_rows,'fetch_captures':captures,'resources':resources,'final_checkpoint_manifest':minfo,'actual_final59_publication':pinfo,'publisher_source':sourceinfo,'external_manifest_config_gate':gateinfo,'all59_original_complete_text_equals_Git_blob_and_current_regular_stage0_S':True,'final59_canonical_bindings_sha256':canonical_hash(checked),'final59_payload_bytes':4918283,'current_index_snapshot':idxmeta,'publisher_all_preexisting_index_exact_flag_is_saved_attestation_only':True,'upstream_V2_preflight':preinfo,'upstream_V2_reader_source':readerinfo,'upstream_old_commit_root':old_root,'upstream_new_commit_root':new_root,'all1642_captured_new_commit_full_bytes_authenticated':True,'upstream1642_canonical_bindings_sha256':canonical_hash(incoming),'current_index_tree_prediction':current_tree,'conditional_upstream_only_tree':future_root,'conditional_missing_tree_objects':missing,'conditional_new_tree_zlib6_content_bytes':25827,'tree_content_only_funding_is_not_complete_publication_funding':True,'old4MiB_reserve_publisher_now_held':True,'recovery_requirements':['No further fetch, no pool-cap increase, no deletion or hiding of old bytes.','Root must freeze exact remaining source/metadata rows and all still-missing zlib-level6 Git blob and tree bytes, including filesystem allocation, temporary/index/commit costs and late receipts.','Require fresh ordered26-root/global scratch/nonreclaimable/tmp/index/overlay measurements before mutation and an exact root publication gate.','Thin prospective1575 source delta remains static; public1570 audit review is separate. No staging, context, compiler, native, source-fit or kernel admission is authorized by this resource receipt.'],'no_Git_commands_or_index_object_ref_changes_or_target_imports_or_producers_by_this_reader':True,'remote_publication_or_scientific_admission_claimed':False}

report={'schema':'FETCH620_PRESERVED_BYTES_CURRENT_RESOURCE_AND_CONDITIONAL_RECOVERY_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes()),'authenticated_own_Git_reader_parent_sha256':PARENT_READER_SHA256}
try:report['checks']=check();report['status']='PASS_PRESERVED_BYTES_AND_CURRENT_FIXED_CAPS_WITH_FETCH_ENVELOPE_HOLD'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
data=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
require(sum(p.stat().st_size for p in Q.iterdir() if p.is_file())+len(data)<MAX_OWN_DIRECTORY_BYTES,'new QC directory bounded below64KiB')
out=Q/'FETCH620-RESOURCE-HOLD-AND-CONDITIONAL-RECOVERY-QC-ATTEMPT1.json'
require(not out.exists(),'immutable independent receipt');out.write_bytes(data)
print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(data),'bytes':len(data),'reviewer_sha256':report['reviewer_sha256'],'error':report.get('error'),'resources':report.get('checks',{}).get('resources'),'directory_bytes':sum(p.stat().st_size for p in Q.iterdir() if p.is_file())}))
