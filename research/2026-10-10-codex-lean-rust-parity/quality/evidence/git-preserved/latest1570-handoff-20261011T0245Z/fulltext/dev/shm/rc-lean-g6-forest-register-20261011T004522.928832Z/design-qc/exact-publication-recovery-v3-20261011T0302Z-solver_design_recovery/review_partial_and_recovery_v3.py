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
def canonical_hash(value):return digest(json.dumps(value,sort_keys=True,separators=(',',':')).encode())
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
def stage_bytes(entries):
    return b''.join((format(v['mode'],'06o')+' '+v['git_blob']+' '+str(v['stage'])+'\t'+p+'\0').encode('utf8','surrogateescape') for p,v in sorted(entries.items(),key=lambda x:x[0].encode('utf8','surrogateescape')))
def current_head():
    head=(REPO/'.git/HEAD').read_text().strip()
    if not head.startswith('ref: '):return head
    path=REPO/'.git'/head[5:]
    if path.is_file():return path.read_text().strip()
    rows=(REPO/'.git/packed-refs').read_text().splitlines()
    return next(line.split()[0] for line in rows if not line.startswith(('#','^')) and line.split()[1]==head[5:])

import ast
import copy
import difflib
import stat
Q=W/'design-qc/exact-publication-recovery-v3-20261011T0302Z-solver_design_recovery'
MAX_OWN_ALLOC=65536
RECOVERY_SHA='a27f769183d758ce4fe21858f004de19239c8b04a32a4c947662f555dfa41e67'

def jp(path,h,size=None):
    info,data=pin(path,h,size);return info,json.loads(data)

def source_check(v2,v3,patch):
    actualdiff=''.join(difflib.unified_diff(v2.decode().splitlines(True),v3.decode().splitlines(True),fromfile='recover_exact_compressed_checkpoint_v2_20261011.py',tofile='recover_exact_compressed_checkpoint_v3_20261011.py'))
    require(actualdiff.encode()==patch,'exactfull frozenV2→V3 source diff')
    oldast=ast.parse(v2);newast=ast.parse(v3);normal=copy.deepcopy(newast)
    function=next(n for n in normal.body if isinstance(n,ast.FunctionDef) and n.name=='write_blob_preserving_existing')
    outer=next(n for n in function.body if isinstance(n,ast.If));require(len(outer.body)==4,'exactexistingbranch catfile/originalset/strictif/return')
    assignment=outer.body[1];branch=outer.body[2]
    require(isinstance(assignment,ast.Assign) and isinstance(assignment.targets[0],ast.Name) and assignment.targets[0].id=='original_missing','exact originalgate missingOID set')
    require(isinstance(branch,ast.If) and isinstance(branch.test,ast.Compare) and isinstance(branch.test.comparators[0],ast.Name) and branch.test.comparators[0].id=='original_missing','existingbutoriginalmissing remainsstrict')
    require(any(isinstance(n,ast.Assert) for n in branch.body),'exactnewlyheldlength guard')
    outer.body=[outer.body[0],outer.body[-1]]
    replacements={'EXACT-COMPRESSED-CHECKPOINT-RECOVERY-V3-GATE.json':'EXACT-COMPRESSED-CHECKPOINT-RECOVERY-V2-GATE.json','READY_SAME_FROZEN_PUBLICATION_V3_RECOVERY_INDEPENDENT_REVIEW_REQUIRED':'READY_SAME_FROZEN_PUBLICATION_V2_RECOVERY_INDEPENDENT_REVIEW_REQUIRED','PASS_EXACT_COMPRESSED_CHECKPOINT_BYTES_AND_UPSTREAM_INDEX_TREE_AFTER_V3_RECOVERY':'PASS_EXACT_COMPRESSED_CHECKPOINT_BYTES_AND_UPSTREAM_INDEX_TREE_AFTER_V2_RECOVERY'}
    changed=[]
    for node in ast.walk(normal):
        if isinstance(node,ast.Constant) and node.value in replacements if isinstance(node,ast.Constant) and isinstance(node.value,str) else False:
            changed.append(node.value);node.value=replacements[node.value]
    require(set(changed)==set(replacements) and len(changed)==3,'only3V3 metadata naming constants')
    require(ast.dump(normal,include_attributes=False)==ast.dump(oldast,include_attributes=False),'wholeASTequalV2except strictoriginalmissingpredicate+3names')
    text=v3.decode()
    for token in ["original_pins()","A.sha(before)==g['prior_index_sha256']","scope['git_tree_path']).read_bytes()==A.git('cat-file','blob',scope['git_blob'])","path.stat().st_size==x['zlib6_content_bytes']","A.git('write-tree').decode().strip()==future","L.A.write_blob=write_blob_preserving_existing"]:
        require(token in text,'fixedrecovery protocol token '+token)
    require('os.replace' not in text and 'unlink' not in text and 'rmtree' not in text,'recoverydoesnotrewrite physicalscope ordelete originals')
    return {'exactfull_AST_delta_from_preservedV2':'Four inserted source lines add original-gate missing OID exact loose length guard, plus three gate/status V3 names. No other executable AST change.','V2_preserved_unexecuted_recovery_source_and_readonly_gate':True,'existing_at_original_gate':'Authenticate complete raw body/OID, return without recompression or any size-equality requirement. Its actual stored compressed bytes were already funded in original pool.','original_missing_even_written_in_failedA':'Require full body/OID plus exact originally predicted level6 loose length after partial write; current existence cannot reclassify it as old.','still_missing':'Write exact funded new object and require full body/OID/exact compressed length.','physical_SCOPE_recovery_is_exact620_only_old_original_index_and_HEAD':'Source requires complete already-replaced620 physical bytes and original fixed before-index/HEAD; it performs no second physical scope rewrite.','late_wrapper':'Pins originalA c347/latea769/partial11fec/gateb1a; locally substitutes corrected writer for the authenticated late module without editing either frozen source.','same_index_100644_stage0_S_newpaths_full_readback_exactfuturetree_caps_floors_and_native_pins':True,'external_prelaunch':'Rehash exact V3/originalA/late source and frozen late-M/rows with PYTHONDONTWRITEBYTECODE=1 before invoking. This reviewer never imports those modules.','bounded_late_M_source_fullauth_newpath_and_actual192_128_reserve_checks_remain_required':True,'not_a_general_transaction_or_untrusted_manifest_codec_approval':True}

def check():
    ai,a=pin(B/'publish_exact_compressed_checkpoint_20261011.py','c3479b7fcc3cc57e7485c7fdd6fa6fb4beef3b89c0a0ae046737ff879eeb6a24',13800)
    li,late=pin(B/'preserve_bounded_late_receipts_20261011.py','a769096c38dc32a9567c939cf8f15283629b8b43ca9693e33c6d4b2672fd28a2',5068)
    oldi,v2=pin(B/'recover_exact_compressed_checkpoint_v2_20261011.py','a35b704135dd3546c01505b7854e4fe886ad950bc3aa6ba3ef876c78349fdb31',8877)
    newi,v3=pin(B/'recover_exact_compressed_checkpoint_v3_20261011.py','d7bc29eafca8f53e4231f880c0d13061c79d7d69ba27c1ed1a886697f327ed7e',9171)
    pi,patch=pin(B/'RECOVERY-V3-ORIGINAL-MISSING-ENCODING-PREDICATE-CORRECTION.patch','68b147c94c7a0a46abc0cb4607b0f5c77be24f8825d04736415f5fa41ab0008d',7213)
    di,derivation=jp(B/'RECOVERY-V3-SOURCE-DERIVATION.json','829d7852e36a149be05b1dde0d3203ec88a528ef2adb6243d609bddfdd36d0f1',948)
    rgi,rg=jp(B/'EXACT-COMPRESSED-CHECKPOINT-RECOVERY-V3-GATE.json',RECOVERY_SHA)
    r2i,r2=jp(B/'EXACT-COMPRESSED-CHECKPOINT-RECOVERY-V2-GATE.json','8a625669319d7beed10bd230503bda18ced215d0a421ca27c92c90de07818bd2',3731)
    gi,g=jp(B/'EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json','b1a260456c2c09673e8d811235f5778bdcb57e530948e12b82163cee87c1cce4',30269)
    mi,m=jp(B/'EXACT-COMPRESSED-CHECKPOINT-INPUTS.json','ec7d5566b162558ffaeef895539e4353306638005cdd2c6adb6b58b9a56ec6a4',23933)
    si,state=jp(B/'EXACT-COMPRESSED-CHECKPOINT-PARTIAL-FAILURE-STATE.json','11fec1822e2abdafb3b776547171205b8ffaf179fce7fa1f462576808fa70595',16162)
    ui,up=jp(B/'UPSTREAM-62020166-EXACT-BYTE-PREFLIGHT-V2.json','dc91c9f43ded02823d6254e8405fc42bb77e78849ba6220345c9ce504e832dce',653286)
    qa,oldqa=jp(W/'design-qc/exact-compressed-funding-20261011T0257Z-solver_design_recovery/EXACT-COMPRESSED-PUBLICATION-SOURCE-AND-FUNDING-QC-ATTEMPT2.json','41dca35b576f95bb337d813fcbb8af51ebd47f67998d725ec9a5bff7c9919bae',15644)
    captures=[]
    for n,h,size in [('EXACT-COMPRESSED-CHECKPOINT-APPLY-LAUNCH.json','d0913e83a7450b2d3e457f0bb78a8d3eaee16fdcee0a62b0e67846cef984c061',607),('EXACT-COMPRESSED-CHECKPOINT-APPLY.stdout','e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',0),('EXACT-COMPRESSED-CHECKPOINT-APPLY.stderr','b82f8821ee47fd3474ec16e7cd0c8dfc741e62738a3130bd05696c49b6a03769',881)]:
        info,data=pin(B/n,h,size);captures.append(info)
        if n.endswith('.json'):
            launch=json.loads(data);require(launch['exit_code']==1 and launch['independent_review_sha256']==qa['sha256'],'actualfailedA ownsourcegate bound')
    require(not (B/'EXACT-COMPRESSED-CHECKPOINT-PUBLICATION.json').exists(),'originalapply has no falsePASS result')
    require(g['publisher_sha256']==ai['sha256'] and m['publisher_sha256']==ai['sha256'] and g['input_manifest_sha256']==mi['sha256'],'alloriginalA/M/Gremainexact')
    require(rg['recovery_source_sha256']==newi['sha256'] and rg['original_source_sha256']==ai['sha256'] and rg['funding_gate_sha256']==gi['sha256'] and rg['partial_failure_state_sha256']==si['sha256'] and rg['input_manifest_sha256']==mi['sha256'],'exactnewgateancestry')
    require(derivation['from_sha256']==oldi['sha256'] and derivation['to_sha256']==newi['sha256'] and derivation['preserved_predecessor_gate_sha256']==r2i['sha256'],'whole V2/V3 derivation preserved')
    protocol=source_check(v2,v3,patch)
    idxdata=INDEX.read_bytes();entries,idxmeta=index_entries(idxdata);stage=stage_bytes(entries)
    require(digest(stage)==g['prior_index_sha256']==state['prior_index_entries_sha256']==rg['prior_index_entries_sha256'],'completeoriginalbeforestage bytesunchanged')
    require(idxmeta['sha256']==oldqa['checks']['current_physical_index_snapshot']['sha256'],'completephysicaloriginalindexflags/stats/extensionsbytesunchanged')
    require(current_head()==g['prior_head']=='2347f1c16bfaf649da33ef0a42d693b97f46a161','HEADunchanged')
    future={p:(format(v['mode'],'o'),v['git_blob']) for p,v in entries.items()};current,_=encode_tree(future);require(current==g['current_tree'],'alloldfullcurrenttree unchanged')
    modified=[];incoming=[]
    for row in up['rows']:
        p=row['git_tree_path'];kind,b=obj(row['git_blob']);require(kind=='blob' and len(b)==row['bytes'] and digest(b)==row['sha256'],'all1642 fullfetchedbodiesstillheld')
        if row['status']=='A':require(p not in entries and not os.path.lexists(REPO/p),'upstream1641notyetindexedormaterialized')
        else:
            require(p=='research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md','specificsinglephysicalscope')
            require((REPO/p).read_bytes()==b and entries[p]['git_blob']!=row['git_blob'],'workingtreeexactcomplete620/indexstilloriginalold')
            oldscope=obj(entries[p]['git_blob']);require(oldscope[0]=='blob','fulloriginalscopebodyretainedinoldindexobject');modified.append((p,entries[p]['git_blob'],row['git_blob'],digest(oldscope[1]),row['sha256']))
        future[p]=(row['mode'],row['git_blob']);incoming.append((p,row['git_blob'],row['sha256'],row['bytes']))
    require(len(up['rows'])==1642 and len(modified)==1,'full1641A+1Mactualpartialscope')
    rows=[dict(r) for r in m['files']]+[{'source_path':str(B/'EXACT-COMPRESSED-CHECKPOINT-INPUTS.json'),'git_tree_path':m['prefix']+'/INPUT-MANIFEST.json','bytes':mi['bytes'],'sha256':mi['sha256'],'ordinary_working_file':False}]
    original_missing={r['git_blob'] for r in g['missing_blob_objects']};require(len(original_missing)==36,'originalfrozen36missingOIDclass')
    loose_rows=[];missing_blobs={};new_written=[];old_encoding_differences=[];checked=[]
    for r in rows:
        info,b=pin(r['source_path'],r['sha256'],r['bytes']);full=b'blob '+str(len(b)).encode()+b'\0'+b;oid=hashlib.sha1(full).hexdigest();compressed=len(zlib.compress(full,6));loose=POOLS[0]/oid[:2]/oid[2:]
        present=object_present(oid)
        if present:
            require(obj(oid)==('blob',b),'everyold/newpresentfullbodyandOIDliteral')
            if loose.is_file():
                raw=loose.read_bytes();require(zlib.decompress(raw)==full and hashlib.sha1(full).hexdigest()==oid,'completeheldlooseencodingfullbodyGitOID')
                row={'path':r['git_tree_path'],'oid':oid,'expected_zlib6_bytes':compressed,'actual_loose_bytes':len(raw),'already_present_at_gate':oid not in original_missing};loose_rows.append(row)
                if oid in original_missing:
                    require(len(raw)==compressed,'everyoriginalmissingpartialwrite exactencodinglength');new_written.append((oid,len(raw),digest(raw)))
                elif len(raw)!=compressed:old_encoding_differences.append({**row,'actual_loose_sha256':digest(raw),'complete_body_sha256':r['sha256']})
        else:
            require(oid in original_missing,'nooriginallyheld objectlost');missing_blobs[oid]={**r,'git_blob':oid,'zlib6_content_bytes':compressed}
        if not r.get('ordinary_working_file'):require(r['git_tree_path'] not in entries and not os.path.lexists(REPO/r['git_tree_path']),'allnewmetadata stillnotindexedandnotmaterialized')
        future[r['git_tree_path']]=('100644',oid);checked.append((r['source_path'],r['git_tree_path'],oid,r['sha256'],r['bytes'],compressed))
    require(len(rows)==43 and loose_rows==state['loose_rows'],'all43 fullsources/30 currentloose rows exactpartialstatement')
    require(len(new_written)==25 and len(old_encoding_differences)==5,'25exactnewencodings/only5different preheldlooseencodings')
    written_bytes=sum(r[1] for r in new_written);remaining_blobs=sum(r['zlib6_content_bytes'] for r in missing_blobs.values())
    require(written_bytes==210194 and remaining_blobs==rg['remaining_new_blob_content_bytes']==r2['remaining_new_blob_content_bytes']==30405,'actual25writtenplus11remainingequalsoriginal240599')
    final,ft=encode_tree(future);remaining_trees=[(oid,comp) for oid,body,comp in ft if not object_present(oid)];treebytes=sum(comp for oid,comp in remaining_trees)
    require(final==rg['future_frozen_tree']==g['future_frozen_tree']=='451a3ed51fd20f553a8807e859d5176a6ad6ecfc' and len(remaining_trees)==22 and treebytes==rg['remaining_new_tree_content_bytes']==57765,'samecomplete futuretree/all22remainexact')
    poolbytes=sum(p.stat().st_size for p in POOLS[0].rglob('*') if p.is_file());require(poolbytes==state['current_resource']['pool_bytes']==rg['resource']['pool_bytes']==g['resource']['pool_bytes']+written_bytes==99477624,'actualpool growthonlypredicted25newblobs')
    for n,key in [('late_blob','unchanged_late_blob_reserve_bytes'),('late_tree','unchanged_late_tree_reserve_bytes'),('commit','unchanged_commit_reserve_bytes')]:require(rg[key]==g[n+'_reserve_bytes'],'samelatecapunchanged')
    remainingfunding=remaining_blobs+treebytes+196608+131072+16384
    require(poolbytes+remainingfunding==99909858<100663296,'originalsamefullfunded96MiBboundwithoutoldrecompression')
    ci,cfg=jp('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json','2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c',4477)
    roots=cfg['allocation_roots'];require(len(roots)==len(set(roots))==26 and roots==rg['resource']['ordered26_roots'] and all(Path(p).is_dir() for p in roots),'samefixed26presentrootgraph')
    require((cfg['scratch_abort_bytes'],cfg['scratch_hard_limit_bytes'],cfg['memory_abort_bytes'])==(2013265920,2147483648,16106127360),'globalscratchabort/memoryfixed')
    logical=allocation(roots);followed=allocation(roots,True);mem={k:int(v) for k,v in (line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())};nr=sum(mem[k] for k in ['anon','shmem','kernel']);tmpfree=free_bytes('/tmp');overlay=free_bytes('/workspace')
    require(max(logical['distinct_allocated_bytes'],followed['distinct_allocated_bytes'])+g['new_loose_files_dirs_and_late_alloc_funding_bytes']+MAX_OWN_ALLOC<2013265920,'allpartialwrites/Qdirs+conservativeoriginalallocationfund+64KiBrecoveryQA belowabort')
    require(nr<16106127360 and tmpfree>len(idxdata)+2097152 and overlay>8388608,'freshactualnonreclaim/tmpindexlock/overlayfloors')
    nativeinfo,_=pin('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver','443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00')
    fetchinfo,fetch=jp(B/'FRESH-MAIN-62020166-FETCH-RESULT.json','7b749f5cc6de951a36ace7db07014a22a1cf543dafacd8deaef0a72099dd004d',796)
    admitinfo,admit=jp(B/'FRESH-MAIN-62020166-FETCH-ADMISSION.json','d4b86ee68df49e232dcae09dc39b1c8c4bdce87c83633df6c6bbd838fbd16df1',2084)
    packs=[]
    for rel,r in list(admit['before_pack_inventory'].items())+list(fetch['new_pack_files'].items()):
        info,_=pin(POOLS[0]/rel,r['sha256'],r['bytes']);packs.append(info)
    require(INDEX.read_bytes()==idxdata and current_head()==g['prior_head'],'currentoriginalphysicalindexandHEADfixedthroughentireQC')
    for info in [ai,li,oldi,newi,pi,di,rgi,r2i,gi,mi,si,qa]:pin(info['path'],info['sha256'],info['bytes'])
    return {'original_frozenA':ai,'original_late_source':li,'preservedV2source':oldi,'preservedV2readonly_gate':r2i,'frozenV3source':newi,'V3_exactdiff':pi,'V3_source_derivation':di,'V3_readonly_recovery_gate':rgi,'original_funding_gate':gi,'original_manifest':mi,'original_full_independent_QA_retained':qa,'actual_failedA_full_launch_stdout_stderr':captures,'failedA_is_compressed_existing_size_check_not_source_math_failure':True,'partial_failure_state':si,'full_current_original_physical_index_byteidentity':idxmeta,'all_originalmode_blob_stage_skipflags_stats_extensions_retained':True,'HEAD':current_head(),'physical_scope_new620_complete_and_index_old_original':modified,'originalscopefulloldGitblobretained':True,'all43_originalsource_bodies_andOIDclasses_authenticated':True,'canonical43_body_origin_target_oid_hash_size_zlib_tuples_sha256':canonical_hash(checked),'all1642_fetchblobs_remainfull_literal':True,'actual25_new_loose_encodings_original_missing_OIDs':new_written,'original_missing_written_bytes':written_bytes,'11_still_missing_blobs_bytes':remaining_blobs,'only5_preheld_different_encodings_fullauthenticated':old_encoding_differences,'no_oldencoding_recompression_permitted':True,'all9_full_oldnew_pack_files_retained':packs,'unchanged_future_frozen_tree':final,'22_stillmissing_tree_bytes':treebytes,'current_pool_bytes':poolbytes,'remaining_content_funding_with_late_commit_reserves_bytes':remainingfunding,'same_funded_pool_bound_bytes':99909858,'same96MiB_pool_bound_remaining_bytes':753438,'fresh_resources':{'config':ci,'lstat_file_and_directory_allocation':logical,'followed_file_target_and_directory_allocation':followed,'original_conservative_loosefile_fanout_late_allocation_reserve':g['new_loose_files_dirs_and_late_alloc_funding_bytes'],'bounded_own_QA64KiB_allocation_reserve':MAX_OWN_ALLOC,'nonreclaimable_bytes':nr,'memory_abort_bytes':16106127360,'scratch_abort_bytes':2013265920,'scratch_hard_bytes':2147483648,'tmp_free_bytes':tmpfree,'index_plus2MiB_bytes':len(idxdata)+2097152,'overlay_free_bytes':overlay,'overlay_floor_bytes':8388608,'instantaneous_measurement_only':True},'public_native443_complete_sha':nativeinfo,'source_and_late_protocol':protocol,'own_prior_source_review_limitation_candidly_recorded':'The initial source review approved an equality predicate for already-held compressed stream length. Actual firstA proved it invalid for five old encodings. Preserve that dated review and failedA; this new gate separates literal raw object identity from old encoded length while retaining all exact originally-missing predicates.','only_this_frozen_partial_state_recovery_and_bounded_frozen_late_M_allowed':True,'no_furtherfetch_capsraise_deletion_hiding_sourcecontextcompiler_native_reference_refinement_or_scientificpromotion':True,'no_Git_commands_mutations_targethelper_imports_or_producer_invocations_by_this_independent_reader':True,'remote_publication_commit_push_verification_pending':True}

report={'schema':'EXACT_PUBLICATION_PARTIAL_STATE_V3_RECOVERY_SOURCE_INDEPENDENT_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes()),'recovery_gate_sha256':RECOVERY_SHA,'funding_gate_sha256':'b1a260456c2c09673e8d811235f5778bdcb57e530948e12b82163cee87c1cce4'}
try:report['checks']=check();report['status']='PASS_FIXED_PARTIAL_BYTES_V3_RECOVERY_ORIGINAL_MISSING_ENCODINGS_STRICT'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
data=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
require(Q.stat().st_blocks*512+sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file())+((len(data)+4095)//4096)*4096<=MAX_OWN_ALLOC,'entirenewrecoveryQCsource+savedreceiptincludingdirectory<=64KiB')
out=Q/'EXACT-PUBLICATION-V3-PARTIAL-RECOVERY-INDEPENDENT-QC-ATTEMPT1.json';require(not out.exists(),'immutableindependentreceipt');out.write_bytes(data)
print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(data),'bytes':len(data),'reviewer_sha256':report['reviewer_sha256'],'recovery_gate_sha256':RECOVERY_SHA,'error':report.get('error'),'directory_full_allocated_bytes':Q.stat().st_blocks*512+sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file()),'fresh_resources':report.get('checks',{}).get('fresh_resources')}))
