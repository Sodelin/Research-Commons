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

import ast
import stat
Q=W/'design-qc/exact-compressed-funding-20261011T0257Z-solver_design_recovery'
MAX_QA_ALLOC=98304

def stage_bytes(entries):
    return b''.join((format(v['mode'],'06o')+' '+v['git_blob']+' '+str(v['stage'])+'\t'+p+'\0').encode('utf8','surrogateescape') for p,v in sorted(entries.items(),key=lambda x:x[0].encode('utf8','surrogateescape')))

def current_head():
    head=(REPO/'.git/HEAD').read_text().strip()
    if not head.startswith('ref: '):return head
    path=REPO/'.git'/head[5:]
    if path.is_file():return path.read_text().strip()
    rows=(REPO/'.git/packed-refs').read_text().splitlines()
    return next(line.split()[0] for line in rows if not line.startswith(('#','^')) and line.split()[1]==head[5:])

def json_pin(path,h,size=None):
    info,data=pin(path,h,size);return info,json.loads(data)

def source_protocol(source,late):
    tree_ast=ast.parse(source);late_ast=ast.parse(late)
    functions={n.name:n for n in tree_ast.body if isinstance(n,ast.FunctionDef)}
    required={'metrics','inputs','upstream','prepare','write_blob','apply','trees','allocated','blob_info'}
    require(required<=set(functions),'frozen protocol expected byte-only methods')
    calls={}
    for fn in ['prepare','apply','git']:
        calls[fn]=[n.args[0].value for n in ast.walk(functions[fn]) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='git' and n.args and isinstance(n.args[0],ast.Constant)]
    require(set(calls['prepare'])=={'rev-parse','cat-file'} and set(calls['apply'])=={'rev-parse','cat-file','update-index','ls-files','show','write-tree'},'fixed prepare/apply direct Git operations')
    constants={n.targets[0].id:n.value.value for n in tree_ast.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and isinstance(n.value,ast.Constant)}
    require(constants['CONFIG_SHA']=='2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c' and constants['NATIVE_SHA']=='443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00','fixed config and native pins')
    text=source.decode();ltext=late.decode()
    require("'core.looseCompression=6'" in text and "'gc.auto=0'" in text,'exact writer compression and no automatic GC')
    require("review['funding_gate_sha256']==sha(gatebytes)" in text and "g['publisher_sha256']==sha(pathlib.Path(__file__).read_bytes())" in text and "sha(before)==g['prior_index_sha256']" in text,'full funding/source/stage prelaunch gate binding')
    require("os.fsync(f.fileno())" in text and "os.replace(temporary,dest)" in text and "oldscope==git('cat-file','blob',oldentries" in text,'specific oldscope authenticated then fsynced atomic replacement')
    require("assert predicted==g['future_frozen_tree']" in text and "assert tree==predicted" in text and "if p not in changed" in text,'exact alluntouched index mode/blob and predicted actual tree')
    require("assert blobs+32*1024<=g['late_blob_reserve_bytes']" in ltext and "assert trees+32*1024<=g['late_tree_reserve_bytes']" in ltext and "assert receipt['zlib6_content_bytes']<32768" in ltext and "assert ft<32768" in ltext,'late192/128 reserves each retain32KiB final full receipt/tree')
    require("A.git('show',':'+receipt['git_tree_path'])==OUT.read_bytes()" in ltext and "A.git('write-tree').decode().strip()==final;A.metrics()" in ltext,'late complete actual result readback and finaltree/fullfloors')
    return {'fixed_source_method_line_spans':{n:[functions[n].lineno,functions[n].end_lineno] for n in sorted(required)},'prepare_does_not_write_Git_index_or_objects':True,'apply_scope_is_frozen_authenticated_regular_fulltext_plus_exact_upstream1642':True,'specific_CURRENT_SCOPE_replace_is_atomic_not_a_whole_multifile_transaction':True,'old_scope_remains_recoverable_as_authenticated_existing_index_commit_blob':True,'untouched_prior_index_mode_blob_and_stage_preserved_in_source':True,'new_sparse_flags_only_named_new_paths':True,'exact_zlib6_no_gc_pool_and_global_pre_post_guards':True,'native_source_no_compiler_reference_runtime_or_cache_mutation':True,'bounded_late_source_uses_authenticated_fixed_A_methods':True,'late_A_module_is_imported_by_publisher_not_by_this_reviewer':True,'late_external_gate_required':'Before invoking late helper, root must pin exact A c3479b7f and late a769096c bytes, freeze/authenticate all late-M rows and absence, and recompute actual missing blob/tree sizes inside192/128KiB reserves; this is not arbitrary-manifest acceptance.','late_actual_receipt_and_finaltree_each_has_separate32KiB_allowance':True,'Git_commit_and_remote_publication_not_executed_by_either_review_or_current_apply':True}

def check():
    si,source=pin(B/'publish_exact_compressed_checkpoint_20261011.py','c3479b7fcc3cc57e7485c7fdd6fa6fb4beef3b89c0a0ae046737ff879eeb6a24',13800)
    li,late=pin(B/'preserve_bounded_late_receipts_20261011.py','a769096c38dc32a9567c939cf8f15283629b8b43ca9693e33c6d4b2672fd28a2',5068)
    gi,gate=json_pin(B/'EXACT-COMPRESSED-CHECKPOINT-FUNDING-GATE.json','b1a260456c2c09673e8d811235f5778bdcb57e530948e12b82163cee87c1cce4',30269)
    mi,manifest=json_pin(B/'EXACT-COMPRESSED-CHECKPOINT-INPUTS.json','ec7d5566b162558ffaeef895539e4353306638005cdd2c6adb6b58b9a56ec6a4',23933)
    ui,up=json_pin(B/'UPSTREAM-62020166-EXACT-BYTE-PREFLIGHT-V2.json','dc91c9f43ded02823d6254e8405fc42bb77e78849ba6220345c9ce504e832dce',653286)
    priorinfo,prior=json_pin(W/'design-qc/fetch620-resource-hold-20261011T0244Z-solver_design_recovery/FETCH620-RESOURCE-HOLD-AND-CONDITIONAL-RECOVERY-QC-ATTEMPT1.json','13c26f4fbac5a786b7a388ac67a88fd35bd9bd08899b0e5d378ca72ab3fffe6e',13541)
    require(gate['publisher_sha256']==manifest['publisher_sha256']==si['sha256'] and gate['input_manifest_sha256']==mi['sha256'],'exact fixed source/input/funding binding')
    require(current_head()==gate['prior_head']=='2347f1c16bfaf649da33ef0a42d693b97f46a161','current prior HEAD remains fixed')
    require(gate['upstream_preflight_sha256']==ui['sha256'] and gate['upstream_cutoff']==up['to']=='62020166e3e7ef690838f50b13caa149ede419ec','exact upstream byte inventory bound')
    idxdata=INDEX.read_bytes();entries,idxmeta=index_entries(idxdata);rawstage=stage_bytes(entries)
    require(digest(rawstage)==gate['prior_index_sha256']=='80c65363ca74fc2de27f30db00699dcae8c357ac8bac95d7b2a93fef30363b9c','independent complete priorstage byte snapshot')
    future={p:(format(r['mode'],'o'),r['git_blob']) for p,r in entries.items()}
    current,current_trees=encode_tree(future);require(current==gate['current_tree']=='cb1a2771a31637f8a411f7584848d237fd3f601c','complete current index puretree')
    require(len(up['rows'])==1642,'all1642 immutable upstream rows')
    incoming=[];modified=[]
    for row in up['rows']:
        p=row['git_tree_path'];kind,body=obj(row['git_blob']);require(kind=='blob' and len(body)==row['bytes'] and digest(body)==row['sha256'] and row['mode']=='100644','all1642 current complete fetched blobs exact')
        if row['status']=='A':require(p not in entries and not os.path.lexists(REPO/p),'all1641 upstream additions genuinely new')
        else:
            require(row['status']=='M' and p=='research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md','only specific original scope mutation')
            require((REPO/p).read_bytes()==obj(entries[p]['git_blob'])[1],'oldphysicalscope equalsoldindexblob')
            modified.append(row)
        future[p]=(row['mode'],row['git_blob']);incoming.append((p,row['mode'],row['git_blob'],row['sha256'],row['bytes']))
    require(len(modified)==1,'one exact CURRENT-SCOPE update')
    upstream_tree,_=encode_tree(future);require(upstream_tree==gate['upstream_only_tree']=='5481499b6738ad04919b661ee6792910605bbcfb','fixed upstream only tree alreadyindependentlychecked')
    require(len(manifest['files'])==42 and sum(x['bytes'] for x in manifest['files'])==1095564,'fixed42 fulltext bytes')
    rawrows=[dict(x) for x in manifest['files']]
    rawrows.append({'source_path':str(B/'EXACT-COMPRESSED-CHECKPOINT-INPUTS.json'),'git_tree_path':manifest['prefix']+'/INPUT-MANIFEST.json','bytes':mi['bytes'],'sha256':mi['sha256'],'ordinary_working_file':False})
    require(len(rawrows)==gate['files_count_including_manifest']==43 and len({r['git_tree_path'] for r in rawrows})==43,'exact43 unique full frozen sources incl manifest')
    require(gate['prefix']==manifest['prefix'] and all(r['git_tree_path'] not in {x['git_tree_path'] for x in up['rows']} for r in rawrows),'frozenmetadata disjoint frompeer mutation')
    checked=[];ordinary=[];missing_blobs={};allnewpaths=[]
    for row in rawrows:
        p=Path(row['source_path']);target=row['git_tree_path'];require(p.is_file() and not p.is_symlink(),'full original regular text file')
        info,body=pin(p,row['sha256'],row['bytes']);body.decode('utf8');require(not body.startswith(b'\x7fELF'),'UTF8 nonELF scientific metadata only')
        require(target==str(Path(target)) and not target.startswith('/') and '..' not in Path(target).parts,'all fixed tree paths normalized relative')
        full=b'blob '+str(len(body)).encode()+b'\0'+body;oid=hashlib.sha1(full).hexdigest();compressed=len(zlib.compress(full,6));actual={**row,'git_blob':oid,'zlib6_content_bytes':compressed}
        if row.get('ordinary_working_file'):
            require(p==REPO/target and target.startswith('research/2026-10-10-codex-lean-rust-parity/'),'exact currentpacket working-sourcepath only indexed')
            ordinary.append((target,oid,row['sha256'],target in entries))
        else:
            require(target.startswith(manifest['prefix']+'/') and target not in future and not os.path.lexists(REPO/target),'explicit new bounded prefix metadata only sparse')
            allnewpaths.append(target)
        if object_present(oid):require(obj(oid)==('blob',body),'already-present full blob body exact')
        else:missing_blobs[oid]=actual
        future[target]=('100644',oid);checked.append((str(p),target,oid,len(body),row['sha256'],compressed))
    require(list(missing_blobs.values())==gate['missing_blob_objects'],'all exactmissing43input body objects identities andlevel6 sizes')
    final,ft=encode_tree(future);missing_trees=sorted([{'git_object':oid,'zlib6_content_bytes':comp} for oid,body,comp in ft if not object_present(oid)],key=lambda r:r['git_object'])
    require(final==gate['future_frozen_tree']=='451a3ed51fd20f553a8807e859d5176a6ad6ecfc' and missing_trees==gate['missing_tree_objects'],'full final predicted tree andexactmissing22 subtreeobjects')
    blobbytes=sum(r['zlib6_content_bytes'] for r in missing_blobs.values());treebytes=sum(r['zlib6_content_bytes'] for r in missing_trees)
    require(blobbytes==gate['exact_missing_blob_content_bytes']==240599 and treebytes==gate['exact_missing_tree_content_bytes']==57765,'completeexact current object content funding')
    require((gate['late_blob_reserve_bytes'],gate['late_tree_reserve_bytes'],gate['commit_reserve_bytes'])==(196608,131072,16384),'unchanged separate192KiB/128KiB/16KiB lateblob/tree/commitreserves')
    funding=blobbytes+treebytes+196608+131072+16384
    require(funding==gate['complete_object_content_funding_bytes']==642428,'completeexactknown+separateboundedlatereserve')
    fileallocation=sum(((r['zlib6_content_bytes']+4095)//4096)*4096 for r in list(missing_blobs.values())+missing_trees)
    objectallocation=fileallocation+4096*(len(missing_blobs)+len(missing_trees))+2097152
    require(objectallocation==gate['new_loose_files_dirs_and_late_alloc_funding_bytes']==2797568,'exact block-rounded new loosefile + perobjectfanout +2MiBlate allocation')
    cfginfo,cfg=json_pin('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json','2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c',4477)
    roots=cfg['allocation_roots'];require(len(roots)==len(set(roots))==26 and roots==gate['resource']['ordered26_roots'] and all(Path(r).is_dir() for r in roots),'all fixed ordered26 present current roots')
    require((cfg['scratch_abort_bytes'],cfg['scratch_hard_limit_bytes'],cfg['memory_abort_bytes'])==(2013265920,2147483648,16106127360),'global2GiB/1.875GiB/15GiB unchanged')
    require(POOLS[0].resolve()==W/'metadata/git-object-pool-preserved-20261011','entirepool countedinsideWF')
    poolbytes=sum(p.stat().st_size for p in POOLS[0].rglob('*') if p.is_file());require(poolbytes==gate['resource']['pool_bytes']==99267430,'all preserved pack+objectpool current exact')
    logical=allocation(roots);followed=allocation(roots,True)
    mem={k:int(v) for k,v in (line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())};nonreclaim=sum(mem[k] for k in ('anon','shmem','kernel'))
    tmpfree=free_bytes('/tmp');overlayfree=free_bytes('/workspace');scope_alloc=((modified[0]['bytes']+4095)//4096)*4096
    ni,_=pin('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver','443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00')
    require(poolbytes+funding==99909858<100663296,'funded future pool exact belowfixed96MiB')
    require(max(logical['distinct_allocated_bytes'],followed['distinct_allocated_bytes'])+objectallocation+MAX_QA_ALLOC<2013265920,'freshwhole-root allocations plusknownobjectfunding+boundedreview belowabort')
    require(nonreclaim<16106127360 and tmpfree>len(idxdata)+2097152,'freshnonreclaim15GiB/tmpfullindexlock+2MiBfloor')
    require(overlayfree>scope_alloc+8388608,'freshphysicalatomicnewscope temporaryfits8MiBfloor')
    thinQ=W/'design-qc/thin1575-static-saved-20261011T0250Z-solver_design_recovery';thinfiles=sum(p.stat().st_blocks*512 for p in thinQ.iterdir() if p.is_file());thindir=thinQ.stat().st_blocks*512
    require(thinfiles==65536 and thindir==0,'actual thinQA file64KiB +directory0B on currenttmpfs')
    touched={x['git_tree_path'] for x in up['rows']}|{x['git_tree_path'] for x in rawrows}
    untouched=[(p,v['mode'],v['git_blob'],v['stage'],v['skip_worktree']) for p,v in entries.items() if p not in touched]
    require(INDEX.read_bytes()==idxdata and current_head()==gate['prior_head'],'HEAD andcurrentfullindex remainedunchangedthroughreadback')
    for info in [si,li,gi,mi,ui,cfginfo]:pin(info['path'],info['sha256'],info['bytes'])
    protocol=source_protocol(source,late)
    return {'source':si,'bounded_late_source':li,'input_manifest':mi,'funding_gate':gi,'fixed_upstream_preflight':ui,'prior_resource_hold_QC':priorinfo,'all43_current_original_fulltext_rows_authenticated':True,'input_payload_bytes':sum(r['bytes'] for r in rawrows),'all43_canonical_body_target_sha1_sha256_zlib6_bindings_sha256':canonical_hash(checked),'ordinary15_named_packet_rows_only_Git_indexed_existing_working_bytes_not_rewritten':ordinary,'metadata_only_new_prefix_paths':len(allnewpaths),'all1642_currentcompletefetchedblobs_mode_length_SHA_checked':True,'upstream1642_canonical_bindings_sha256':canonical_hash(incoming),'one_atomic_CURRENT_SCOPE_expected_new_bytes':modified[0]['bytes'],'allprior_untouched_index_mode_blob_stage_sparseflag_snapshot_sha256':canonical_hash(untouched),'untouched_prior_entry_count':len(untouched),'current_physical_index_snapshot':idxmeta,'prior_full_stage_bytes_sha256':digest(rawstage),'current_tree':current,'upstream_only_tree':upstream_tree,'funded_frozen_tree':final,'future_entry_count':len(future),'missing_blob_objects_count':len(missing_blobs),'exact_missing_blob_content_bytes':blobbytes,'missing_tree_objects_count':len(missing_trees),'exact_missing_tree_content_bytes':treebytes,'known_missing_tree_objects':missing_trees,'late_blob_reserve_bytes':196608,'late_tree_reserve_bytes':131072,'commit_reserve_bytes':16384,'complete_object_content_funding_bytes':funding,'new_loose_files_dirs_and_late_alloc_funding_bytes':objectallocation,'current_pool_bytes':poolbytes,'funded_pool_bound_bytes':poolbytes+funding,'funded_pool_remaining_below96MiB_bytes':100663296-poolbytes-funding,'fresh_resource_checks':{'config':cfginfo,'guard_lstat_includes_file_and_directory_blocks':logical,'conservative_followed_file_targets_includes_directory_blocks':followed,'remaining_review_allocation_reserved_bytes':MAX_QA_ALLOC,'funded_scratch_bound_including_review_bytes':max(logical['distinct_allocated_bytes'],followed['distinct_allocated_bytes'])+objectallocation+MAX_QA_ALLOC,'scratch_abort_bytes':2013265920,'scratch_hard_limit_bytes':2147483648,'memory_nonreclaimable_bytes':nonreclaim,'memory_abort_bytes':16106127360,'tmp_free_bytes':tmpfree,'current_index_plus2MiB_requirement_bytes':len(idxdata)+2097152,'overlay_free_bytes':overlayfree,'atomic_scope_temporary_allocated_bytes':scope_alloc,'required_overlay_plus_temporary_floor_bytes':8388608+scope_alloc,'instantaneous_measurements_only':True},'public_native_443_complete_rehash':ni,'thin_Q_actual_file_allocation65536_directory_allocation0_bytes':True,'source_protocol':protocol,'late_full_QA_and_gate_and_actualreceipt_publication_is_funded_but_still_requires_frozen_actual_rows_reserve_checks':'Known43 plus bounded late files only. Require actualmissing lateblob/tree costs <=192/128KiB; latewriter preserves32KiB each for its full actual receipt/finaltree, and16KiB commit reserve remains separate. No furtherfetch, capincrease, deletion, hiding, oldbyte loss, new compiler/context/native/refinement or master admission.','no_Git_commands_index_objects_refs_mutations_target_imports_or_producers_by_independent_reader':True,'remote_commit_push_or_scientific_acceptance_changed':False}

report={'schema':'EXACT_COMPRESSED_CHECKPOINT_SOURCE_AND_FUNDING_INDEPENDENT_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes()),'funding_gate_sha256':'b1a260456c2c09673e8d811235f5778bdcb57e530948e12b82163cee87c1cce4','parent_Git_reader_sha256':'d38a29eb2c2546eccd30ff45321f2805eadab2b9061d1984f343cf51f6897a0d','parent_pure_tree_allocation_reader_sha256':'f5a3c12e2c2902b359f1e7426f8253272455d37c7233359766e6155a29263f28'}
try:report['checks']=check();report['status']='PASS_FIXED_EXACT_COMPRESSED_PUBLICATION_SOURCE_FUNDING_WITH_BOUNDED_LATE_GATE'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
data=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
require(sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file())+Q.stat().st_blocks*512+((len(data)+4095)//4096)*4096<=MAX_QA_ALLOC,'combinednewsource_QAactualallocationincludingdirectory<=96KiB')
out=Q/'EXACT-COMPRESSED-PUBLICATION-SOURCE-AND-FUNDING-QC-ATTEMPT2.json';require(not out.exists(),'immutableownreceipt');out.write_bytes(data)
print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(data),'bytes':len(data),'reviewer_sha256':report['reviewer_sha256'],'funding_gate_sha256':report['funding_gate_sha256'],'error':report.get('error'),'directory_content_bytes':sum(p.stat().st_size for p in Q.iterdir() if p.is_file()),'directory_full_allocated_bytes':sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file())+Q.stat().st_blocks*512,'fresh_resources':report.get('checks',{}).get('fresh_resource_checks')}))
