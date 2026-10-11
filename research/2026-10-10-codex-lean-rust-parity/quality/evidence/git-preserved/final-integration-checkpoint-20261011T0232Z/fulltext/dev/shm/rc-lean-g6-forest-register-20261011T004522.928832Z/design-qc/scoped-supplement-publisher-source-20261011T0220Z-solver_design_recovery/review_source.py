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

import ast
import os
import stat
import traceback

Q=W/'design-qc/scoped-supplement-publisher-source-20261011T0220Z-solver_design_recovery'
SOURCE=B/'publish_full_scoped_supplement_20261011.py'
PARENT=B/'publish_natural141_pass_fixed_shmem_to_git_20261011_v2_96mib.py'
MANIFEST=B/'SUPPLEMENTAL-PUBLICATION-INPUTS-V2.json'
PARENT_MANIFEST=W/'metadata/publication-completeness-20261011T020723.373648Z-lean-reuse-successor/SUPPLEMENTAL-FULLTEXT-MANIFEST.json'
PLAN=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json')

def ast_form(node): return ast.dump(node,include_attributes=False)
def main_node(data):return next(n for n in ast.parse(data).body if isinstance(n,ast.FunctionDef) and n.name=='main')
def free_bytes(path):
    s=os.statvfs(path);return s.f_bavail*s.f_frsize

def check():
    sp,sd=pin(SOURCE,'58ac463496e55fc8ae9d67ac5bb4731d1275e5c92b0de759d83c8925aaa20e8e')
    pp,pd=pin(PARENT,'7b464ff41bd45bca4a9356ebbb00c0193f8e8af3d34da9fc5ef023a07eac2218')
    mt=ast.parse(sd);pt=ast.parse(pd)
    pure={}
    for name in ['git','digest','size','free']:
        a=next(n for n in mt.body if isinstance(n,ast.FunctionDef) and n.name==name)
        b=next(n for n in pt.body if isinstance(n,ast.FunctionDef) and n.name==name)
        require(ast_form(a)==ast_form(b),'literal pure helper '+name);pure[name]=digest(ast_form(a).encode())
    for name in ['REPO','OBJECTS','INDEX','ENV']:
        def assignment(t):return next(n for n in t.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id==name for x in n.targets))
        require(ast_form(assignment(mt))==ast_form(assignment(pt)),'fixed Git binding '+name)
    a=main_node(sd);b=main_node(pd)
    def loop(node,needle):
        return next(n for n in node.body if isinstance(n,ast.For) and needle in ast.unparse(n))
    oldwrite=loop(b,"hash-object");newwrite=loop(a,"hash-object")
    class RenameSource(ast.NodeTransformer):
        def visit_Constant(self,node):
            if node.value=='original_path':return ast.copy_location(ast.Constant('source_path'),node)
            return node
    oldwrite=RenameSource().visit(oldwrite)
    require(ast_form(oldwrite)==ast_form(newwrite),'exact full blob/hash/write/readback loop except source field name')
    def segment(node):
        start=next(i for i,n in enumerate(node.body) if isinstance(n,ast.Assign) and ast.unparse(n).startswith('preexisting ='))
        end=next(i for i,n in enumerate(node.body[start:],start) if isinstance(n,ast.For) and "ls-files', '-v'" in ast.unparse(n))
        return node.body[start+2:end]
    require([ast_form(n) for n in segment(a)]==[ast_form(n) for n in segment(b)],'exact index addition and all preexisting-stage filtering protocol')
    oldread=loop(b,"startswith('S ')");newread=loop(a,"startswith('S ')")
    assignment=oldread.body[0];oldread.body[1].test.func.value=assignment.value
    oldread.body=oldread.body[1:]
    oldread=RenameSource().visit(oldread)
    require(ast_form(oldread)==ast_form(newread),'same S/readback with inline status expression')
    for expr in ["before['object_pool_bytes'] + payload + len(rows) * 4096 < 96 * 1024 * 1024", "before['tmp_free_bytes'] > payload + len(rows) * 4096 + before['index_bytes'] + 2 * 1024 * 1024", "before['overlay_free_bytes'] > 8 * 1024 * 1024", "after['object_pool_bytes'] < 96 * 1024 * 1024", "after['overlay_free_bytes'] > 8 * 1024 * 1024"]:
        goal=ast_form(ast.parse(expr,mode='eval').body)
        require(any(isinstance(n,ast.Assert) and ast_form(n.test)==goal for n in a.body),'retained fixed storage pre/post condition '+expr)
    mp,md=pin(MANIFEST,'bbb443e9fbfb61a157b6dc24d5d0995791fb562b9381a41e7bb886ce72cab26c');m=json.loads(md)
    pmp,pmd=pin(PARENT_MANIFEST,'4e25b6e1c0cfac56ed8e13e8c0ae5eef77038d9e79668cea5f582e01fb112c1a');pm=json.loads(pmd)
    require(len(m['files'])==m['files_count']==118 and sum(x['bytes'] for x in m['files'])==m['payload_bytes']==6771092,'exact manifest count/bytes')
    require(m['parent_manifest_sha256']==pmp['sha256'],'exact parent manifest reference')
    prefix='research/2026-10-10-codex-lean-rust-parity/quality/evidence/git-preserved/scoped-integration-supplement-20261011T0212Z'
    require(m['prefix']==prefix,'fixed new evidence prefix')
    rows=[dict(x) for x in m['files']]
    source_rows={x['source_path']:x for x in rows}
    require(len(source_rows)==118,'unique source locators')
    inherited=pm['additional_fulltext_payload'];require(len(inherited)==100,'parent has exactly 100 full-text rows')
    for row in inherited:
        require(row['source_path'] in source_rows,'parent full text retained '+row['source_path'])
        current=source_rows[row['source_path']]
        require(current['bytes']==row['bytes'] and current['sha256']==row['sha256'],'parent bytes/hash unchanged')
    for name,path in [('INPUT-MANIFEST.json',MANIFEST),('PUBLISHER.py',SOURCE)]:
        info,data=pin(path);rows.append({'source_path':str(path),'git_tree_path':prefix+'/'+name,'bytes':len(data),'sha256':info['sha256']})
    idxdata=INDEX.read_bytes();entries,idxmeta=index_entries(idxdata)
    require(idxmeta['entry_count']==102972,'current post-f812 entry count 102972')
    require(len({x['git_tree_path'] for x in rows})==120,'120 unique tree paths')
    for row in rows:
        source=Path(row['source_path']);require(source.is_file() and not source.is_symlink(),'regular frozen full text '+str(source))
        info,data=pin(source,row['sha256'],row['bytes']);data.decode('utf8');require(not data.startswith(b'\x7fELF'),'no ELF')
        target=row['git_tree_path'];require(target.startswith(prefix+'/') and '..' not in Path(target).parts and not Path(target).is_absolute(),'fixed bounded tree path')
        require(not os.path.lexists(REPO/target) and target not in entries,'genuinely absent physical/index new path '+target)
        row['git_blob']=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    payload=sum(x['bytes'] for x in rows);require(payload<8*1024*1024,'120 files fit 8MiB payload reserve')
    planinfo,pldata=pin(PLAN,'2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c');plan=json.loads(pldata)
    roots=plan['allocation_roots'];require(len(roots)==len(set(roots))==26,'26 unchanged roots')
    require(plan['scratch_abort_bytes']==2013265920 and plan['scratch_hard_limit_bytes']==2147483648 and plan['memory_abort_bytes']==16106127360,'scientific caps unchanged')
    inodes=set();allocated=0;regular=0
    for root in roots:
        require(Path(root).is_dir(),'counted root exists')
        for current,dirs,files in os.walk(root,followlinks=False):
            for path in [Path(current)]+[Path(current)/x for x in dirs+files]:
                s=path.lstat();identity=(s.st_dev,s.st_ino)
                if identity in inodes:continue
                inodes.add(identity);allocated+=s.st_blocks*512
                regular+=int(stat.S_ISREG(s.st_mode))
    pool_files=[p for p in POOLS[0].rglob('*') if p.is_file()]
    poolbytes=sum(p.stat().st_size for p in pool_files)
    allowance=len(rows)*4096;growth=payload+allowance
    mem={x.split()[0]:int(x.split()[1]) for x in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines()}
    nonreclaim=sum(mem[x] for x in ['anon','shmem','kernel'])
    before={'object_pool_bytes':poolbytes,'object_files':len(pool_files),'tmp_free_bytes':free_bytes('/tmp'),'overlay_free_bytes':free_bytes('/workspace'),'index_bytes':len(idxdata),'global_allocated_distinct_inode_bytes':allocated,'global_regular_files':regular,'nonreclaim_anon_shmem_kernel_bytes':nonreclaim}
    require(poolbytes+growth<96*1024*1024,'96MiB publisher allowance funded')
    require(before['tmp_free_bytes']>growth+len(idxdata)+2*1024*1024,'tmp index/write reserve funded')
    require(before['overlay_free_bytes']>8*1024*1024,'8MiB overlay floor')
    require(allocated+growth+1024*1024<2013265920,'global abort with 1MiB extra own QA/receipt reserve')
    require(nonreclaim<16106127360,'15GiB nonreclaim')
    require(not (B/'FULL-SCOPED-SUPPLEMENT-PUBLICATION.json').exists(),'publisher remains uninvoked')
    return {'source':sp,'accepted_parent':pp,'four_literal_pure_helper_ast_sha256':pure,'exact_git_bindings_and_blob_index_full_readback_protocol':True,'whole_main_identity_claimed':False,'explicit_tail_difference':'The parent has a third overlay-floor assertion after its shmem receipt write. This source keeps the pre-Git and post-Git floors and writes OUT in counted shmem; no overlay mutation occurs between retained post-Git assertion and receipt. Root explicitly approved the omission.','fixed_authenticated_manifest':mp,'parent_fulltext_manifest':pmp,'all_100_parent_fulltexts_retained':True,'additional_regular_fulltexts':18,'all_120_files':rows,'payload_bytes':payload,'planned_per_file_growth_allowance':allowance,'bounded_fixed_manifest_only_not_general_untrusted_publisher_acceptance':True,'before':before,'funded_pool_bytes':poolbytes+growth,'funded_global_allocated_with_1MiB_QA_reserve':allocated+growth+1024*1024,'pool_limit_bytes':96*1024*1024,'scientific_caps_unchanged':True,'capacity_plan':planinfo,'current_index':idxmeta,'out_in_existing_counted_context':True,'no_Git_commands_or_mutations':True,'no_target_module_import_or_invocation':True,'no_compiler_or_mathematical_producer':True,'scientific_acceptance_changed':False,'execution_and_commit_push_are_root_owned_separate_steps':True,'own_exploratory_schema_correction':'Prior inline metadata display expected parent files; actual immutable parent schema is additional_fulltext_payload. That read stopped with KeyError before target import, invocation, or mutation. This reader uses and checks the exact 100-row field.'}

report={'schema':'INDEPENDENT_SCOPED_SUPPLEMENT_FIXED_SOURCE_AND_CAPACITY_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes())}
try:
    report['checks']=check();report['status']='PASS_SOURCE_ONLY_FIXED120_FULL_TEXT_AND_CURRENT_CAPACITY'
except Exception as e:
    report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
output=Q/'SCOPED-SUPPLEMENT-PUBLISHER-SOURCE-CAPACITY-QC-ATTEMPT1.json'
require(not output.exists(),'immutable own output');output.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
print(json.dumps({'status':report['status'],'path':str(output),'sha256':digest(output.read_bytes()),'bytes':output.stat().st_size,'error':report.get('error'),'capacity':report.get('checks',{}).get('before'),'payload':report.get('checks',{}).get('payload_bytes')}))
