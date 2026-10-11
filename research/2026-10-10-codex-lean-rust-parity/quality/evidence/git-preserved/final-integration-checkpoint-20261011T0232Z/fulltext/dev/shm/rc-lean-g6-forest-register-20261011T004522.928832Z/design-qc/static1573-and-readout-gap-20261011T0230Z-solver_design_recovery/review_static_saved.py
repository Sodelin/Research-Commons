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

import ast
import re
from fractions import Fraction
Q=W/'design-qc/static1573-and-readout-gap-20261011T0230Z-solver_design_recovery'
D=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/metadata/static-union1573-source-plan-20261011T022330.460416Z')
META_COMMIT='f8120b1e413b64303891f7f2f8007169856c03f3'
ORIGINAL_COMMIT='3972858d5c896171f80d7bc5a32f3ed1e95a6583'
PEER='research/2026-10-11-dot-accepted-connected-union1568-0133z'

def canonical(value):return digest(json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode())
def literal_imports(text):
    # Independently strip comments while preserving literal string boundaries.
    out=[];i=0;depth=0;string=False
    while i<len(text):
        ch=text[i];two=text[i:i+2]
        if depth:
            if two=='/-':depth+=1;i+=2;continue
            if two=='-/':depth-=1;i+=2;continue
            out.append('\n' if ch=='\n' else ' ');i+=1;continue
        if string:
            out.append(ch);i+=1
            if ch=='\\' and i<len(text):out.append(text[i]);i+=1
            elif ch=='"':string=False
            continue
        if two=='/-':depth=1;out.extend('  ');i+=2;continue
        if two=='--':
            while i<len(text) and text[i]!='\n':out.append(' ');i+=1
            continue
        out.append(ch);string=ch=='"';i+=1
    require(depth==0,'source block comments complete')
    found=[]
    for line in ''.join(out).splitlines():
        match=re.fullmatch(r'\s*(?:public\s+)?import\s+(.+?)\s*',line)
        if match:found.extend(match[1].split())
    return found

def git_file(root,path,expected_hash,expected_size=None):
    mode,oid=tree_path(root,path);require(mode=='100644','regular captured Git source path')
    kind,data=obj(oid);require(kind=='blob' and digest(data)==expected_hash,'captured Git file hash '+path)
    require(expected_size is None or len(data)==expected_size,'captured Git size')
    return {'git_path':path,'git_blob':oid,'sha256':digest(data),'bytes':len(data)},data

def review_static():
    outputs={}
    expected={
      'STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json':'c250c416171cfd895f84812fbca415879ef84e20a4cc779785ac40d6c7c1f9e3',
      'STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json':'8b65e62c0d894269d73429035c40a006c877d88d76a4543edd3300630ae73878',
      'StaticProspectiveUnion1573Imports.lean':'15266faf674115986680f273f04786cdfdd0dc1e78c1f0670471b7634a115322',
      'STATIC-PROSPECTIVE-UNION1573-VALIDATION.json':'20c945b647658ccae79358361e90621d33afec685ed2afcc1660019cdf53a54d',
      'STATIC-PROSPECTIVE-UNION1573-FINAL-HANDOFF.json':'f2fefd6852e469eb73f8e803e77f7f49ded14f67d24cbfb1637288eba0857ff4',
      'derive_static_union1573.py':'6d93074ea965489298b09a4caf69831c9bc42fdab757f127188e4ca12ecd13e1',
      'READER-SOURCE-IDENTITY.json':'3add687a24cc354a6331ecb0aa81cd76a02f7b7842ee651e5c5d5eda60772bd0',
      'STATIC-PROSPECTIVE-UNION1573-READBACK.json':'56e6e70bb080e70278b70327bd66e5bdde52bb7f3d6194edd41330cca9543256',
      'STATIC-PROSPECTIVE-UNION1573-FILE-INVENTORY.json':'e812622af51d8a54363480c37d2e095c91eb87eb0b4171f23e4b2c2ba154a4f1',
      'readback_static_union1573.py':'c91e57c3c5718cfbc31e249b01a2afe22d84daf0630e486b146c3beb2ba00deb'}
    data={}
    for name,h in expected.items():outputs[name],data[name]=pin(D/name,h)
    graph=json.loads(data['STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json']);smap=json.loads(data['STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json']);validation=json.loads(data['STATIC-PROSPECTIVE-UNION1573-VALIDATION.json']);handoff=json.loads(data['STATIC-PROSPECTIVE-UNION1573-FINAL-HANDOFF.json'])
    for doc in [graph,smap,handoff]:require(doc['status']=='STATIC_NOT_KERNEL_ACCEPTED','static scope exact')
    require(validation['status']=='PASS_STATIC_NOT_KERNEL_ACCEPTED' and graph['runnable_lake_setup_or_builder_context'] is False and graph['combined_kernel_or_owned_audit_acceptance'] is False and handoff['combined_kernel_aggregate_audit_executed'] is False,'no runnable context or combined kernel/audit')
    for flags in [validation['execution'],validation['storage']]:
        for name,value in flags.items():
            if name not in ['all_outputs_inside_existing_counted_WN_metadata']:require(value is False,'explicit no-execution/storage-change field '+name)
    require(set(graph['targets'])=={'static/prospective1573'},'single static projection')
    combined=graph['targets']['static/prospective1573'];modules=combined['modules'];mapping=smap['modules']
    require(len(modules)==len(mapping)==smap['module_count']==1573,'1573 module/source-map identities')
    meta_root,_=commit_tree(META_COMMIT);original_root,_=commit_tree(ORIGINAL_COMMIT)
    baseinfo,basedata=git_file(meta_root,PEER+'/DEPENDENCY-GRAPH.json','1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825',3121407)
    base=json.loads(basedata);peer=base['targets']['current/connected'];require(len(peer['modules'])==1568,'captured peer1568 graph')
    mi,mdata=git_file(meta_root,PEER+'/MANIFEST.json','355515fdea8b7515511c24681edbb93b70daf35ff5be1c7cf4bfb6a802f9bb78',501788);manifest=json.loads(mdata)
    oi,odata=git_file(original_root,PEER+'/MANIFEST.json','a907d14ad4a4f172feeba616e8190e51d898203c7e0ec3dcb7b98f24d255e139',501788);oldmanifest=json.loads(odata)
    aci,acdata=git_file(meta_root,PEER+'/ACCEPTANCE.json','439d4989dfb480522f21cc3775dc0185e6607b2892fce82a48104f4a7a056060',597);acceptance=json.loads(acdata)
    require(acceptance['modules']==1568 and acceptance['local_loader_payloads_public'] is False,'peer original public acceptance scope')
    hfinfo,hfdata=pin(P/'lean/FIVE-ACCEPTED-ADDITIONS-FOR-UNION1573-HANDOFF-20261011T0204Z.json','a8da11f75c80dffde842ac6f982a119dc32ca8188269aca90cb1339d39056f9d',4595);five=json.loads(hfdata)
    newnames=[x['module'] for x in five['sources']];require(len(newnames)==len(set(newnames))==5 and newnames==five['safe_new_only_topological_order'],'exact five source topological handoff')
    require(set(modules)==set(peer['modules'])|set(newnames) and not set(newnames)&set(peer['modules']),'exact1568+5, no extra drafts/guards')
    for name,row in peer['modules'].items():require(modules[name]==row,'entire inherited original module dictionary '+name)
    require(sum('module' not in x for x in peer['modules'].values())==64,'64 original missing module fields retained')
    require(combined['order']==peer['order']+newnames and combined['roots']==peer['roots']+newnames,'exact order/root prefixes')
    require(len(peer['roots'])==1451 and len(combined['roots'])==1456 and len(set(combined['roots']))==1456,'1451+5 root count')
    pins={x['path']:x for x in manifest['files']};oldpins={x['path']:x for x in oldmanifest['files']}
    require(len(pins)==len(manifest['files']) and len(oldpins)==len(oldmanifest['files']),'unique manifest paths')
    inherited_tuples=[];new_tuples=[]
    for name in combined['order']:
        row=modules[name];source=mapping[name];require(source['module']==name and source['sha256']==row['sha256'] and source['literal_imports']==row['imports'] and source['combined1573_object_admission']=='NOT_PERFORMED' and source['git_mode']=='100644','graph↔map tuple '+name)
        require(source['body_hash_size_and_literal_imports_checked'] is True,'claimed source check')
        kind,body=obj(source['git_blob']);require(kind=='blob' and len(body)==source['bytes'] and digest(body)==source['sha256'],'full captured source bytes '+name)
        require(literal_imports(body.decode())==row['imports'],'independent source literal imports '+name)
        if name in peer['modules']:
            path=source['source_git_path'];require(path==PEER+'/source-store/'+source['sha256']+'.lean','original hash-addressed peer source path')
            require(source['source_git_ref']=={'kind':'commit','value':ORIGINAL_COMMIT},'original source commit exact')
            require(tree_path(original_root,path)==('100644',source['git_blob']),'original source tree↔blob '+name)
            short=path[len(PEER)+1:];current=pins[short];old=oldpins[short]
            for x in [current,old]:require(x['bytes']==source['bytes'] and x['sha256']==source['sha256'] and x['git_blob']==source['git_blob'],'latest/original source manifest bytes/hash/blob exact')
            origin=source['source_origin'];require(origin['original_record_canonical_sha256']==canonical(peer['modules'][name]) and origin['parent_graph_sha256']==baseinfo['sha256'],'full inherited canonical dictionary provenance')
            require(source['accepted_scope_origin']['sha256']==aci['sha256'],'peer source acceptance origin')
            inherited_tuples.append((name,source['sha256'],source['bytes'],source['git_blob'],row['imports']))
        else:
            original=next(x for x in five['sources'] if x['module']==name);require(source['source_origin']['original_handoff_record']==original and source['source_origin']['handoff_sha256']==hfinfo['sha256'],'exact original five-source handoff record')
            for k in ['source_git_path','sha256','bytes','literal_imports']:require(source[k]==original[k],'exact new source tuple field '+k)
            ref=source['source_git_ref'];require(ref['kind']=='regular_index_blob_snapshot' and ref['git_blob']==source['git_blob'] and ref['git_mode']=='100644' and ref['stage']==0,'captured regular index blob only; no mutable live-index/current admission')
            scope=source['accepted_scope_origin'];scopeinfo,scopedata=pin(REPO/scope['source_git_path'],scope['sha256'],scope['bytes'])
            require(scope['sha256']==validation['inputs']['separate_new_scope_pins'][name]['sha256'],'separate acceptance binding')
            new_tuples.append({**original,'git_blob':source['git_blob'],'separate_acceptance':scopeinfo})
    order=combined['order'];require(len(set(order))==len(order)==1573,'unique1573 order');positions={name:i for i,name in enumerate(order)};external=set();edges=0
    for name,row in modules.items():
        for parent in row['imports']:
            if parent in modules:require(positions[parent]<positions[name],'independent DAG order');edges+=1
            else:external.add(parent)
    require(edges==2839 and sorted(external)==combined['external_imports']==peer['external_imports'] and len(external)==181,'2839 internal edges/181 unchanged externals')
    visited=set();pending=list(combined['roots'])
    while pending:
        name=pending.pop()
        if name in visited:continue
        visited.add(name);pending.extend(x for x in modules[name]['imports'] if x in modules)
    require(visited==set(modules),'independent entire root closure1573')
    aggregate=data['StaticProspectiveUnion1573Imports.lean'].decode();require(literal_imports(aggregate)==order,'import-only aggregate exact1573 order')
    clean=aggregate.split('-/',1)[1];require(clean==''.join('import '+x+'\n' for x in order),'no options/decl/bodies in aggregate')
    require('STATIC_NOT_KERNEL_ACCEPTED' in aggregate and graph['source_inputs']==smap['source_inputs']==validation['inputs'],'exact inputs/static banner')
    for which,file in [('graph','STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json'),('source_map','STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json'),('import_only_aggregate','StaticProspectiveUnion1573Imports.lean'),('validation','STATIC-PROSPECTIVE-UNION1573-VALIDATION.json')]:
        record=handoff['outputs'][which];require(record['path']==outputs[file]['path'] and record['sha256']==outputs[file]['sha256'] and record['bytes']==outputs[file]['bytes'],'handoff output manifest')
    # Inspect derivation source, never import it or run its read-only Git helper.
    tree=ast.parse(data['derive_static_union1573.py']);imports=[n.names[0].name for n in tree.body if isinstance(n,ast.Import)]
    require(not any(n=='Lean' or 'Builder' in n for n in imports),'no Builder/Lean import in derivation source')
    return {'status':'PASS_STATIC_NOT_KERNEL_ACCEPTED','frozen_outputs_and_sources':outputs,'original_peer_graph':baseinfo,'peer_current_and_original_manifests':[mi,oi],'original_peer_acceptance':aci,'five_exact_source_handoff':hfinfo,'all1568_full_original_module_dictionaries_retained':True,'inherited_dictionary_canonical_sha256':canonical(peer['modules']),'inherited_source_tuples_canonical_sha256':canonical(inherited_tuples),'64_original_missing_module_fields_preserved':True,'all1573_captured_source_blobs_bytes_and_independent_literal_imports_checked':True,'five_separate_accepted_source_records':new_tuples,'counts':{'original_sources':1568,'new_sources':5,'static_sources':1573,'original_roots':1451,'static_roots':1456,'internal_edges':edges,'external_names':len(external),'entire_root_closure':len(visited),'aggregate_imports':1573,'aggregate_declarations_options':0},'combined_kernel_or_owned_audit_accepted':False,'current_native_compiled_context_admission_performed':False,'current_live_index_identity_asserted':False,'external_library_resolution_exercised':False,'new_working_or_staged_Lake_context_created':False,'new_mathematical_source_or_uncompiled_G4_draft_added':False,'declaration_count_predicted':False,'remaining_gate':'Authenticate/install the exact five source versions in the receiving native/library context, then fresh aggregate/full owned audit and exact inherited comparison. This file is a static source plan only.'}

def review_gap():
    jp,jd=pin(W/'metadata/NATURAL141-SELECTED-PREFIX-READOUT-GAP-20261011T0225Z.json','aefe0d373ac728066f2360f3d1a13b200332aaf5e0f86fead75de0879a165a58',23722)
    mp,md=pin(W/'metadata/NATURAL141-SELECTED-PREFIX-READOUT-GAP-20261011T0225Z.md','e76a7380f1d803d81999f1a185079642e90c87a67e76f05f522e69f0906775b4',10452);j=json.loads(jd)
    require(j['authenticated_input_count']==len(j['inputs'])==34,'34 exact gap inputs')
    pins=[];texts={};modules={}
    for row in j['inputs']:
        info,data=pin(row['path'],row['sha256'],row['bytes']);pins.append(info)
        if row['path'].endswith('.lean') or row['path'].endswith('.rs'):texts[row['sha256']]=data.decode()
        if row.get('accepted1504_source_identity'):
            modules[row['module']]=row;require(literal_imports(data.decode())==row['imports'],'provider literal imports')
    parent=json.loads(Path(j['inputs'][0]['path']).read_bytes())['targets']['current/connected']['modules']
    require(len(parent)==1504 and len(modules)==j['provider_body_and_accepted1504_sha_bindings']==12,'12 accepted1504 exact provider pins')
    for name,row in modules.items():require(parent[name]['sha256']==row['sha256'] and parent[name]['imports']==row['imports'],'full provider graph identity '+name)
    require(j['note']=={'path':mp['path'],'sha256':mp['sha256'],'bytes':mp['bytes']},'note exact bytes')
    for flag in ['accepted_sources_changed','compiled_elf_copied','compiler_called','git_operation_called','independence_certified','literal_code_history_verified','native_refinement_verified','native_solver_called','public_module_promoted','reference_producer_called','source_admission_verified','tests_called','timed_history_supported']:
        require(j[flag] is False,'no execution/promotion '+flag)
    require(j['prior_accepted_finite_tests']==5 and j['prior_new_tests_reexecuted']==0,'dated existing finite-five only')
    native=texts['46172afa3ba29b19ea924a4110be822104ca236566a69d8d91e5170a0b6d7af3'];epoch=texts['c46a498ac2b5a0f3bc3ea246cc4f6d012ff58871292b8af84cfebe3d45b40354'];eraser=texts['b9c845b56653599d0015e63d3d400e574fbec5955cde5b95271b4e4d5d8777c4'];factor=texts['3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4']
    require('pub view:SelectedView' in native and 'pub conditional_range_witness:Snapshot' in native and 'pub parent:Option<PathId>' in native and 'let key=(parent,state)' in native,'complete selected state + parent path distinction')
    require('pub fn record_views' in native and 'result.reverse();Ok(result)' in native,'entire entering/endpoints reconstruction')
    require('word::Initial::Natural,Vec::new()' in native and 'word::Initial::Conditional(witness),vec![letter]' in native and 'request.terminal=word::Terminal::FullView' in native,'once Natural then conditional one letter FullView')
    require('let mut selected_panel = Row::new();' in epoch and 'view: selected_view(&panel.context, &transition.destination)?' in epoch and 'accumulate(&mut selected_panel' in epoch,'selected-panel literal destinations summed before join')
    require(not re.search(r'\bfn\s+\w*eras\w*\s*\(',native),'current private recorder has no pure erased observer')
    require('register := fun v => if v ∈ P then false else s.register v' in eraser and 'theorem erasePrivateCode_register_outside' in eraser and 'theorem erasePrivateCode_register_inside' in eraser,'one-slot erasure and retained outside fields')
    require('(erasePrivateCode N P a.1, historyProjection (erasePrivateCode N P) a.2)' in factor and '((state s).register, rootForest N s)' in factor and 'forestRegister N (erasePrivateCode N P s)' in factor,'whole erased record/full forest-register observer')
    require('(old : Code N sample × (Fin pastOps.length → Code N sample) → Old)' in factor and '(old (erasedRecord N {h.val} a.2), erasedForestRegister N {h.val} d)' in factor,'arbitrary Old signature and exact private singleton')
    require('NoPrivateWordRead N {h.val} pastOps' in factor and '∀ l ∈ (state (recordEnd pastOps.length a.2.1 a.2.2)).live' in factor,'no-read and all-live support remain hypotheses')
    for name in ['compiler_literal_order_bound','literal_code_history_verified','native_refinement_verified','source_admission_verified','timed_history_supported']:
        require('pub fn '+name+'(&self)->bool {false}' in native,'native explicit unresolved gate '+name)
    control=j['meaningful_future_control'];require(control['future_execution'] is False and control['origin_scope']=='Graph/registry reuse only; proposed new all-tip6 rational source-fit input not constructed','future control remains proposed')
    fixture=json.loads(Path(control['origin']['path']).read_bytes());require(fixture['context']['hybrids']==[[3,2,3],[5,5,6]],'original two-hybrid occurrence registry')
    require(control['private_vertex']==3 and control['retained_vertex']==5 and control['private_hybrid']==0 and control['retained_hybrid']==1,'only upper original vertex erased')
    require([str(Fraction(x)) for x in control['original_gamma']]==['1/3','2/5'] and [1-Fraction(x) for x in control['old_parent_zero_g']]==[Fraction(x) for x in control['original_gamma']],'exact parent1 Gamma orientation')
    require('not already one of the accepted five inputs' in md.decode() and 'NOT a claim both occur on a particular natural prefix' in md.decode(),'unexecuted new scenario/non-injectivity diagnostic qualifications')
    matrix=j['gap_matrix'];require(len(matrix)==8,'eight field gap matrix')
    return {'status':'PASS_SOURCE_ONLY_SCOPED_READOUT_GAP_NO_IMPLEMENTATION_OR_PROMOTION','matrix_receipt':jp,'note':mp,'all34_frozen_input_pins_checked':pins,'all12_accepted1504_provider_bytes_imports_checked':True,'accepted_factor_source_sha256':'3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4','existing_selected_endpoint_vector_and_parent_path_information_retained':True,'current_pure_erasure_and_combined_full_forest_register_observer_missing':True,'arbitrary_Code_Old_not_discharged':'SelectedView omits literal representative/ancestor/dead-option information, and selected_panel sums before join. A conditional range witness is not a complete literal-Code path. No accepted injectivity/refinement theorem is supplied. The diagnostic is general-carrier only, not proof of two naturally reached histories.','one_slot_erasure':'P={h.val}; reset only that original vertex bit in every returned entering/endpoint view; retain every other register slot, complete carried forest, labels, populations and selected path. Never erase the original latent states used by Conditional/COMMON transitions.','smaller_possible_source_specialization':'Old factors through the complete erased selected endpoint vector. A pure observer and exact whole-vector coefficient fibre sum are plausible representations; encoding/erasure/forest quotient commuting equalities, conditional path/native refinement, actual bank/support and literal calendar order still require explicit proof/checks. No new native law or initializer is accepted by this review.','no_per_copy_or_block_multiplicity_rescaling':True,'local_global_labels_transport_must_remain_bijective':True,'all_live_no_read_positive_arm_original_bank_and_occurrence_order_guards_remain_explicit':True,'proposed_future_control':{'original_hybrid_slots':[3,5],'erase_only_upper_vertex':3,'retain_correlated_lower_vertex':5,'original_parent1_gamma':['1/3','2/5'],'old_parent0_g':['2/3','3/5'],'all_tip6_new_input_not_constructed_or_executed':True,'current_fixture_local_samples':fixture['context']['local_samples']},'no_universal_native_source_refinement_source_admission_literal_Code_or_timed_history_claim':True,'no_tests_compilers_native_reference_producers_or_accepted_source_edits':True,'public_native_binary443a1eb6_authenticated_as_pin_only_not_copied_or_executed':True,'no_new_combined1573_certificate':True}

for name,review in [('STATIC1573-INDEPENDENT-SAVED-QC-ATTEMPT1.json',review_static),('NATURAL141-RUST-READOUT-GAP-INDEPENDENT-SOURCE-QC-ATTEMPT1.json',review_gap)]:
    report={'schema':'independent_saved_static_sources_and_scope_v1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes()),'no_Git_commands_or_target_imports_or_producers_or_source_edits':True}
    try:report['checks']=review();report['status']=report['checks']['status']
    except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
    out=Q/name;require(not out.exists(),'immutable own output');out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(out.read_bytes()),'bytes':out.stat().st_size,'error':report.get('error')}))
require(sum(p.stat().st_size for p in Q.iterdir() if p.is_file())<128*1024,'full new own QC/source directory below128KiB')
