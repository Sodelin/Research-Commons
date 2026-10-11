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


import re
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

import ast
import re
Q=W/'design-qc/thin1575-static-saved-20261011T0250Z-solver_design_recovery'
D=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/metadata/static-union1575-thin-source-plan-20261011T024500Z')
OLD=D.parent/'static-union1573-source-plan-20261011T022330.460416Z'
PUBLIC=W/'metadata/connected1570-readonly-review-20261011T0238Z/PUBLIC-CONNECTED1570-READONLY-REVIEW-ATTEMPT1.json'
PEER='62020166e3e7ef690838f50b13caa149ede419ec'
PACKET='research/2026-10-11-dot-accepted-connected-union1570-g4span-0225z'

def canonical(value):return digest(json.dumps(value,sort_keys=True,separators=(',',':')).encode())

def fixed_json(path,h,size=None):
    info,data=pin(path,h,size);return info,json.loads(data)

def captured_file(root,path,h,size=None):
    mode,oid=tree_path(root,path);require(mode=='100644','regular captured commit blob')
    kind,data=obj(oid);require(kind=='blob' and digest(data)==h and (size is None or len(data)==size),'full captured blob hash/size')
    return {'git_tree_path':path,'git_blob':oid,'bytes':len(data),'sha256':h},data

def check():
    ii,inventory=fixed_json(D/'STATIC-PROSPECTIVE-UNION1575-FILE-INVENTORY.json','e4b82f108f65456f243e8bce08719e463901786cb439b6f808f7b73ab5544b7b',2606)
    require(inventory['status']=='STATIC_NOT_KERNEL_ACCEPTED' and inventory['file_count_including_manifest']==7,'frozen thin inventory static-only')
    identities=[];contents={};current_files=list(D.iterdir())
    require(len(current_files)==7 and all(p.is_file() and not p.is_symlink() for p in current_files),'exact7 frozen regular files')
    for row in inventory['files_except_this_manifest']:
        path=Path(row['path']);require(path.parent==D,'all6 bounded thin paths')
        info,data=pin(path,row['sha256'],row['bytes']);require(path.stat().st_blocks*512==row['allocated_bytes'],'exact frozen file allocation')
        identities.append(info);contents[path.name]=data
    require({p.name for p in current_files}==set(contents)|{Path(ii['path']).name},'inventory covers exact7')
    total=sum(p.stat().st_size for p in current_files);allocated=sum(p.stat().st_blocks*512 for p in current_files)
    require(total==inventory['total_content_bytes_including_manifest']==93270 and allocated==inventory['total_allocated_bytes_including_manifest']==110592,'actual thin content/allocation retained')
    require(total<98304 and inventory['content_limit_bytes']==98304,'thin content below96KiB; allocation separately reported')
    delta=json.loads(contents['STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json']);validation=json.loads(contents['STATIC-PROSPECTIVE-UNION1575-VALIDATION.json']);handoff=json.loads(contents['STATIC-PROSPECTIVE-UNION1575-FINAL-HANDOFF.json']);readback=json.loads(contents['STATIC-PROSPECTIVE-UNION1575-READBACK.json'])
    require(delta['status']==handoff['status']=='STATIC_NOT_KERNEL_ACCEPTED','delta and handoff uncompiled scope')
    require(delta['source_inputs']['peer_commit']==PEER and readback['delta_sha256']==digest(contents['STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json']),'exact peer and delta cross-pin')
    for key,name in [('aggregate','StaticProspectiveUnion1575Imports.lean'),('source_plan_delta','STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json'),('producer_source','derive_static_union1575_delta.py')]:
        row=validation[key];require(row=={'path':str(D/name),'sha256':digest(contents[name]),'bytes':len(contents[name])},'saved validation output/source cross-pin')
    for key,name in [('delta','STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json'),('validation','STATIC-PROSPECTIVE-UNION1575-VALIDATION.json'),('import_only_aggregate','StaticProspectiveUnion1575Imports.lean'),('producer_source','derive_static_union1575_delta.py')]:
        require(handoff[key]=={'path':str(D/name),'sha256':digest(contents[name]),'bytes':len(contents[name])},'saved handoff exact cross-pin')
    source=contents['derive_static_union1575_delta.py'];source_tree=ast.parse(source)
    require(digest(source)=='89ea707c057a4bd2837ae313cb3fe7986e4f8be6e8d656edbfe7b4675ab6328f','frozen author source exact')
    oldinventoryinfo,oldinventory=fixed_json(OLD/'STATIC-PROSPECTIVE-UNION1573-FILE-INVENTORY.json','e812622af51d8a54363480c37d2e095c91eb87eb0b4171f23e4b2c2ba154a4f1',4233)
    old_rows=validation['all_old1573_file_identities_pre_post'];require(len(old_rows)==len(list(OLD.iterdir()))==10,'old10 inventory count')
    old_pins=[]
    for name,row in old_rows.items():
        require(row['path']==str(OLD/name),'old bound file path');info,data=pin(row['path'],row['sha256'],row['bytes']);old_pins.append(info)
    for row in oldinventory['files_except_this_manifest']:
        require(old_rows[Path(row['path']).name]['sha256']==row['sha256'] and old_rows[Path(row['path']).name]['bytes']==row['bytes'],'old original inventory retained')
    gi,gdata=pin(OLD/'STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json','c250c416171cfd895f84812fbca415879ef84e20a4cc779785ac40d6c7c1f9e3',627489)
    mi,mdata=pin(OLD/'STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json','8b65e62c0d894269d73429035c40a006c877d88d76a4543edd3300630ae73878',2745885)
    oldg=json.loads(gdata)['targets']['static/prospective1573'];oldmap=json.loads(mdata)['modules']
    oldsourceinfo,oldsource=pin(OLD/'derive_static_union1573.py','6d93074ea965489298b09a4caf69831c9bc42fdab757f127188e4ca12ecd13e1',24827)
    oldparser=next(n for n in ast.parse(oldsource).body if isinstance(n,ast.FunctionDef) and n.name=='literal_imports');newparser=next(n for n in source_tree.body if isinstance(n,ast.FunctionDef) and n.name=='literal_imports')
    require(ast.dump(oldparser,include_attributes=False)==ast.dump(newparser,include_attributes=False),'target parser textual AST unchanged; never invoked')
    publicinfo,public=fixed_json(PUBLIC,'c92c6be19d13504c25447f353142864225942b1e1baeb1df9d55cdf25f8a5162',44331)
    require(delta['source_inputs']['public1570_saved_review']==handoff['public1570_saved_review']==publicinfo,'exact public1570 saved review bindings')
    require(readback['public1570_review_sha256']==validation['public1570_review_pre_post_sha256']==publicinfo['sha256'],'review unchanged cross-pins')
    require(public['status']=='PASS_EXACT_PUBLIC_GRAPH_SOURCES_IMPORTS_FULL_AUDIT_AND_ALL_1568_RECORDS' and public['fixed_current_commit']==PEER,'actual public1570 saved-only PASS')
    require(public['source_graph']['modules']==1570 and public['source_graph']['sha256']=='ba9148757fda063c86b40db0d453a3eccd85c224800a8b98ebd12f6ffe31f367','actual saved1570 graph binding')
    require(public['whole_inherited_record_equality']['matched_names']==101705 and public['whole_inherited_record_equality']['all_parsed_fields_including_module_identical'],'public reviewer exact prior record qualifier')
    require((public['complete1570_audit']['declarations'],public['complete1570_audit']['theorems'],public['complete1570_audit']['raw_bytes'])==(101749,92182,115166638),'public saved audit counts only')
    require(public['complete1570_audit']['raw_sha256']=='026783d9a4476842d9403b041b112fa08373b250885672163e3a47bcf17686ab','saved full public raw audit identity')
    pubsourceinfo,_=pin(public['source']['path'],public['source']['sha256'],public['source']['bytes'])
    root,_=commit_tree(PEER)
    ginfo,gb=captured_file(root,PACKET+'/DEPENDENCY-GRAPH.json','ba9148757fda063c86b40db0d453a3eccd85c224800a8b98ebd12f6ffe31f367',3741851)
    manifestinfo,mb=captured_file(root,PACKET+'/MANIFEST.json','ddeb64940618cf3253971c47380c807145fdc2e9b2516e06d5bd3942a3f41587',454402)
    acinfo,ab=captured_file(root,PACKET+'/ACCEPTANCE.json','ce2a64c47885084ff52279da8242f16dccdb25eeeac89b7675478692156cdc64',765)
    peer=json.loads(gb)['targets']['current/connected'];manifest={r['path']:r for r in json.loads(mb)['files']};acceptance=json.loads(ab)
    require(acceptance['modules']==1570 and acceptance['graph_sha256']==ginfo['sha256'],'reported public acceptance pins exactgraph')
    hi,hdata=pin(P/'lean/FIVE-ACCEPTED-ADDITIONS-FOR-UNION1573-HANDOFF-20261011T0204Z.json','a8da11f75c80dffde842ac6f982a119dc32ca8188269aca90cb1339d39056f9d')
    h=json.loads(hdata);five=h['safe_new_only_topological_order'];require(five==delta['recipe']['cloud_addition_order'] and len(five)==len(set(five))==5,'five fixed additions exact order')
    base=set(oldg['modules'])-set(five);pair=set(peer['modules'])-base
    require(len(base)==1568 and pair=={'G4ActualOriginalSpanDiagonal','G4ActualOriginalSpanNaturalAverage'} and not set(five)&set(peer['modules']),'1570 exact2 additions vs1568 and5 separately absent')
    require(all(peer['modules'][n]==oldg['modules'][n] for n in base),'all1568 full module dictionaries literal retained')
    require([n for n in peer['order'] if n in base]==[n for n in oldg['order'] if n in base] and [n for n in peer['roots'] if n in base]==[n for n in oldg['roots'] if n in base],'1568 original restricted order and roots retained')
    require(peer['external_imports']==oldg['external_imports'],'external list retained exactly')
    modules=dict(peer['modules']);modules.update({n:oldg['modules'][n] for n in five});order=peer['order']+five;roots=peer['roots']+five
    require(len(modules)==len(set(order))==len(order)==1575 and set(order)==set(modules),'full reconstructed1575 exact names/order')
    specs=[];new_pair_rows=[];five_rows=[];body_total=0
    for name in peer['order']:
        record=modules[name];path='source-store/'+record['sha256']+'.lean';row=manifest[path]
        info,body=captured_file(root,PACKET+'/'+path,row['sha256'],row['bytes']);require(info['git_blob']==row['git_blob'] and row['sha256']==record['sha256'],'all1570 original source-store blob/manifest/graph bindings')
        require(literal_imports(body.decode('utf8'))==record['imports'],'all1570 independently parsed imports')
        if name in base:
            orig=oldmap[name];require((orig['sha256'],orig['bytes'],orig['literal_imports'])==(record['sha256'],len(body),record['imports']),'all1568 original source map tuple unchanged')
        else:
            new_pair_rows.append({'module':name,'sha256':record['sha256'],'bytes':len(body),'imports':record['imports'],'source_git_path':PACKET+'/'+path,'git_blob':info['git_blob'],'source_git_commit':PEER,'original_peer_module_record':record})
        specs.append([name,record['sha256'],len(body),record['imports'],info['git_blob']]);body_total+=len(body)
    require(new_pair_rows==delta['two_peer_G4_records'],'exact two peer records and origins')
    for name in five:
        orig=oldmap[name];kind,body=obj(orig['git_blob']);record=modules[name]
        require(kind=='blob' and len(body)==orig['bytes'] and digest(body)==orig['sha256']==record['sha256'] and literal_imports(body.decode())==orig['literal_imports']==record['imports'],'all5 captured oldmap immutable full blobs/imports')
        row={k:orig[k] for k in ['module','sha256','bytes','literal_imports','source_git_path','git_blob','source_git_ref','accepted_scope_origin']};five_rows.append(row)
        scope=row['accepted_scope_origin'];pin(REPO/scope['source_git_path'],scope['sha256'],scope['bytes'])
        require(row['source_git_ref']['git_blob']==row['git_blob'] and row['source_git_ref']['stage']==0 and row['source_git_ref']['git_mode']=='100644','captured immutable5 blob snapshots no liveindex assertion')
        hrow=next(r for r in h['sources'] if r['module']==name);require(all(orig[k]==hrow[k] for k in ['module','sha256','bytes','literal_imports','source_git_path']),'fixed5handoff tuples')
        specs.append([name,orig['sha256'],len(body),orig['literal_imports'],orig['git_blob']]);body_total+=len(body)
    require(five_rows==delta['five_separately_accepted_sources'],'five exact thin delta rows')
    pos={n:i for i,n in enumerate(order)};edges={(n,d) for n in order for d in modules[n]['imports'] if d in modules}
    require(all(pos[d]<pos[n] for n,d in edges),'entire1575 ordered DAG')
    external=sorted({d for n in order for d in modules[n]['imports'] if d not in modules});require(set(external)==set(peer['external_imports']),'181 unchanged external dependencies')
    require(len(roots)==len(set(roots)) and set(roots)<=set(modules),'1457unique roots subset')
    visited=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n not in visited:visited.add(n);todo.extend(d for d in modules[n]['imports'] if d in modules)
    require(visited==set(modules),'full1575 actual root closure')
    counts={'peer_base_modules':1570,'inherited_original1568':1568,'new_peer_G4':2,'separate_cloud_additions':5,'prospective_modules':1575,'roots':len(roots),'internal_DAG_edges':len(edges),'external_imports':len(external)}
    require(counts==delta['counts']==validation['counts']==handoff['counts'] and (len(roots),len(edges),len(external))==(1457,2844,181),'all exact static count cross-pins')
    fingerprints={'canonical_order_sha256':canonical(order),'canonical_roots_sha256':canonical(roots),'canonical_name_sha_import_tuples_sha256':canonical([[n,modules[n]['sha256'],modules[n]['imports']] for n in order])}
    require(all(delta['recipe'][k]==v for k,v in fingerprints.items()),'all3 reconstructed canonical recipe fingerprints')
    aggregate=contents['StaticProspectiveUnion1575Imports.lean']
    expected=('/- STATIC_NOT_KERNEL_ACCEPTED. Import-only prospective1575 source plan.\nPeer1570 fixed Git base plus five separately accepted cloud sources.\nNo staging, object admission, runnable Lake setup, compiler or combined audit. -/\n'+''.join('import '+n+'\n' for n in order)).encode()
    require(aggregate==expected and literal_imports(aggregate.decode())==order,'exact importonly aggregate1575 no declarations/options')
    require(body_total==validation['total_module_body_bytes_read']==15565137,'all1575 full source bytecount')
    scope=delta['scope'];require(all(scope[k] is False for k in ['combined1575_kernel_acceptance','compiled_object_or_native_admission','context_staging_cache_or_Git_mutation','runnable_Lake_setup_claim','master_closure']) and scope['declaration_count_prediction'] is None,'all static-only boundaries explicit')
    require(validation['compiler_or_native_processes']==validation['Git_mutations']==0 and readback['live_index_or_native_cache_admission'] is False,'saved source-only action scope')
    for info in identities+[ii]+old_pins+[publicinfo]:pin(info['path'],info['sha256'],info['bytes'])
    fi,fd=pin(Q/'EXPLORATORY-SCHEMA-READ-FAILURE-AND-CORRECTION.json')
    return {'thin7_frozen_inventory':ii,'all6_frozen_files_and_source':identities,'total_thin_content_bytes':total,'total_thin_file_allocated_bytes':allocated,'thin_content_limit_bytes':98304,'old10_files_authenticated_unchanged':old_pins,'all1568_entire_original_module_dicts_retained':True,'original_missing_module_fields_retained':sum('module' not in peer['modules'][n] for n in base),'all1568_restricted_order_roots_and_external_list_retained':True,'peer_fixed_commit':PEER,'peer_root_tree':root,'peer_graph':ginfo,'peer_manifest':manifestinfo,'peer_reported_acceptance':acinfo,'public1570_saved_review':publicinfo,'public1570_reader_source':pubsourceinfo,'public1570_audit_recomputed_in_this_review':False,'public1570_scope':'Bound existing exact public-source/import/full-audit saved PASS only; unavailable private loader/native/cache payloads are not authenticated or admitted here.','public1570_saved_counts':{'declarations':101749,'theorems':92182,'all101705_inherited_full_records_exact_saved_review':True,'44G4_global_new_29thm_saved_review':True},'all1575_immutable_full_source_blobs_hash_size_and_independent_imports_verified':True,'module_source_tuples_canonical_sha256':canonical(specs),'module_source_body_bytes':body_total,'five_fixed_source_handoff':hi,'five_exact_additive_rows':five_rows,'two_exact_peer_G4_rows':new_pair_rows,'reconstructed_static_counts':counts,'recipe_fingerprints':fingerprints,'importonly_aggregate_exact_all1575':True,'combined_kernel_or_ownership_audit_acceptance':False,'local_private_native_cache_context_admission':False,'external_library_compatibility_or_availability_exercised':False,'current_live_index_identity_asserted':False,'new_context_or_staging_or_Lake_or_execution_created':False,'no_Git_commands_or_mutations_target_imports_compilers_native_reference_or_producer_invocations_by_this_reader':True,'preserved_own_exploratory_schema_failure_and_correction':fi,'publication_hold':'Prior fetch620 resource receipt13c26f4f remains conditional: no more fetch or mutation before exact complete zlib6 blob/tree/allocation/index/commit funding gate; this source-only QC grants no resource or scientific promotion.','source_scope':'Natural141 output resets only its selected private COMMON register slot to false, retaining every other slot and the full carried forest. Arbitrary literal Code Old does not follow from selected runtime record data. G4 scalar actual-span/fresh-natural averaging laws do not imply that full Old forest law, source constructor, passive mixed-colour topology decoder, or master closure.'}

report={'schema':'THIN1575_FIXED_SOURCE_PLAN_INDEPENDENT_SAVED_QC_V1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':digest(Path(__file__).read_bytes()),'own_Git_parser_parent_sha256':'d38a29eb2c2546eccd30ff45321f2805eadab2b9061d1984f343cf51f6897a0d','own_literal_imports_parser_parent_sha256':'700524040b9387b72bd805e254d5383593dcf523ef6ea49411cde6dbe396da4d'}
try:report['checks']=check();report['status']='PASS_STATIC_NOT_KERNEL_ACCEPTED_THIN1575_EXACT_SOURCE_ONLY'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
data=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
require(sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file())+((len(data)+4095)//4096)*4096<=65536,'entire new QC files allocation at most64KiB')
out=Q/'THIN1575-INDEPENDENT-SOURCE-SAVED-QC-ATTEMPT1.json';require(not out.exists(),'immutable own receipt');out.write_bytes(data)
print(json.dumps({'status':report['status'],'path':str(out),'sha256':digest(data),'bytes':len(data),'reviewer_sha256':report['reviewer_sha256'],'error':report.get('error'),'directory_content_bytes':sum(p.stat().st_size for p in Q.iterdir() if p.is_file()),'directory_file_allocated_bytes':sum(p.stat().st_blocks*512 for p in Q.iterdir() if p.is_file())}))
