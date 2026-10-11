#!/usr/bin/env python3
"""Attributed independent frozen-byte/source QC. No target imports or Git calls.
Retains and reuses authenticated OWN v2 definitions; nothing is overwritten.
Contributor: /root/solver_design_recovery. M/G supplied as immutable CLI pins.
"""
import argparse, ast, base64, difflib, gzip, hashlib, json, pathlib, struct
P=pathlib.Path(__file__);Q=P.parent
old=Q/'review_text_publication_v2.py';ob=old.read_bytes()
assert hashlib.sha256(ob).hexdigest()=='fd70b09e12a0a284f138eeeedfe27981143feba0956b2797bdbfd745f7264968'
ns={'__file__':str(P),'__name__':'own_frozen_v3_byte_review'}
exec(compile(ob.split(b'\nap=argparse.',1)[0],str(old),'exec'),ns)
pin,sha,canon=ns['pin'],ns['sha'],ns['canon'];D=ns['D']
v2='9970fdb3088e4f441aa162191ac4cdb30dfe8df5794e1f5f3edc71fdb28a9f1c'
v3='6c9fd8cd57d8cc8400804e104c652857275ab66c1559f98a68e8dbbff71da15c'
physical='c8194740769d523354c5ede7049fb54edc1fac03b9d6b605aaaa53d04f7188e4'
original_protocol=ns['source']()
vi,vb=pin(D/'publish_reviewed_text_v3.py',v3,11807)
_,p2=pin(D/'publish_reviewed_text_v2.py',v2,9104)
di,db=pin(D/'EXACT-OWN-PUBLISHER-V3-INDEX-FUNDING.patch','eb89d499edb59300ef6c7edb5e865adb7721fff90ddaf9da464b6a7094867086',8317)
assert db==''.join(difflib.unified_diff(p2.decode().splitlines(True),vb.decode().splitlines(True),fromfile='publish_reviewed_text_v2.py',tofile='publish_reviewed_text_v3.py')).encode()
ci,cb=pin(D/'OWN-INDEX-TRANSIENT-FUNDING-CORRECTION.json','f057d3facaa85e44f5e89959c594fb89472d643ef521eebdff3278011ca01b96',1455)
c=json.loads(cb);assert c['original_v2_sha256']==v2 and c['new_v3_sha256']==v3
assert (c['new_loose_metadata_reserve_bytes'],c['separate_index_rewrite_reserve_bytes'],c['total_publication_allocation_reserve_bytes'])==(6291456,12582912,18874368)
f=lambda b:{x.name:ast.dump(x) for x in ast.parse(b).body if isinstance(x,ast.FunctionDef)}
a,b=f(p2),f(vb)
assert set(b)-set(a)=={'index_rewrite_envelope'} and not set(a)-set(b)
assert {n for n in a if a[n]!=b[n]}=={'base','inputs','funding','prepare','apply'}
t=vb.decode()
for text in ("A.E['GIT_INDEX_VERSION']='4'","assert sha(A.I.read_bytes())==BASE_INDEX_SHA","assert len(rows)<=256",'assert bound<INDEX_REWRITE_RESERVE','assert allocated+256*1024<=LOOSE_METADATA_RESERVE',"assert r['tmp_free_bytes']>INDEX_REWRITE_RESERVE+2*1024**2","r['global_conservative_max_bytes']+ALLOCATION_RESERVE<2013265920"):
 assert text in t,text
assert t.index('envelope=funding(r,b,t,a,rows+[rx],entries)')<t.index('for x in rows:write_blob(x)')
assert t.count("A.git('write-tree')")==1
protocol={'original_v1_hold_and_v2_correction':original_protocol,'publisher_source':vi,'v2_to_v3_exact_full_patch':di,'root_index_funding_correction':ci,'own_original_reader':pin(old)[0],'changed_functions':['base','inputs','funding','prepare','apply'],'one_new_function':'index_rewrite_envelope','manual_full_source_review':'V3 retains the reviewed full-byte/index protocol. Before writes, actual v4 index SHA/checksum/count, byte-length paths, full future entries/directories and complete Gate/QC/receipt are costed. Charge new entries plus following-old suffix expansion plus entire future TREE, retaining all old extension bytes. Fixed6MiB loose plus separate12MiB index =18MiB under unchanged global abort; /tmp also exceeds12MiB+2MiB. Final all-row/readback and one-tree checks remain. This is fixed serializer funding, not an observed peak or generic Git bound.'}
# Own in-memory derivative only: v2 report/check changes exactly to v3 reserve
# schema/projection and labels. The6MiB loose-object predicate stays unchanged.
fn=next(x for x in ast.parse(ob).body if isinstance(x,ast.FunctionDef) and x.name=='funding')
ft=ast.get_source_segment(ob.decode(),fn)
changes=[('(524288,131072,16384,6291456)','(524288,131072,16384,18874368)'),('remaining+6291456<2013265920','remaining+18874368<2013265920'),("'full6MiB_plus_remaining_Q_projected':usage['conservative']+remaining+6291456","'full18MiB_plus_remaining_Q_projected':usage['conservative']+remaining+18874368"),('tmp>len(idxraw)+2097152','tmp>12582912+2097152'),("'index_plus2MiB':len(idxraw)+2097152","'index_rewrite12MiB_plus2MiB':12582912+2097152"),('independent_fixed_text_publication_funding_qc_v2','independent_fixed_text_publication_funding_qc_v3'),('PASS_FIXED_V2_SOURCE_ALL_FROZEN_ROWS_AND_CURRENT_SEPARATE_FUNDING','PASS_FIXED_V3_SOURCE_ALL_FROZEN_ROWS_AND_CURRENT_SEPARATE_FUNDING'),('full6MiB/26root funding','full18MiB/26root funding including12MiB index rewrite')]
for x,y in changes:
 assert ft.count(x)==1,(x,ft.count(x));ft=ft.replace(x,y)
ns['PUB']=v3;exec(compile(ft,str(P)+'#own_funding_derivative','exec'),ns)
ap=argparse.ArgumentParser();ap.add_argument('--manifest-sha',required=True);ap.add_argument('--gate-sha',required=True);args=ap.parse_args()
assert len(args.manifest_sha)==len(args.gate_sha)==64
r=ns['funding'](args,protocol)
g=json.loads((D/'FUNDING-GATE.json').read_bytes());m=json.loads((D/'INPUTS.json').read_bytes())
assert (g['loose_metadata_reserve'],g['index_rewrite_reserve'])==(6291456,12582912)
lib,z=ns['own_byte_library']();ib=z['INDEX'].read_bytes();assert sha(ib)==physical
magic,version,n=struct.unpack('!4sII',ib[:12]);assert magic==b'DIRC' and version==4 and hashlib.sha1(ib[:-20]).digest()==ib[-20:]
idx,meta=z['index_entries'](ib);assert len(idx)==n
rows=[ns['blob'](x['source_path'],x['git_tree_path'],x['bytes'],x['sha256']) for x in m['files']]
rows.append(ns['blob'](D/'INPUTS.json',m['prefix']+'/INPUT-MANIFEST.json'))
added={x['git_tree_path'].encode('utf8') for x in rows};assert len(rows)==len(added)<=256 and all(len(p)<=1024 for p in added)
for name in ('FUNDING-GATE.json','INDEPENDENT-PUBLICATION-QC.json','ACTUAL-PUBLICATION.json'):
 path=m['prefix']+'/'+name;ns['normalized'](path);assert path not in idx and not z['os'].path.lexists(z['REPO']/path)
oldpaths={p.encode('utf8') for p in idx};entries=oldpaths|added;assert len(entries)==len(oldpaths)+len(added)
directories={b''}
for p in entries:
 parts=p.split(b'/')
 directories.update(b'/'.join(parts[:i]) for i in range(1,len(parts)))
maxold=max(map(len,oldpaths));ne=sum(64+10+len(p)+1 for p in added);succ=len(added)*(maxold+10)
ew=max(2,len(str(len(entries))));sw=max(2,len(str(len(directories))))
te=8+sum(len(d.rsplit(b'/',1)[-1])+1+ew+1+sw+1+20 for d in directories)
env={'current_binary_index_sha256':sha(ib),'current_binary_index_bytes':len(ib),'current_version':version,'current_entries':n,'future_entries':len(entries),'added_entries':len(added),'max_old_path_utf8_bytes':maxold,'new_entry_fixed_varint_full_suffix_bytes':ne,'old_successor_max_expansion_bytes':succ,'future_directory_nodes':len(directories),'future_directory_set_sha256':sha(b'\0'.join(sorted(directories))),'entire_future_TREE_extension_envelope_bytes':te,'future_index_file_upper_bound_bytes':len(ib)+ne+succ+te,'fixed_index_rewrite_reserve_bytes':12582912,'no_old_TREE_extension_subtraction':True,'scope':'Conservative Git v4 serialization envelope, not an observed transient peak. Independently reviewed fixed source/manifest/gate required.'}
assert env==g['known_fixed_index_envelope'] and env['future_index_file_upper_bound_bytes']<12582912
r['known_fixed_index_envelope']=env;r['own_in_memory_funding_derivative_exact_substitutions']=changes
r['source_only_scope']='Saved native5/5 rows and G4/Lean drafts are supplied full texts; no rerun/admission/remote completion. Independent byte QC only. Root must recost Gate/this full QC/full actual receipt and remeasure before mutation.'
raw=(json.dumps(r,sort_keys=True,separators=(',',':'))+'\n').encode()
encoded=base64.b85encode(gzip.compress(raw,compresslevel=9,mtime=0)).decode('ascii')
out={'status':r['status'],'publisher_sha256':v3,'manifest_sha256':r['manifest_sha256'],'funding_gate_sha256':r['funding_gate_sha256'],'decoded_full_review_bytes':len(raw),'decoded_full_review_sha256':sha(raw),'full_review_encoding':'gzip_base85','full_review':encoded,'reviewer':'/root/solver_design_recovery','reader':pin(P)[0]}
assert gzip.decompress(base64.b85decode(encoded))==raw
data=(json.dumps(out,sort_keys=True,separators=(',',':'))+'\n').encode();assert len(data)<=4096,('lossless_receipt_size',len(data))
assert ns['own_alloc']()+4096<=32768
dest=Q/'V3-FROZEN-INPUTS-AND-FUNDING-QC.json'
with dest.open('xb') as f:f.write(data)
print(json.dumps({'status':r['status'],'receipt':pin(dest)[0],'decoded_full_body_bytes':len(raw),'decoded_full_body_sha256':sha(raw),'own_allocated_including_directory':ns['own_alloc'](),'known_cost':r['known_exact_cost'],'capacity':r['capacity'],'known_fixed_index_envelope':env},sort_keys=True))
