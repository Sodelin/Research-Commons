"""Additive exact-byte desktop integration; never writes an original input."""
import argparse, copy, hashlib, json, re, shutil, subprocess
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repository',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
repo=args.repository.resolve()
prefix='research/2026-10-10-codex-lean-rust-parity/lean'
hist=f'{prefix}/evidence/proof-extensions/history-accepted-union-1497/20261010T204542.182773Z'
dot='research/2026-10-10-dot-modular-lean-reuse-handoff-1448z/g3-fixed-residue-critical-bridge-1522z'
out=args.output.resolve()
sha=lambda b:hashlib.sha256(b).hexdigest()
def blob(path):
    ref='f1636499b963d3982b2dfff0f2757042b1796d21' if path.startswith(dot+'/') else 'cb6642f60a76eaa005d406763367635afca3dc9c'
    return subprocess.check_output(['git','-c','core.longpaths=true','-C',str(repo),'show',ref+':'+path])
def save(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    assert not path.exists(),path
    path.write_bytes(data)
def js(data):return (json.dumps(data,indent=2)+'\n').encode()

original=blob(hist+'/DEPENDENCY-GRAPH.json')
assert sha(original)=='b1cf28461bce4bfc2ba4adcf26e4eca4c76214783cf29e2557ce134db782838e'
graph=json.loads(original); old=graph['targets']['current/connected']
assert len(old['modules'])==1497
packet=json.loads(blob(dot+'/ADDITIVE-PROFILE.json')); added=packet['source_scope']
overlap=sorted(set(old['modules'])&set(added['modules']))
assert len(overlap)==6 and all(all(old['modules'][m][k]==added['modules'][m][k] for k in ['sha256','imports']) for m in overlap)
new=sorted(set(added['modules'])-set(old['modules']))
assert len(new)==64
union=copy.deepcopy(old)
union['modules'].update({m:e for m,e in added['modules'].items() if m not in old['modules']})
union['order']+= [m for m in added['order'] if m not in old['modules']]
union['roots']+= [m for m in added['roots'] if m not in union['roots']]
union['status']='PREPARED_EXACT_ADDITIVE_UNION_UNVERIFIED'
assert len(union['modules'])==len(set(union['order']))==1561
positions={m:i for i,m in enumerate(union['order'])}
assert all(positions[d]<positions[m] for m,e in union['modules'].items() for d in e['imports'] if d in positions)
graph['targets']['history/accepted1497']=copy.deepcopy(old)
graph['targets']['history/accepted1497']['required_for_accepted_release']=False
graph['targets'][packet['profile']]=added
graph['targets']['current/connected']=union
graph['scope']='Exact additive desktop union; preserved history/accepted1497 profile plus G3 selected profile. Fresh aggregate and owned audit required before acceptance.'
pins=[]
for m in union['order']:
    e=union['modules'][m]
    path=hist+'/sources/'+m.replace('.','/')+'.lean' if m in old['modules'] else dot+'/source-store/'+e['sha256']+'.lean'
    b=blob(path); assert sha(b)==e['sha256'],(m,path)
    # Parser records the literal imports in these frozen Lean bodies.
    text=b.decode('utf-8'); clean=re.sub(r'/\-.*?\-/','',text,flags=re.S); clean=re.sub(r'--[^\n]*','',clean)
    imports=[]
    for line in clean.splitlines():
        match=re.match(r'\s*(?:public\s+|private\s+)?import\s+(.+)',line)
        if match: imports+=match.group(1).split()
    assert imports==e['imports'],(m,imports,e['imports'])
    dest=out/'source-store'/(e['sha256']+'.lean')
    if not dest.exists():save(dest,b)
    pins.append({'module':m,'sha256':e['sha256'],'bytes':len(b),'imports':imports,'original_path':path})
save(out/'DEPENDENCY-GRAPH.json',js(graph))
save(out/'provenance/ACCEPTED1497-GRAPH.json',original)
save(out/'provenance/ADDITIVE-PROFILE.json',blob(dot+'/ADDITIVE-PROFILE.json'))
scripts={
 'build_connected.py':prefix+'/scripts/build_connected.py',
 'AuditTemplate.lean':prefix+'/scripts/AuditTemplate.lean',
 'build_with_mathlib_overlay.py':prefix+'/evidence/cache-install-transport/20261010T204700.350834Z/ORIGINAL-NAMESPACE-OVERLAY.py',
 'build_with_authenticated_overlay.py':prefix+'/evidence/cache-install-transport/20261010T204700.350834Z/ORIGINAL-AUTHENTICATED-OVERLAY.py'}
expected=['13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc','f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a','09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0','ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc']
scriptpins={}
for (name,path),want in zip(scripts.items(),expected):
    b=blob(path);assert sha(b)==want;save(out/'scripts'/name,b);scriptpins[name]=want
licensepath=prefix+'/evidence/read-only-prerequisites/mathlib-funext/20261010T134426.130726Z/third-party/mathlib/LICENSE'
save(out/'third-party/mathlib/LICENSE',blob(licensepath))
save(out/'SOURCE-MANIFEST.json',js({'modules':pins,'module_count':1561,'shared_exact_modules':overlap,'new_modules':new}))
save(out/'PREPARATION.json',js({'status':'PREPARED_UNVERIFIED','source_commit':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),'accepted_base_commit':'cb6642f60a76eaa005d406763367635afca3dc9c','g3_packet_commit':'f1636499b963d3982b2dfff0f2757042b1796d21','modules':1561,'preserved1497':True,'literal_imports_checked':1561,'shared_exact_modules':overlap,'new_modules':64,'scripts':scriptpins,'graph_sha256':sha((out/'DEPENDENCY-GRAPH.json').read_bytes()),'source_bytes':sum(r['bytes'] for r in pins),'new_source_bytes':sum(r['bytes'] for r in pins if r['module'] in new),'compiled_objects_transferred':0,'fresh_aggregate_and_full_audit_required':True}))
save(out/'scripts/assemble_union.py',Path(__file__).read_bytes())
print(json.dumps({'output':str(out),'modules':1561,'overlap':overlap,'new_modules':64,'source_bytes':sum(r['bytes'] for r in pins),'graph_sha256':sha((out/'DEPENDENCY-GRAPH.json').read_bytes())}))
