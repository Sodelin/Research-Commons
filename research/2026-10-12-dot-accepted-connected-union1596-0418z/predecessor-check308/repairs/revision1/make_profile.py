from pathlib import Path
import hashlib,json,re,difflib
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=Path(__file__).resolve().parent
old=Path('LOCAL_EVIDENCE/entrance294-budget-proposal-20261012-0247z')
base=Path('LOCAL_EVIDENCE/connected-union1595-20261012-0342z')
out=Path('LOCAL_EVIDENCE/scaling308-budget-proposal-20261012-0354z');out.mkdir(exist_ok=False)
ledger=json.loads((src/'DEPENDENCY-LEDGER.json').read_text());rows={r['module']:r for r in ledger['providers']};name='G4ActualFirstMeetingExposureScaling';target='candidate/g4-first-meeting-exposure-scaling';sh=ledger['source_sha256'];rows[name]={'module':name,'sha256':sh,'imports':ledger['imports']}
g={'targets':{target:{'roots':[name],'order':[r['module'] for r in ledger['providers']]+[name],'modules':rows,'external_imports':sorted({i for r in rows.values() for i in r['imports'] if i not in rows})}},'scope':'Separate 308-module candidate: same-bank cross-arity exposure scaling and original scaled comb mass; no strict positivity or natural averaging.'}
(out/'DEPENDENCY-GRAPH.json').write_text(json.dumps(g,indent=2)+'\n');gh=h(out/'DEPENDENCY-GRAPH.json')
replacements={'entrance294':'scaling308','ENTRANCE294':'SCALING308','G4ActualFirstMeetingEntrance':name,'candidate/g4-first-meeting-entrance':target,'Connected_candidate_g4-first-meeting-entrance':'Connected_candidate_g4-first-meeting-exposure-scaling','78ef6a06d2b4ed61dd9b0d790a0c3a9e5256d5b7c5a0cbf08e299818631a041c':gh,'a18142c052a500a664050a0f4cef665fe81171ee59bb73a926dc2b19f26dd43f':sh,'len(mods)==294':'len(mods)==308','Separate exact183 target':'Separate exact308 target','Mathlib183 graph':'Mathlib308 graph'}
for filename in ['build_entrance294.py','run_entrance294.py','run_current.py']:
 text=(old/filename).read_text()
 for a,b in replacements.items():text=text.replace(a,b)
 newname=filename.replace('entrance294','scaling308');(out/newname).write_text(text)
 (out/(newname+'.diff')).write_text(''.join(difflib.unified_diff((old/filename).read_text().splitlines(True),text.splitlines(True),fromfile=filename,tofile=newname)))
p=(old/'prepare_entrance294.py').read_text()
for a,b in replacements.items():p=p.replace(a,b)
p=p.replace('LOCAL_EVIDENCE/connected-union1593-20261012-0003z',str(base)).replace('LOCAL_EVIDENCE/g4-cut-entrance-reuse-20261012-0243z/revision1',str(src)).replace('len(cache)==293','len(cache)==307').replace('all293','all307').replace("'selected_count':294,'reuse_count':293","'selected_count':308,'reuse_count':307")
p=re.sub(r'^EXPECTED_SCRIPTS=.*$', 'EXPECTED_SCRIPTS='+repr({n:h(base/'scripts'/n) for n in ['build_desktop.py','build_with_authenticated_overlay.py','build_with_mathlib_overlay.py','build_connected.py','completed_trace_transport.py','build_streamed_audit.py','audit_stream.py','AuditTemplate.lean']} | {n:h(out/n) for n in ['run_scaling308.py','build_scaling308.py','run_current.py']}),p,flags=re.M)
(out/'prepare_scaling308.py').write_text(p)
(out/'prepare_scaling308.py.diff').write_text(''.join(difflib.unified_diff((old/'prepare_entrance294.py').read_text().splitlines(True),p.splitlines(True),fromfile='prepare_entrance294.py',tofile='prepare_scaling308.py')))
cache=[]
for f in (base/'.build/cache').glob('*/receipt.json'):
 d=json.loads(f.read_text());n=d.get('module')
 if n in rows and n!=name and d.get('source_sha256')==rows[n]['sha256']:
  cache.append({'module':n,'key':f.parent.name,'receipt_sha256':h(f),'allocated_bytes':sum(x.stat().st_blocks*512 for x in f.parent.iterdir())})
assert len(cache)==307 and len({r['module'] for r in cache})==307
(out/'MEASURED-INPUTS.json').write_text(json.dumps({'accepted_contexts':307,'cache_path_allocated_bytes':sum(r['allocated_bytes'] for r in cache),'cache_rows':cache},indent=2)+'\n')
print(out,gh,h(out/'prepare_scaling308.py'))
