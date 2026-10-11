#!/usr/bin/env python3
"""Own pure-print qualification: ONLY the seven pinned canonical9ec note paths."""
from pathlib import Path,PurePosixPath
import hashlib,json,ast,sys
S=Path(__file__).parents[3]/'design-qc/final-fixed-late-publication-20261011T0320Z-solver_design_recovery/review_finalizer_source_state_and_gate.py'
d=S.read_bytes();assert hashlib.sha256(d).hexdigest()=='2031fb50c772f2eba345bc6a981bcda0bb780e30eb10209a96783afe35f23c90'
exec(compile(d.split(b'\nphase=sys.argv[1]',1)[0],str(S),'exec'))
p=B/'peer-main9ec-api/NEWEST-MAIN-READONLY-PROVENANCE.json'
pin(B/'FINAL-REMAINING-FULLTEXT-INPUTS.json','a0519b052c9ec6c0433bf6ebb0f9bb1318b37d7fc6dc56b284f3991fe63dddf7')
pin(B/'FINAL-REMAINING-FIXED-RESERVE-GATE.json','7b827fd1c0617e6aecf8f4ef526d0cf05ff09613d9396348e61b5bba678740a7')
i,j=load(p,'8caf81fd72ca09d0e393b818d7513adb15b17fcc87dc028cde451db8c9c17daf')
require(j['ref']=='9ec5d63a839e6998d3ff1c143007434f3c7ebcdc' and j['base']=='62020166e3e7ef690838f50b13caa149ede419ec','exact canonical note-only commit range')
EXACT_CANONICAL_7={r['path'] for r in j['files']}
require(len(j['files'])==len(EXACT_CANONICAL_7)==7 and {r['filename'] for r in j['compare']['files']}==EXACT_CANONICAL_7 and all(r['status']=='added' for r in j['compare']['files']),'exact ONLY seven added API paths')
bindings=[]
for r in j['files']:
 path=r['path'];saved_note=Path(r['source_path']);data=saved_note.read_bytes();data.decode('utf8')
 require(not PurePosixPath(path).is_absolute() and str(PurePosixPath(path))==path and '..' not in PurePosixPath(path).parts and '\0' not in path,'normalized explicit canonical path')
 require(path.endswith(('.md','.json')) and saved_note.is_file() and not saved_note.is_symlink(),'regular saved text note')
 oid,_=blob(data);require(oid==r['git_blob'],'full raw Git-SHA1 equal pinned API body')
 bindings.append([path,str(saved_note),oid,len(data),digest(data)])
part=ast.get_source_segment(d.decode(),next(x for x in ast.parse(d).body if isinstance(x,ast.FunctionDef) and x.name=='frozen_gate'))
old="path.startswith(prefix+'/')";require(part.count(old)==1,'exact one old own-reader prefix predicate')
ns='latest1570-handoff-20261011T0245Z';require(part.count(ns)==1,'old own namespace assumption');part=part.replace(ns,'final-fixed-receipts-20261011T0330Z',1)
# Preserve original source and widen only its one gate-reader path predicate.
exec(compile(part.replace(old,"(path.startswith(prefix+'/') or path in EXACT_CANONICAL_7)",1),str(S)+'#explicit-seven-only','exec'))
answer={'status':'PASS_EXPLICIT_SEVEN_CANONICAL_NOTE_PATH_QUALIFICATION_FROZEN_GATE_STILL_REQUIRED','wrapper_sha256':digest(Path(__file__).read_bytes()),'original_reader_sha256':digest(d),'finalizer_source_sha256':F,'api_provenance':i,'seven_canonical_full_body_bindings':bindings,'only_gate_reader_prefix_test_changed':'Exact a0510330 namespace equality plus ONLY seven pinned canonical paths. Other destination/full-body/absence/index/cost/cap predicates unchanged; original own sources immutable.','no_git_target_import_producer_or_scientific_admission':True}
if len(sys.argv)>1 and sys.argv[1]=='gate':
 protocol=source();state,e=saved_state();mi,m=load(B/'FINAL-REMAINING-FULLTEXT-INPUTS.json')
 outsiders=[r for r in m['files'] if not r['git_tree_path'].startswith(m['prefix']+'/')]
 require(len(outsiders)==7 and {r['git_tree_path'] for r in outsiders}==EXACT_CANONICAL_7,'ONLY seven canonical outsiders in fixed final manifest')
 bypath={r['path']:r for r in j['files']}
 for r in outsiders:require(r['source_path']==bypath[r['git_tree_path']]['source_path'],'exact API retained source path')
 gate=frozen_gate(e);answer.update(status='PASS_FIXED_FINALIZER_FROZEN_GATE_WITH_ONLY_SEVEN_CANONICAL_NOTE_PATHS',finalizer_gate_sha256=gate['gate']['sha256'],frozen_gate=gate,current_index=state['current_index'],current_resources=resources(),all_saved30_and_prior_tree_checks_pass=True)
print(json.dumps(answer,indent=2))
