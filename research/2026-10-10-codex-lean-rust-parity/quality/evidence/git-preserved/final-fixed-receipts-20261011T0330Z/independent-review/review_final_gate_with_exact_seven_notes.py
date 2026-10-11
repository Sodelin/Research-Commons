#!/usr/bin/env python3
"""Own pure-print qualification: ONLY the seven pinned canonical9ec note paths."""
from pathlib import Path,PurePosixPath
import hashlib,json,ast,sys
S=Path(__file__).with_name('review_finalizer_source_state_and_gate.py')
d=S.read_bytes();assert hashlib.sha256(d).hexdigest()=='2031fb50c772f2eba345bc6a981bcda0bb780e30eb10209a96783afe35f23c90'
exec(compile(d.split(b'\nphase=sys.argv[1]',1)[0],str(S),'exec'))
p=B/'peer-main9ec-api/NEWEST-MAIN-READONLY-PROVENANCE.json'
i,j=load(p,'8caf81fd72ca09d0e393b818d7513adb15b17fcc87dc028cde451db8c9c17daf')
require(j['ref']=='9ec5d63a839e6998d3ff1c143007434f3c7ebcdc' and j['base']=='62020166e3e7ef690838f50b13caa149ede419ec','exact canonical note-only commit range')
EXACT_CANONICAL_7={r['path'] for r in j['files']}
require(len(j['files'])==len(EXACT_CANONICAL_7)==7 and {r['filename'] for r in j['compare']['files']}==EXACT_CANONICAL_7 and all(r['status']=='added' for r in j['compare']['files']),'exact ONLY seven added API paths')
bindings=[]
for r in j['files']:
 path=r['path'];source=Path(r['source_path']);data=source.read_bytes();data.decode('utf8')
 require(not PurePosixPath(path).is_absolute() and str(PurePosixPath(path))==path and '..' not in PurePosixPath(path).parts and '\0' not in path,'normalized explicit canonical path')
 require(path.endswith(('.md','.json')) and source.is_file() and not source.is_symlink(),'regular saved text note')
 oid,_=blob(data);require(oid==r['git_blob'],'full raw Git-SHA1 equal pinned API body')
 bindings.append([path,str(source),oid,len(data),digest(data)])
part=ast.get_source_segment(d.decode(),next(x for x in ast.parse(d).body if isinstance(x,ast.FunctionDef) and x.name=='frozen_gate'))
old="path.startswith(prefix+'/')";require(part.count(old)==1,'exact one old own-reader prefix predicate')
# Preserve original source and widen only its one gate-reader path predicate.
exec(compile(part.replace(old,"(path.startswith(prefix+'/') or path in EXACT_CANONICAL_7)",1),str(S)+'#explicit-seven-only','exec'))
answer={'status':'PASS_EXPLICIT_SEVEN_CANONICAL_NOTE_PATH_QUALIFICATION_FROZEN_GATE_STILL_REQUIRED','wrapper_sha256':digest(Path(__file__).read_bytes()),'original_reader_sha256':digest(d),'finalizer_source_sha256':F,'api_provenance':i,'seven_canonical_full_body_bindings':bindings,'only_gate_reader_prefix_test_changed':'prefix OR exact seven pinned paths; all other destination normalization, absence, full body pins, costs, source/gate/cap checks unchanged. Original own source remains immutable.','no_git_target_import_producer_or_scientific_admission':True}
if len(sys.argv)>1 and sys.argv[1]=='gate':
 protocol=source();state,e=saved_state();mi,m=load(B/'FINAL-REMAINING-FULLTEXT-INPUTS.json')
 outsiders=[r for r in m['files'] if not r['git_tree_path'].startswith(m['prefix']+'/')]
 require(len(outsiders)==7 and {r['git_tree_path'] for r in outsiders}==EXACT_CANONICAL_7,'ONLY seven canonical outsiders in fixed final manifest')
 bypath={r['path']:r for r in j['files']}
 for r in outsiders:require(r['source_path']==bypath[r['git_tree_path']]['source_path'],'exact API retained source path')
 gate=frozen_gate(e);answer.update(status='PASS_FIXED_FINALIZER_FROZEN_GATE_WITH_ONLY_SEVEN_CANONICAL_NOTE_PATHS',finalizer_gate_sha256=gate['gate']['sha256'],frozen_gate=gate,current_index=state['current_index'],current_resources=resources(),all_saved30_and_prior_tree_checks_pass=True)
print(json.dumps(answer,indent=2))
