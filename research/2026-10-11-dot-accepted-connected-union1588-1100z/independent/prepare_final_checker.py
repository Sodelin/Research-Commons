from pathlib import Path
O=Path(__file__).parent;s=Path('LOCAL_EVIDENCE/union1585-independent-review-20261011-0925z/check_final.py').read_text()
def sub(a,b):
 global s
 assert a in s,a[:100]
 s=s.replace(a,b)
sub("ROOT=Path('LOCAL_EVIDENCE/connected-union1585-20261011-0910z')", "ROOT=Path('LOCAL_EVIDENCE/connected-union1588-20261011-1049z')\nBASE1585=Path('LOCAL_EVIDENCE/connected-union1585-20261011-0910z')\nPARENT154=Path('LOCAL_EVIDENCE/parent-path-check154-20261011-1021z')")
sub("NEW_MODULES={'G7EncodedMergerSupport','G4ActualCommonPrefixSelector','G4ActualColocatedCompletion','G3FiniteWordLogSignature'}", "NEW_MODULES={'GroupedParentPathCalendar','FirstParentJoin','MixedParentBoundary'}")
sub("==1585", "==1588")
sub("BASE1581,G7,ROOT", "BASE1581,G7,BASE1585,PARENT154,ROOT")
sub("PASS_INDEPENDENT_EXACT_1585_CONTEXT_REVIEW", "PASS_INDEPENDENT_EXACT_1588_CONTEXT_REVIEW")
a=s.index(" initialp=ROOT/");b=s.index(" for n,x in g['modules'].items():",a)
s=s[:a]+" assert GRAPH=='534564494039d127c137a1ec2a9010fd5250a871dead60dc2d5cf48ae1341919'\n"+s[b:]
sub("basegraph=read(BASE1581/'DEPENDENCY-GRAPH.json')", "basegraph=read(BASE1585/'DEPENDENCY-GRAPH.json')")
a=s.index(" base_result=read(");b=s.index(" report=final_check(g,b)",a)
s=s[:a]+''' base_result=read(BASE1585/'.build/runs/20261011T094301.633551Z/targets/current_connected/RESULT.json')
 tp=Path('LOCAL_EVIDENCE/completed1585-audit-transport-20261011-1035z/audit_transport.py');check(tp,'02aed23bbc3d94871e981b1525932fe1cc3a080900b412e0f9a11f4772fb4a6f');sp=importlib.util.spec_from_file_location('explicit_transport',tp);t=importlib.util.module_from_spec(sp);sp.loader.exec_module(t)
 raw=t.read_audit(base_result['audit_receipt']['audit_output']);assert len(raw)==115612308 and digest_bytes(raw)=='763852d35780a7986ec812fbc96b372e4a8dfe7bdf102f8cda513930a53856e5';b={x['name']:x for x in json.loads(raw)['declarations']};del raw;assert len(b)==102014
 ACCEPTED_RECEIPTS={r['module']:r for r in base_result['component_receipts']}
 rr=read(PARENT154/'.build/runs/20261011T104206.717245Z/targets/candidate_parent-path/RESULT.json')
 for r in rr['component_receipts']:
  if r['module'] in NEW_MODULES:ACCEPTED_RECEIPTS[r['module']]=r
 assert len(ACCEPTED_RECEIPTS)==1588
''' + s[b:]
sub(" report=final_check(g,b)", " report=final_check(g,b)\n assert report['fresh_components']==0 and report['authenticated_component_reuse']==1588\n expected_path=Path('LOCAL_EVIDENCE/parent-path154-independent-review-20261011-1024z/EXACT-DECLARATION-COMPARISON.json');check(expected_path,'6fd226a51d39b82212336dd27a07974a5cade75eef291d84da5e593361a98c29');wanted=read(expected_path)['new_names'];actual_new=read(OUT/'EXACT-NEW-DECLARATION-RECORDS.json');assert actual_new==wanted,'new-record equality to reviewed154 requires explicit difference audit'\n assert report['declarations']==102084 and report['theorems']==92445 and report['globally_new_declarations']==70 and report['globally_new_theorems']==59")
(O/'check_final.py').write_text(s);print('Prepared only; no final build acceptance exists yet.')
