#!/usr/bin/env python3
"""Static AST-only whole-preparer equality; no target import or execution."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

P=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
OLD='e3391d165f5f3253a6de2876544ac6568dca3013cbc5d294a6cd55c9a4f39b41'
NEW='54f1dc3e7326f13b51ddb7427e8fa97bf9908f3dcc6073e5dc2f7e98ef33a230'

def require(value, reason):
    if not value: raise AssertionError(reason)

def pin(path, expected):
    path=Path(path); raw=path.read_bytes(); h=hashlib.sha256(raw).hexdigest()
    require(h==expected,'pin '+str(path))
    return {'path':str(path),'sha256':h,'bytes':len(raw)}

def check():
    parent=pin(P/'lean/scripts/prepare_g6_natural_common_factorization_20261011_v5.py','b0e1bd54657d03056e07dc99cdb8f9cc9d16673f5fd57c4211039ca7d9afc72a')
    child=pin(P/'lean/scripts/prepare_g6_natural_common_factorization_20261011_v6.py','cd1e353ab5baf9b4bee444c78837e6d5769a4a11d95d40236a08d054467f4b19')
    basis=pin(P/'design/history/g6-natural-prefix-second-repair-static-qc-20261011T0031Z-solver_design_recovery/A227-REPAIR-V5-PREPARER-STATIC-QC-ATTEMPT2.json','f9cb832971a6e47c96cb26e6729cb10f65c437373c54d8fb5b86fdca27d75df4')
    source=pin(Path(__file__).with_name('A080-FINAL-REPAIR-SOURCE-STATIC-QC-ATTEMPT1.json'),'9c37a0628ddf31b35d3621115abaf92e349125cc1c3359c3f21e1f90e7e1efbf')
    freeze=pin(P/'lean/proposals/reuse-integration-20261010T2138Z/natural-common-factorization/PROPOSAL-FREEZE-V5.json',NEW)
    old_ast=ast.parse(Path(parent['path']).read_text()); new_ast=ast.parse(Path(child['path']).read_text())
    counts=[0,0]; lineages=[]
    class Normalize(ast.NodeTransformer):
        def visit_Constant(self,node):
            if node.value=='proposals/reuse-integration-20261010T2138Z/natural-common-factorization/PROPOSAL-FREEZE-V5.json':
                counts[0]+=1; return ast.copy_location(ast.Constant(value='proposals/reuse-integration-20261010T2138Z/natural-common-factorization/PROPOSAL-FREEZE-V4.json'),node)
            if node.value==NEW:
                counts[1]+=1; return ast.copy_location(ast.Constant(value=OLD),node)
            return node
        def visit_Dict(self,node):
            node=self.generic_visit(node)
            for i,key in reversed(list(enumerate(node.keys))):
                if isinstance(key,ast.Constant) and key.value=='source_repair_derivation':
                    lineages.append(ast.literal_eval(node.values[i]));node.keys.pop(i);node.values.pop(i)
            return node
    a=Normalize().visit(new_ast); b=Normalize().visit(old_ast)
    require(counts==[1,1] and len(lineages)==2,'exact new path/SHA and old/new inert metadata')
    require(ast.dump(a,include_attributes=False)==ast.dump(b,include_attributes=False),'every other executable AST node identical')
    current,previous=lineages
    require(current['prior_preparer_sha256']==parent['sha256'] and current['prior_workspace']=='/dev/shm/rc-lean-g6-natural-common-20261011T002733.947509Z','exact previous context/preparer')
    require(current['failed_source_sha256']=='a2275917b1a844e7b12c5198419f17f51646ff5ac84fee435e0c90f1b129eca3' and current['proof_only_repair_sha256']=='a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917','exact failed/repaired source lineage')
    return {'status':'PASS_STATIC_V6_PREPARER_WHOLE_AST_EQUIVALENCE_EXCEPT_FROZEN_SOURCE_AND_LINEAGE',
        'parent':parent,'new_preparer':child,'prior_source_preparer_qc':basis,'new_source_qc':source,'frozen_proposal':freeze,
        'exact_difference':{'freeze_path_literal':1,'freeze_SHA_literal':1,'new_inert_lineage':current,'old_inert_lineage':previous,'all_other_AST_nodes_identical':True},
        'unchanged':['141 executable/145 staged/143 reused/2 new source topology','four protected guard records','canonical core/storage/same-core facade/parent-equivalence checks','native/import/kernel/audit predicates','4GiB180s actual narrow caps and connected6GiB300s separate policy','76MiB reserve/2GiB scratch/15GiB nonreclaimable guard','all prior context and byte-support allocation policies'],
        'qualification':['Source-only gate. No preparer, helper, seeder, installer, target module or compiler was imported or executed here.',
            'The approved caller must supply the absolute capture gate; actual preparation/source/cache/parent pins and dated resource budget require separate saved review before root-approved mathematical launch.',
            'No proof goal closure, audit ownership, coherent1504 widening or runtime/application promotion is inferred.']}

def main():
    report={'schema':'natural141_v6_preparer_independent_static_qc_v1','contributor':'Codex / solver_design_recovery',
        'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'target_imports_or_producers_started':0,'accepted_mathematical_evidence_changed':False}
    try: report.update(check())
    except Exception as e: report.update(status='FAIL_STATIC_QC',error_type=type(e).__name__,error=str(e))
    out=Path(sys.argv[1])
    with out.open('x') as f: json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'status':report['status'],'path':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))
    return 1 if report['status']=='FAIL_STATIC_QC' else 0

if __name__=='__main__': raise SystemExit(main())
