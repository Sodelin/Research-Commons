#!/usr/bin/env python3
"""Inspect frozen Lean source/providers only; no Lean or producer is launched."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

REPO=Path('/workspace/Research-Commons')
P=REPO/'research/2026-10-10-codex-lean-rust-parity'
B=P/'lean/proposals/reuse-integration-20261010T2138Z/forest-register-compression'

def require(value,label):
    if not value: raise AssertionError(label)

def pin(path,digest):
    path=Path(path); raw=path.read_bytes(); require(hashlib.sha256(raw).hexdigest()==digest,'pin '+str(path))
    return {'path':str(path),'bytes':len(raw),'sha256':digest}

def imports(source):
    return re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',source,re.M)

def check():
    freeze_pin=pin(B/'PROPOSAL-FREEZE.json','cd0e36cec18afb38fc07e0ad31b5bbaa68addc5f8e920fac7982093c0c04791e')
    freeze=json.loads((B/'PROPOSAL-FREEZE.json').read_bytes()); row=freeze['source']
    source_pins=[pin(REPO/row['path'],row['sha256']),pin(REPO/row['immutable_version'],row['sha256'])]
    require(row['sha256']=='2fc15e1e16f8aa5742b06e08473ab22df896e485b6df48d70e3ed703056e123a' and
            all(v==0 for v in freeze['actual_calls'].values()),'uncompiled frozen source scope')
    source=(REPO/row['path']).read_text(); require(imports(source)==row['imports'],'root exact literal imports')
    certificate_pin=pin(P/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json','1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2')
    accepted=json.loads(Path(certificate_pin['path']).read_bytes())['source_pins']
    graph=freeze['graph']; providers=graph['providers']; provider_pins=[]; module_imports={freeze['module']:row['imports']}
    require(graph['exact_accepted_parent_modules']==len(providers)==100 and graph['new_source_roots']==1 and graph['actual_source_closure']==101,
            '100 parents plus1 new')
    for provider in providers:
        require(provider['module'] not in module_imports and accepted[provider['module']]==provider['sha256'],'unique exact accepted1504 provider '+provider['module'])
        provider_pins.append(pin(provider['path'],provider['sha256']))
        require(imports(Path(provider['path']).read_text())==provider['imports'],'provider public/plain literal imports '+provider['module'])
        module_imports[provider['module']]=provider['imports']
    order=[]; active=set(); seen=set(); external=set()
    def visit(module):
        if module not in module_imports:
            external.add(module); return
        require(module not in active,'acyclic graph '+module)
        if module in seen:return
        active.add(module)
        for dependency in module_imports[module]:visit(dependency)
        active.remove(module);seen.add(module);order.append(module)
    visit(freeze['module'])
    require(len(seen)==101 and seen==set(module_imports) and external==set(graph['protected_external_imports']), 'exact reachable closure and external imports')
    heads=[]; lines=source.splitlines()
    for header in row['heads']:
        remainder='\n'.join(lines[header['line']-1:]); boundary=remainder.index(':=')
        actual=remainder[:boundary].strip()
        require(actual==header['header'] and hashlib.sha256(actual.encode()).hexdigest()==header['header_sha256'],'literal header '+header['name'])
        heads.append({'name':header['name'],'line':header['line'],'header_sha256':header['header_sha256']})
    authored=re.findall(r'^(?:noncomputable )?(?:def|theorem)\s+([A-Za-z_][A-Za-z0-9_]*)',source,re.M)
    require(authored==[r['name'] for r in row['heads']] and len(authored)==7,'exact seven authored public heads')
    require(len(re.findall(r'^theorem ',source,re.M))==4 and len(re.findall(r'^noncomputable def ',source,re.M))==3,'4 public theorems/3 definitions')
    require(not re.search(r'^(?:axiom|opaque)\b|\bsorry\b|\badmit\b|native_decide|debug\.skipKernelTC',source,re.M),'no skipped/admitted new proof')
    for text in ['{Obs : Type*} [DecidableEq Obs]', '∑ d : Code N sample,',
                 '((state d).register,rootForest N d)', 'exact original_population_compression M hM z alpha atom beta hz hmass htail',
                 '(hs : CoLocated N s i) (hcap : liveCard s ≤ M)', 'r ≤ M - 1',
                 'positive_tail_compression M hM z alpha halpha', 'checked_real_moments M z alpha atom beta h']:
        require(text in source,'actual source/premise/provider role '+text)
    require('[Fintype Obs]' not in source and '[Fintype (UnrankedTree' not in source and '[Fintype (Finset' not in source,'no ambient finite forest/reader premise')
    existential=source[source.index('theorem exists_uniform_original_forest_register_compression'):source.index('theorem checked_original_forest_register_compression')]
    require(existential.index('∃ atom : Fin r → Fin n') < existential.index('∀ (N : RootedBinary V E X)') < existential.index('∀ (register : V → Bool)'),
            'one atom list precedes every source/row/output')
    guard_in_closure=[n for n in seen if n.startswith('Mathlib.')]
    require(guard_in_closure==['Mathlib.Analysis.Convex.Caratheodory'],'one protected accepted provider already executed in actual closure')
    outline_pin=pin(REPO/freeze['provider_plan']['path'],freeze['provider_plan']['sha256'])
    return {'status':'PASS_FROZEN_SOURCE_SCOPE_100_ACCEPTED_PARENTS_PLUS_ONE_NEW_ROOT_ONLY',
            'freeze':freeze_pin,'source_pins':source_pins,'accepted1504_certificate':certificate_pin,'accepted_provider_pins':provider_pins,
            'literal_public_heads':heads,'public_head_count':7,'public_theorems':4,'public_definitions':3,'topological_owned_modules':order,
            'external_imports':sorted(external),'guard_provider_already_in_executed_closure':guard_in_closure,'provider_outline':outline_pin,
            'checked_properties':['full original finite Code destination equality is summed over one fixed readout fibre, with finite sums interchanged',
                'concrete readout retains the entire original vertex register and full rooted labelled unranked forest including all carried descendant subtrees',
                'all-copy CoLocated at one actual population and current liveCard≤M remain explicit for every row',
                'one supplied mass/tail or one positive selected original-atom certificate precedes every source/entering row/forest/register output',
                'reader/forest alphabet need not be Fintype; only original Code is summed',
                'existing positive_tail_compression and executable rational checked_real_moments are reused; no new extractor/count/minpoly engine'],
            'qualifications':['Static Lean source/import/header review only; no compiler, kernel, audit, checker or runtime was invoked. Actual accepted heads/generated ownership/axioms remain pending a sole-scheduler receipt.',
                'This transfers quotient-generator fibre equality, not a probability factor, sharp count-conditioned R_M theorem, semigroup/runtime refinement or legal positive biological graph construction.',
                'Uniform atom choice retains positivity premises and the zero-total-mass empty-list case from its accepted parent.',
                'Natural private-seed averaging, proper exterior panels/current-root grafting, physical exit/future contexts, bin/calibrated observational decoders and arbitrary full FKey contracts remain separate exact interfaces.',
                'The G4 full extracted-word scalar product still needs actual_no_loss_append reachable no-loss row-constant hq for each actual word/cohort; this quotient reader transfer does not supply it.',
                'The101 executed closure already contains the accepted Caratheodory guard provider. Under the four-guard namespace policy, staging adds only the other three (104 total); no guard may be counted twice.',
                'Natural141 remains the next actual proof slot. This separate proposal does not widen accepted1504 or establish a coherent prospective union/master result.']}

def main():
    report={'schema':'g6_original_forest_register_independent_static_design_qc_v1','contributor':'Codex / solver_design_recovery',
            'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'producer_compiler_native_adapter_reference_processes_started':0,'mathematical_acceptance_modified':False}
    try: report.update(check())
    except Exception as error: report.update(status='FAIL_STATIC_QC',error_type=type(error).__name__,error=str(error))
    path=Path(sys.argv[1])
    with path.open('x') as handle:json.dump(report,handle,indent=2,sort_keys=True);handle.write('\n')
    print(json.dumps({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'status':report['status']}))

if __name__=='__main__':main()
