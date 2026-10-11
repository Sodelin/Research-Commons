#!/usr/bin/env python3
"""Source/AST/accepted-byte checks only; never runs preparation or helpers."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

REPO=Path('/workspace/Research-Commons')
P=REPO/'research/2026-10-10-codex-lean-rust-parity'

def require(value,reason):
    if not value: raise AssertionError(reason)

def pin(path,expected):
    path=Path(path);raw=path.read_bytes();h=hashlib.sha256(raw).hexdigest();require(h==expected,'pin '+str(path))
    return {'path':str(path),'sha256':h,'bytes':len(raw)}

def assigned(tree,name):
    out=[]
    for node in ast.walk(tree):
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id==name for t in node.targets): out.append(node.value)
    return out

def dump(node): return ast.dump(node,include_attributes=False)

def check():
    parent=pin(P/'lean/scripts/prepare_g6_natural_common_factorization_20261011_v3.py','06c551cc1e9fe218eb3a2f0dc9517ae023293bac059fc07d3c92e3ab5c34c4b7')
    child=pin(P/'lean/scripts/prepare_g6_forest_register_compression_20261011.py','6d0f0dcecfa53f934a82988b1a68bdbf66ee23d5e04ce2a824ebbd48b089ec29')
    basis=pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/NATURAL141-PREPARER-V3-FACADE-STATIC-QC-ATTEMPT1.json','fbc8d2ca0111b2accad87be86b96335e87a36f0f0036dc8782cbb893555c01ee')
    source=pin(P/'design/history/g6-forest-register-static-qc-20261011T0012Z-solver_design_recovery/G6-FOREST-REGISTER-STATIC-QC-ATTEMPT1.json','26f3ceae385ff19ee0be47ca56822baa6f96cd5fdded494f7204796fb672ee5f')
    frozen=pin(P/'lean/proposals/reuse-integration-20261010T2138Z/forest-register-compression/PROPOSAL-FREEZE.json','cd0e36cec18afb38fc07e0ad31b5bbaa68addc5f8e920fac7982093c0c04791e')
    freeze=json.loads(Path(frozen['path']).read_bytes())
    a=ast.parse(Path(parent['path']).read_text());b=ast.parse(Path(child['path']).read_text())
    fa={n.name:n for n in a.body if isinstance(n,ast.FunctionDef)};fb={n.name:n for n in b.body if isinstance(n,ast.FunctionDef)}
    require(set(fa)==set(fb)=={'allocated','link','main'},'same preparation function inventory')
    require(all(dump(fa[n])==dump(fb[n]) for n in ['allocated','link']),'inode accounting and exclusive/hash-checked transport methods identical')
    for name in ['ROOT','REPOSITORY','PARENT','ARM','STORAGE','STORAGE_SHA','CORE','AUDIT','OVERLAY','AUTH','GUARD','LAUNCHER','LAUNCHER_SHA','reserves','policy','budget','equivalence']:
        aa=assigned(a,name);bb=assigned(b,name)
        require(len(aa)==len(bb)==1 and dump(aa[0])==dump(bb[0]),'unchanged policy/source/parent AST '+name)
    before_a=[ast.literal_eval(n) for n in assigned(a,'before')];before_b=[ast.literal_eval(n) for n in assigned(b,'before')]
    after_a=[ast.literal_eval(n) for n in assigned(a,'after')];after_b=[ast.literal_eval(n) for n in assigned(b,'after')]
    require(before_a==before_b and len(after_a)==len(after_b)==3,'same exact helper replacement entry points')
    for i in [0,1]:
        expected=after_a[i]
        for old,new in [(145,104),(143,103),(2,1)]: expected=re.sub(r'\b'+str(old)+r'\b',str(new),expected)
        require(expected==after_b[i],'seeder/installer only104/103/1 coverage substitution')
    require(after_a[2]==after_b[2],'same prelaunch storage/source gate insertion')
    text=Path(child['path']).read_text()
    require("choices=['forest']" in text and "'phases':{'forest':{'target':label,'requires':[]}}" in text,'forest phase label matches actual guard/plan')
    require("['rc-lean-g6-natural-common-*','rc-lean-g6-forest-register-*']" in text and "gate.get('byte_trial_allocation_roots',[])" in text,'all natural/forest/support contexts counted')
    require("prep['additional_storage_input_pins']['source_static_QC']" in text and source['sha256'] in text,'actual proposal QC pin carried into prelaunch inputs')
    calls=[n for n in ast.walk(b) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess']
    require(len(calls)==1 and calls[0].func.attr=='run' and "['seed_forest_register_cache.py','prepare_forest_register_install.py']" in text,'only two metadata helper calls; no compiler launch in preparer')
    for phrase in ["set(protected)&set(modules)=={'Mathlib.Analysis.Convex.Caratheodory'}", "len(guard_only)==3 and len(staging_order)==104", "len(cache_by_module)==103", "len(order)==len(modules)==101", "len(fresh)==1"]:
        require(phrase in text,'exact forest count/overlap assertion '+phrase)
    cert_pin=pin(P/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json','1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2')
    root_pin=pin(P/'quality/HISTORY-SURVIVAL-UNION-1504-REVIEW-20261010T224327.307430Z.json','e10e65a37003efcd1c9dce3d7cb80a154b034f66bb8dd740ee061f9e35bc33cb')
    cert=json.loads(Path(cert_pin['path']).read_bytes());providers=freeze['graph']['providers'];pins=[];graph={}
    require(len(providers)==len({r['module'] for r in providers})==100,'100 unique accepted providers')
    for row in providers:
        item=pin(REPO/row['path'],row['sha256']);item['module']=row['module'];pins.append(item)
        require(row['sha256']==cert['source_pins'][row['module']],'accepted1504 source identity')
        imports=re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',Path(item['path']).read_text(),re.M)
        require(imports==row['imports'],'literal accepted provider imports');graph[row['module']]=imports
    row=freeze['source'];fresh_pin=pin(REPO/row['immutable_version'],row['sha256'])
    require(fresh_pin['sha256']=='2fc15e1e16f8aa5742b06e08473ab22df896e485b6df48d70e3ed703056e123a','exact reviewed forest source')
    pin(REPO/row['path'],row['sha256']);graph[freeze['module']]=row['imports']
    require(re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',Path(fresh_pin['path']).read_text(),re.M)==row['imports'],'new literal imports')
    reached=set()
    def visit(name):
        if name in reached:return
        reached.add(name)
        for dep in graph[name]:
            if dep in graph:visit(dep)
    visit(freeze['module']);require(reached==set(graph) and len(reached)==101,'independent reachable101 source closure')
    require('Mathlib.Analysis.Convex.Caratheodory' in reached,'Caratheodory already executes in101')
    plan=pin(REPO/freeze['provider_plan']['path'],freeze['provider_plan']['sha256'])
    guard=pin(P/'lean/scripts/guard_g7_survival_run_20261010_v2.py','4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4')
    projected=Path(guard['path']).read_text()
    require(projected.count(before_b[2])==1,'exact guard storage insertion')
    projected=projected.replace("choices=['primary', 'secondary', 'union1503', 'union1504']","choices=['forest']",1).replace(before_b[2],after_b[2],1)
    guard_sha=hashlib.sha256(projected.encode()).hexdigest()
    return {'status':'PASS_STATIC_FOREST101_PREPARER_SOURCE_IMPORT_GRAPH_GUARD_AND_STORAGE_SCOPE_ONLY',
        'parent_preparer':parent,'new_preparer':child,'prior_preparer_qc':basis,'forest_source_qc':source,'frozen_proposal':frozen,
        'accepted_certificate':cert_pin,'accepted_root_review':root_pin,'provider_plan':plan,'fresh_source':fresh_pin,'provider_source_pins':pins,
        'independent_closure':{'executable':101,'accepted1504_parents':100,'fresh':1,'warm_staging':103,'total_staging':104,'protected_records':4,'guard_only':3,'Caratheodory_inside_executable_closure':True},
        'unchanged_AST_blocks':['allocated/link','all canonical core/parent/storage/facade pins','reserves/policy/budget','full post-installer parent source equivalence record','prelaunch storage/source input insertion'],
        'new_guard_source_sha256_from_static_literal_reconstruction':guard_sha,
        'qualifications':['Preparation source only; no helper, installer, seeder, guard, Builder, compiler or target module was imported/executed by this reader.',
            '101 selected executable modules and104 staging records are configured counts, not executed mathematical results. Actual new context/pins/resource measurement require their own root gate.',
            'Protected Caratheodory is one of100 accepted parents and already in101; only the other3 protected records are nonexecuted namespace guards. All4 guard policies remain enforced.',
            'Preparation invokes only two metadata helpers. Core/helper method bodies, actual4GiB180s narrow caps, connected6GiB300s label policy,76MiB reserve/2GiB scratch/15GiB memory and create-new/hash/alias semantics remain those of the reviewed parent.',
            'The metadata guard_changes wording retains natural phase text, while the executable guard/plan phase is explicitly forest; source pins and actual phase fields determine this gate.',
            'Full-forest/register quotient-generator fibre equality remains scoped to source support/CoLocated/liveCard and supplied rational checker conditions. No count-conditioned chain, positive physical graph factor, G4 scalar word product/calibrated decoder, native refinement or master closure is inferred.']}

def main():
    report={'schema':'forest101_preparer_independent_static_qc_v1','contributor':'Codex / solver_design_recovery',
        'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'target_imports_or_producers_started':0,'mathematical_acceptance_changed':False}
    try:report.update(check())
    except Exception as e:report.update(status='FAIL_STATIC_QC',error_type=type(e).__name__,error=str(e))
    out=Path(sys.argv[1])
    with out.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'status':report['status'],'path':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))
    return 1 if report['status']=='FAIL_STATIC_QC' else 0

if __name__=='__main__':raise SystemExit(main())
