"""Admit only the predeclared model-matched synthetic fixture after generation."""
import hashlib,json,re,importlib.util
from pathlib import Path
BASE=Path(__file__).resolve().parent
PROJECTOR_PATH=BASE/'project_fixture.py'
PROJECTOR_SHA='2aa59713f21b7e018b23b372984cd5e42afa86cd91ec0b1145f2f78713251cb1'
if hashlib.sha256(PROJECTOR_PATH.read_bytes()).hexdigest()!=PROJECTOR_SHA:raise ValueError('reviewed projector source changed')
SPEC=importlib.util.spec_from_file_location('reviewed_projection',PROJECTOR_PATH);projection=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(projection)
TRUTH={'K':(0.,.0036),'C':(0.,.0098),'L':(0.,.0067),'H':(0.,.0029),'H,L':(.0017,.0016),'C,H,L':(.0018,.00175),'C,H,K,L':(.0019,.0037)}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def admit():
    if sha(PROJECTOR_PATH)!=PROJECTOR_SHA:raise ValueError("reviewed projector source changed")
    sim=BASE/'runs/simulation-seed21001';out=BASE/'runs/projected-seed21001'
    t=json.loads((sim/'TERMINAL.json').read_text());pr=json.loads((out/'PROJECTION.json').read_text())
    if t['status']!='EXECUTION_EXIT_ZERO' or not t['inputs_stable'] or t['settings']['seed']!=21001 or pr['status']!='PROJECTED_AND_VALIDATED':raise ValueError('stages not complete/stable')
    if pr['projector_sha256']!=PROJECTOR_SHA:raise ValueError('projection source changed')
    if t['command']!=['bpp','--simulate','control.ctl'] or t['input_hashes_before']['binary']!='6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e' or sha(sim/'control.ctl')!='dad49392999ddf8a908286d588406fd119e77aac98b48d69b0ffc07665d4e5b8':raise ValueError('simulation model/engine command differs')
    if pr['layout_sha256']!=projection.LAYOUT_SHA or pr['observed_alleles_copied'] is not False:raise ValueError('projection contract mismatch')
    if sha(sim/'TERMINAL.json')!=pr['simulation_terminal_sha256']:raise ValueError('simulation receipt changed')
    inv={x['path']:x['sha256'] for x in t['output_inventory']}
    for name,expected in inv.items():
        if sha(sim/name)!=expected:raise ValueError('generated evidence changed')
    layout_bytes=projection.bounded_bytes(projection.LAYOUT)
    if projection.digest(layout_bytes)!=projection.LAYOUT_SHA:raise ValueError('layout changed')
    data,mapping,stats=projection.project_data(projection.bounded_bytes(sim/'full-synthetic.txt'),projection.bounded_bytes(sim/'full-synthetic.Imap.txt'),json.loads(layout_bytes))
    if (out/'matched-synthetic.txt').read_bytes()!=data or (out/'matched-synthetic.Imap.txt').read_bytes()!=mapping or pr['loci']!=stats:raise ValueError('projection is not exact declared mask/crop')
    for row in pr['output_inventory']:
        if sha(out/row['path'])!=row['sha256']:raise ValueError('projected evidence changed')
    log=(sim/'stdout.log').read_text()
    if 'Substitution model: JC69' not in log:raise ValueError('wrong substitution model')
    observed={}
    for label,tau,theta in re.findall(r'^\d+\s+(\S+)\s+[01 ]+tau = ([.\d]+)\s+theta = ([.\d]+)',log,re.M):
        key=','.join(sorted(label.split(',')))
        if key in observed:raise ValueError('duplicate population identity')
        observed[key]=(float(tau),float(theta))
    if observed!=TRUTH:raise ValueError('runtime demographic truth mismatch')
    expected={pop+'^'+pop.lower()+str(i)+hap for pop,n in projection.COUNTS.items() for i in range(1,n+1) for hap in 'ab'}
    trees=(sim/'full-truth-gene-trees.txt').read_text().splitlines()
    if len(trees)!=5:raise ValueError('full truth genealogy count')
    for tree in trees:
        names=re.findall(r'([KCLH]\^[kclh]\d+[ab]):',tree)
        if len(names)!=64 or set(names)!=expected:raise ValueError('full sampling/phase mismatch')
    return {'schema':'matched-synthetic-runtime-admission-v1','status':'MODEL_MATCHED_SYNTHETIC_FIXTURE_ADMITTED','simulation_terminal_sha256':sha(sim/'TERMINAL.json'),'projection_receipt_sha256':sha(out/'PROJECTION.json'),'projected_alignment_sha256':sha(out/'matched-synthetic.txt'),'projected_map_sha256':sha(out/'matched-synthetic.Imap.txt'),'layout_sha256':projection.LAYOUT_SHA,'truth_population_parameters':{k:{'tau':v[0],'theta':v[1]} for k,v in observed.items()},'full_simulated_gene_copies':64,'loci':stats,'observed_alleles_copied':False,'biological_admission':False,'calibration_claimed':False,'full_genealogy_used_in_inference':False}
if __name__=='__main__':
    result=admit();(BASE/'SYNTHETIC-ADMISSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
