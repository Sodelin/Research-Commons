"""Full authenticated matched pair, descriptive diagnostics and fixed-truth facts only."""
import hashlib,importlib.util,json,re
from pathlib import Path
BASE=Path(__file__).resolve().parent
NAMES=['A00-matched-recovery-seed21101','A00-matched-second-seed21102']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name,expected):
    p=BASE/(name+'.py')
    if sha(p)!=expected:raise ValueError('changed reviewed helper: '+name)
    spec=importlib.util.spec_from_file_location(name,p);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def truth_facts(reports,truth):
    values={'theta_'+k:truth[k]['theta'] for k in ['K','C','L','H']};values['root_tau']=truth['C,H,K,L']['tau']
    return {key:{'declared_fixed_truth':value,'chain_intervals_025_975':[[r['scalars']['columns'][key]['quantiles_025_50_975'][j] for j in [0,2]] for r in reports],'truth_in_interval':[r['scalars']['columns'][key]['quantiles_025_50_975'][0]<=value<=r['scalars']['columns'][key]['quantiles_025_50_975'][2] for r in reports]} for key,value in values.items()}

def main():
    summary=load('summarize_matched','fc1458faa22872548306eff7a8f0020614ac11b043cdc17716c1fb70db941c7d')
    compare=load('compare_matched','a85a052a9377da91e2a07c6e9aea61a0cfc2041cf347bd92b679e617390bf41d')
    admission=BASE/'SYNTHETIC-ADMISSION.json'
    if sha(admission)!='2c8c0685ac8c30b832cf8c23211c36c3c73a48256c1acdd1098e17da9e71d3ca':raise ValueError('truth admission changed')
    terminals=[json.loads((BASE/'runs'/name/'TERMINAL.json').read_text()) for name in NAMES]
    a,b=terminals
    if [t['settings']['seed'] for t in terminals]!=[21101,21102]:raise ValueError('unexpected seeds')
    if {k:v for k,v in a['settings'].items() if k!='seed'}!={k:v for k,v in b['settings'].items() if k!='seed'}:raise ValueError('different target settings')
    for key in ['binary','watchdog','projector','admission','alignment','map']:
        if a['input_hashes_before'][key]!=b['input_hashes_before'][key]:raise ValueError('different target input')
    for name,t in zip(NAMES,terminals):
        ctl=(BASE/'runs'/name/'control.ctl').read_bytes()
        if hashlib.sha256(ctl).hexdigest()!=t['input_hashes_before']['control']:raise ValueError('control changed')
        norm,n=re.subn(rb'(?m)^seed = '+str(t['settings']['seed']).encode()+rb'$',b'seed = 21101',ctl)
        if n!=1 or hashlib.sha256(norm).hexdigest()!='e653b2a121d85d5cde534de9d18373319e9a7459879ddccedcfc660d18485098':raise ValueError('control differs beyond seed')
    reports=[summary.summarize(name) for name in NAMES]
    out={'schema':'matched-completed-pair-v1','runs':reports,'terminal_sha256':[sha(BASE/'runs'/name/'TERMINAL.json') for name in NAMES],'summarizer_sha256':sha(BASE/'summarize_matched.py'),'comparison_source_sha256':sha(BASE/'compare_matched.py'),'admission_sha256':sha(admission),'pair_comparison':compare.main({'runs':reports}),'fixed_truth_facts':truth_facts(reports,json.loads(admission.read_text())['truth_population_parameters']),'status':'COMPLETE_BOUNDED_AUXILIARY_DIAGNOSTIC; CONVERGENCE_NOT_CERTIFIED','interpretation':'One fixed-truth realization with five loci, not prior-predictive simulation or repeated coverage calibration. Individual interval exclusion is not by itself a mixing defect. Fixed true topology was supplied, so topology recovery was not tested. No automatic further run.'}
    return out
if __name__=='__main__':print(json.dumps(main(),indent=2))
