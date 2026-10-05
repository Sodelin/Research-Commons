"""Summarize fixed-topology root/extant-theta/likelihood traces; no convergence proof."""
import hashlib,importlib.util,json,io
from pathlib import Path
import numpy as np
BASE=Path(__file__).resolve().parent
HELPER=BASE.parent/'bpp-a01-continuation-20261005-0450z'/'summarize_a01.py'
HELPER_SHA256=hashlib.sha256(HELPER.read_bytes()).hexdigest()
if HELPER_SHA256!='e8e86ef17f2f25a98f63108661fe234a40f0033922a915ff96862ded2bb3e9ce':raise ValueError('reviewed ESS helper changed')
SPEC=importlib.util.spec_from_file_location('a01summary',HELPER)
M=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(M)
RUNS=BASE/'runs'
NAMES=['A00-matched-seed21101','A00-matched-seed21102']
def summarize(name):
    folder=RUNS/name;t=json.loads((folder/'TERMINAL.json').read_text());p=folder/'result.mcmc.txt';data=p.read_bytes()
    if t['status']!='EXECUTION_EXIT_ZERO' or not t['inputs_stable']:raise ValueError('not stable terminal')
    expected=next(x['sha256'] for x in t['output_inventory'] if x['path']==p.name)
    if hashlib.sha256(data).hexdigest()!=expected:raise ValueError('trace changed')
    header=data.decode().splitlines()[0].split();x=np.loadtxt(io.StringIO(data.decode()),skiprows=1)
    if len(header)!=len(set(header)):raise ValueError('duplicate header labels')
    n=t['settings']['nsample']
    if x.shape!=(n,len(header)) or not np.isfinite(x).all():raise ValueError('trace shape/numbers')
    if not np.array_equal(x[:,0],np.arange(1,n+1)*t['settings']['sampfreq']):raise ValueError('generation labels')
    result_path=folder/'result.txt'
    result_expected=next(z['sha256'] for z in t['output_inventory'] if z['path']==result_path.name)
    result_bytes=result_path.read_bytes()
    if hashlib.sha256(result_bytes).hexdigest()!=result_expected:raise ValueError('engine summary changed')
    result_text=result_bytes.decode()
    summary_section=result_text.split('ESS*',1)[1].split('List of nodes, taus and thetas:',1)[0]
    vendor={}
    for line in summary_section.splitlines():
        parts=line.split()
        if len(parts)==13 and (parts[0].startswith(('theta:','tau:')) or parts[0]=='lnL'):
            vendor[parts[0]]=list(map(float,parts[1:]))
    columns={}
    for i,label in enumerate(header):
        parts=label.split(':');kind=parts[0]
        root=kind=='tau' and set(parts[-1].split(','))==set('KCLH')
        if root and len(parts[-1].split(','))!=4:raise ValueError('duplicate root-population label')
        extant=kind=='theta' and parts[-1] in 'KCLH' and len(parts[-1])==1
        if not(root or extant or label=='lnL'):continue
        key='root_tau' if root else ('theta_'+parts[-1] if extant else 'lnL')
        if key in columns:raise ValueError('duplicate semantic scalar identity')
        y=x[:,i]
        if key!='lnL' and np.min(y)<=0:raise ValueError('nonpositive parameter')
        row_key=':'.join(parts[:2]) if key!='lnL' else 'lnL'
        if row_key not in vendor:raise ValueError('missing engine scalar summary')
        engine=vendor[row_key]
        if abs(engine[0]-float(y.mean()))>5.01e-7:raise ValueError('engine/trace mean discrepancy')
        columns[key]={'engine_mean':engine[0],'engine_ess':engine[9],'engine_efficiency':engine[10],'engine_lag1_correlation':engine[11],'engine_mean_matches_trace_rounding':True,'source_header':label,'mean':float(y.mean()),'quantiles_025_50_975':np.quantile(y,[.025,.5,.975]).tolist(),'ten_contiguous_block_means':[float(a.mean()) for a in np.array_split(y,min(10,len(y)))],**M.ess(y)}
    if set(columns)!={'root_tau','theta_K','theta_C','theta_L','theta_H','lnL'}:raise ValueError('required scalar identity')
    return {'run':name,'samples':n,'trace_sha256':expected,'conditional_topology':t['conditional_topology'],'columns':columns,'convergence_claimed':False}
if __name__=='__main__':
    reports=list(map(summarize,NAMES)); comparisons={}
    for key in reports[0]['columns']:
        a=reports[0]['columns'][key];b=reports[1]['columns'][key]
        scale=None if a['mcse'] is None or b['mcse'] is None else (a['mcse']**2+b['mcse']**2)**.5
        comparisons[key]={'mean_difference':a['mean']-b['mean'],'combined_within_chain_heuristic_mcse':scale,'difference_over_heuristic_mcse':None if not scale else (a['mean']-b['mean'])/scale}
    print(json.dumps({'schema':'bpp-fixed-leading-diagnostic-v1','runs':reports,'comparisons':comparisons,'status':'DESCRIPTIVE_DIAGNOSTIC_NOT_STATIONARITY_PROOF','reviewed_ess_helper_sha256':HELPER_SHA256,'a01_convergence_claimed':False},indent=2))
