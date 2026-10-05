"""Descriptive comparison of two predeclared instrumented chains.
No p-values, convergence threshold, causal diagnosis or automatic extension.
"""
import json,math
from pathlib import Path
BASE=Path(__file__).resolve().parent

def compare(a,b):
    ma,mb=a['mcse'],b['mcse'];scale=None if ma is None or mb is None else math.hypot(ma,mb)
    return {'means':[a['mean'],b['mean']],'mean_difference':a['mean']-b['mean'],'combined_within_chain_heuristic_mcse':scale,'difference_over_heuristic_mcse':None if not scale else (a['mean']-b['mean'])/scale}

def main(report):
    a,b=report['runs'];out={'schema':'matched-auxiliary-pair-comparison-v1','data_role':'simulated auxiliary; not empirical frog inference','runs':[a['run'],b['run']],'scalars':{},'loci':[],'status':'DESCRIPTIVE_NOT_STATIONARITY_PROOF','note':'MCSE estimates are within-chain heuristics, not certified bounds or independent confirmation; no automatic further runs.'}
    if a['scalars']['conditional_topology']!=b['scalars']['conditional_topology']:raise ValueError('different conditional models')
    for key in a['scalars']['columns']:out['scalars'][key]=compare(a['scalars']['columns'][key],b['scalars']['columns'][key])
    if len(a['loci'])!=len(b['loci']):raise ValueError('different locus sets')
    for x,y in zip(a['loci'],b['loci']):
        if x['locus']!=y['locus'] or x['label_set_sha256']!=y['label_set_sha256']:raise ValueError('different locus/sample identity')
        out['loci'].append({'locus':x['locus'],'TH':compare(x['TH'],y['TH']),'TL':compare(x['TL'],y['TL'])})
    return out
if __name__=='__main__':print(json.dumps(main(json.loads((BASE/'matched-diagnostics.json').read_text())),indent=2))
