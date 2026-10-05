"""Descriptive root-time mixing decomposition, not a stationarity test."""
import collections,hashlib,json
from pathlib import Path
import numpy as np
from summarize_a01 import parse
BASE=Path(__file__).resolve().parent
RUNS=BASE.parent/'bpp-sequence-pilot-20261005'/'runs'
NAMES=['A01-posterior-seed5511-long-v2','A01-posterior-seed6622-long-v2']
def read(name):
    folder=RUNS/name;t=json.loads((folder/'TERMINAL.json').read_text());p=folder/'result.mcmc.txt';data=p.read_bytes()
    expected=next(x['sha256'] for x in t['output_inventory'] if x['path']==p.name)
    if hashlib.sha256(data).hexdigest()!=expected:raise ValueError('trace changed')
    rows=[parse(x) for x in data.decode().splitlines()]
    if len(rows)!=t['settings']['nsample']+1:raise ValueError('trace length')
    rows=rows[1:];by=collections.defaultdict(list)
    for tree,_,height in rows:by[tree].append(height)
    x=np.array([r[2] for r in rows]);n=len(x)
    result={'run':name,'trace_sha256':expected,'mean':float(x.mean()),'ten_contiguous_block_means':[float(a.mean()) for a in np.array_split(x,10)],'topology_conditional':{tree:{'frequency':len(y)/n,'mean_root_height':float(np.mean(y)),'draws':len(y)} for tree,y in sorted(by.items())}}
    return result
if __name__=='__main__':
    a,b=map(read,NAMES);ta=a['topology_conditional'];tb=b['topology_conditional']
    if set(ta)!=set(tb):raise ValueError('this decomposition requires common observed support')
    composition=sum(.5*(ta[t]['frequency']-tb[t]['frequency'])*(ta[t]['mean_root_height']+tb[t]['mean_root_height']) for t in ta)
    within=sum(.5*(ta[t]['frequency']+tb[t]['frequency'])*(ta[t]['mean_root_height']-tb[t]['mean_root_height']) for t in ta)
    difference=a['mean']-b['mean']
    if abs(composition+within-difference)>1e-15:raise ValueError('decomposition mismatch')
    print(json.dumps({'schema':'root-time-descriptive-diagnostic-v1','chains':[a,b],'mean_difference':difference,'symmetric_topology_composition_component':composition,'symmetric_within_topology_component':within,'identity_verified_numerically':True,'causal_or_stationarity_claim':False,'note':'Algebraic decomposition of empirical averages; conditional draws need not be independent or stationary.'},indent=2))
