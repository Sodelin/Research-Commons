"""Read pinned BPP A01 Newick traces, excluding its initial-state row.
No sequence data, sampler, biological admission, or convergence certificate.
"""
import collections, hashlib, itertools, json, math, re
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent.parent/'bpp-sequence-pilot-20261005'
NUM=r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'
TOKEN=re.compile(r'\s*('+NUM+r'|[A-Za-z_][A-Za-z_0-9]*|[(),;:#])')

def parse(text):
    tokens=[]; pos=0
    while pos < len(text.rstrip()):
        m=TOKEN.match(text,pos)
        if not m:raise ValueError('invalid Newick token')
        tokens.append(m[1]);pos=m.end()
    i=0;tips=[];clades=[]
    def node():
        nonlocal i
        if i>=len(tokens):raise ValueError('truncated tree')
        if tokens[i]=='(':
            i+=1;a=node()
            if tokens[i]!=',':raise ValueError('binary tree required')
            i+=1;b=node()
            if tokens[i]!=')':raise ValueError('binary tree required')
            i+=1
            labels=a[1]|b[1]; canonical='('+','.join(sorted([a[0],b[0]]))+')'
            heights=[a[2]+a[3],b[2]+b[3]]
            if abs(heights[0]-heights[1])>3e-6:raise ValueError('non-ultrametric trace beyond printed rounding')
            height=sum(heights)/2
            if len(labels)<4:clades.append(''.join(sorted(labels)))
        else:
            label=tokens[i];i+=1
            if label not in {'K','C','L','H'}:raise ValueError('unexpected tip')
            tips.append(label);labels={label};canonical=label;height=0
        branch=0;seen=set()
        while i<len(tokens) and tokens[i] in {'#',':'}:
            marker=tokens[i];i+=1
            if marker in seen:raise ValueError('duplicate node attribute')
            seen.add(marker)
            if i>=len(tokens) or not re.fullmatch(NUM,tokens[i]):raise ValueError('numeric attribute required')
            x=float(tokens[i]);i+=1
            if not math.isfinite(x) or x<0:raise ValueError('nonfinite/negative attribute')
            if marker==':':branch=x
        return canonical,labels,height,branch
    out=node()
    if tokens[i:]!=[';'] or sorted(tips)!=['C','H','K','L']:raise ValueError('tree labels/end mismatch')
    return out[0]+';',frozenset(clades),out[2]

def ess(x):
    x=np.asarray(x,dtype=float);n=len(x);v=float(np.var(x))
    if v==0:return {'ess':None,'mcse':None,'status':'CONSTANT_TRACE_NOT_DIAGNOSTIC'}
    y=x-x.mean(); size=1<<(2*n-1).bit_length();f=np.fft.rfft(y,size)
    ac=np.fft.irfft(f*np.conjugate(f),size)[:n]/n/v
    # Initial-positive, initial-monotone paired autocorrelation estimator.
    pairs=[]
    for k in range(0,n-1,2):
        pair=float(ac[k]+ac[k+1])
        if pair<=0:break
        pairs.append(min(pair,pairs[-1]) if pairs else pair)
    tau=max(1.0,-1+2*sum(pairs));e=min(n,n/tau)
    return {'ess':e,'mcse':math.sqrt(v/e),'status':'WITHIN_CHAIN_HEURISTIC'}

def dist(values):
    c=collections.Counter(values);return {k:v/len(values) for k,v in c.items()}
def tv(a,b):return sum(abs(a.get(k,0)-b.get(k,0)) for k in a.keys()|b.keys())/2

def summarize(name, run_root=None):
    folder=(Path(run_root) if run_root is not None else ROOT/'runs')/name;t=json.loads((folder/'TERMINAL.json').read_text())
    if t['status']!='EXECUTION_EXIT_ZERO' or not t['inputs_stable']:raise ValueError('run not terminal/stable')
    p=folder/'result.mcmc.txt';raw=p.read_bytes()
    inv={x['path']:x['sha256'] for x in t['output_inventory']}
    if hashlib.sha256(raw).hexdigest()!=inv[p.name]:raise ValueError('trace changed after terminal')
    rows=[parse(x) for x in raw.decode().splitlines() if x.strip()]
    n=t['settings']['nsample']
    if len(rows)!=n+1:raise ValueError('expected initial row plus nsample')
    initial=rows[0][0];rows=rows[1:];trees=[x[0] for x in rows];counts=collections.Counter(trees)
    # Upstream summary includes the extra initial tree. Check exactly, not rounded probabilities.
    vendor={}
    vendor_path=folder/'result.txt'
    if hashlib.sha256(vendor_path.read_bytes()).hexdigest()!=inv[vendor_path.name]:raise ValueError('vendor summary changed after terminal')
    output=vendor_path.read_text(); section=output.split('(A) Best trees in the sample',1)[1].split('(B)',1)[0]
    for line in section.splitlines():
        m=re.match(r'\s*(\d+)\s+[\d.]+\s+[\d.]+\s+(\(.*;)',line)
        if m:vendor[parse(m[2])[0]]=int(m[1])
    expected=counts.copy();expected[initial]+=1
    if vendor!=expected:raise ValueError('vendor count cross-check failed')
    topology=[];cumulative=0;credible=[]
    for k,v in sorted(counts.items(),key=lambda kv:(-kv[1],kv[0])):
        indicator=[float(x==k) for x in trees];d=ess(indicator)
        topology.append({'tree':k,'count':v,'frequency':v/n,**d})
        if cumulative<.95:credible.append(k);cumulative+=v/n
    clades={}
    for size in [2,3]:
        for c in itertools.combinations('CHKL',size):
            k=''.join(c);x=[float(k in row[1]) for row in rows]
            clades[k]={'frequency':sum(x)/n,**ess(x)}
    height=[row[2] for row in rows]
    return {'run':name,'seed':t['settings']['seed'],'usedata':t['settings']['usedata'],'retained_samples':n,'initial_row_excluded':True,'vendor_counts_match_with_initial':True,'trace_sha256':hashlib.sha256(raw).hexdigest(),'terminal_sha256':hashlib.sha256((folder/'TERMINAL.json').read_bytes()).hexdigest(),'topologies':topology,'credible_set_95':credible,'clades':clades,'transitions':sum(a!=b for a,b in zip(trees,trees[1:])),'split_half_total_variation':tv(dist(trees[:n//2]),dist(trees[n//2:])),'root_height':{'mean':float(np.mean(height)),'quantiles_025_50_975':np.quantile(height,[.025,.5,.975]).tolist(),**ess(height)},'convergence_claimed':False},trees

def main(names, run_root=None):
    reports=[];traces=[]
    for name in names:
        r,t=summarize(name,run_root=run_root);reports.append(r);traces.append(t)
    comparisons=[]
    for i,j in itertools.combinations(range(len(reports)),2):
        if reports[i]['usedata']==reports[j]['usedata']:
            comparisons.append({'runs':[names[i],names[j]],'topology_total_variation':tv(dist(traces[i]),dist(traces[j]))})
    return {'schema':'bpp-a01-diagnostics-v1','runs':reports,'comparisons':comparisons,'calibrated':False,'biological_admission':False,'note':'Monte Carlo diagnostics are estimates, not a proof of convergence; initial pre-burn-in row excluded.'}
if __name__=='__main__':
    import sys
    print(json.dumps(main(sys.argv[1:]),indent=2))
