"""Instrumented fixed-tree scalar, per-node tuning and per-locus TH/TL diagnostics.
No topology-stationarity or biological-admission claim.
"""
import hashlib,importlib.util,json,re
from pathlib import Path
import numpy as np
BASE=Path(__file__).resolve().parent
RUNS=BASE/'runs'
HELPER=BASE/'summarize_matched_scalars.py'
HELPER_SHA=hashlib.sha256(HELPER.read_bytes()).hexdigest()
if HELPER_SHA!='53c69adf8401fc38cd55efd687d6bb3fef116433221f0a13a722a457489e5ea4':raise ValueError('reviewed scalar helper changed')
SPEC=importlib.util.spec_from_file_location('fixed',HELPER);FIXED=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(FIXED)
NAMES=['A00-matched-seed21101','A00-matched-seed21102']
NUM=r'(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?'

def tuning(log,theta_labels):
    log=log.replace('\r','\n')
    pattern=r'(?m)^\s*(Gage\s+Gspr(?:\s+th\d+)+\s+tau\s+mix)\s*\nCurrent Pjump:\s*([^\n]+)\nCurrent finetune:\s*([^\n]+)\nNew finetune:\s*([^\n]+)'
    blocks=re.findall(pattern,log)
    if not blocks:raise ValueError('no labelled per-node tuning block')
    names=blocks[-1][0].split();expected=['Gage','Gspr']+['th'+str(i) for i in range(1,8)]+['tau','mix']
    if names!=expected:raise ValueError('unexpected per-node tuning identities')
    values=list(map(float,blocks[-1][1].split()));steps=list(map(float,blocks[-1][3].split()))
    if len(values)!=len(names) or len(steps)!=len(names) or any(not 0<=v<=1 for v in values) or any(not np.isfinite(v) or v<=0 for v in steps):raise ValueError('bad tuning values')
    lines=re.findall(r'(?m)^\s*100%\s+([^\n]+)',log)
    if not lines:raise ValueError('no final progress acceptance row')
    row=lines[-1].split();node_rates={}
    for i in range(7):
        token=row[2+i]
        if not re.fullmatch(NUM+':'+NUM,token):raise ValueError('missing slide:gibbs node acceptance')
        a,b=map(float,token.split(':'))
        if not(0<=a<=1 and 0<=b<=1):raise ValueError('acceptance outside unit interval')
        node_rates[theta_labels[i+1]]={'sliding_window':a,'metropolized_gibbs':b}
    return {'autotune_rounds':len(blocks),'final_burnin_tuning_acceptance':dict(zip(names,values)),'final_step_sizes':dict(zip(names,steps)),'final_progress_node_acceptance_rounded_2dp':node_rates}

def genealogy_stats(data,expected_labels,samples):
    rows=data.decode().splitlines()
    if len(rows)!=samples:raise ValueError('genealogy retained-row count')
    heights=[];lengths=[]
    for row in rows:
        m=re.fullmatch(r'(.+;)\s*\[TH=('+NUM+r'), TL=('+NUM+r')\]',row)
        if not m:raise ValueError('genealogy format')
        tree=m[1];labels=re.findall(r'[(,]\s*([^():,;\s]+)\s*:',tree)
        if len(labels)!=len(expected_labels) or set(labels)!=expected_labels:raise ValueError('genealogy sample labels changed')
        if tree.count('(')!=len(labels)-1 or tree.count(')')!=len(labels)-1:raise ValueError('nonbinary genealogy structure')
        depth=0
        for c in tree:
            if c=='(':depth+=1
            elif c==')':depth-=1
            if depth<0:raise ValueError('unbalanced genealogy')
        if depth:raise ValueError('unbalanced genealogy')
        h,total=float(m[2]),float(m[3])
        if not(np.isfinite(h) and np.isfinite(total)) or h<=0 or total+2e-6<2*h:raise ValueError('invalid TH/TL')
        heights.append(h);lengths.append(total)
    def stats(x):
        a=np.asarray(x);return {'mean':float(a.mean()),'quantiles_025_50_975':np.quantile(a,[.025,.5,.975]).tolist(),'ten_contiguous_block_means':[float(z.mean()) for z in np.array_split(a,min(10,len(a)))],**FIXED.M.ess(a)}
    return {'retained_genealogies':samples,'gene_copy_count':len(expected_labels),'label_set_sha256':hashlib.sha256('\n'.join(sorted(expected_labels)).encode()).hexdigest(),'TH':stats(heights),'TL':stats(lengths)}

def expected_locus_labels(data):
    lines=[line.strip() for line in data.decode().splitlines() if line.strip()];pos=0;result=[]
    while pos<len(lines):
        n,length=map(int,lines[pos].split());pos+=1
        if n<=0 or length<=0:raise ValueError('bad admitted locus dimension')
        labels=set()
        for line in lines[pos:pos+n]:
            parts=line.split();label=parts[0]
            if len(''.join(parts[1:]))!=length:raise ValueError('bad admitted sequence length')
            labels.update([label+'.1',label+'.2'])
        if len(labels)!=2*n:raise ValueError('duplicated input observations')
        result.append(labels);pos+=n
    if len(result)!=5:raise ValueError('expected five admitted loci')
    return result

def summarize(name):
    folder=RUNS/name;t=json.loads((folder/'TERMINAL.json').read_text());inv={x['path']:x['sha256'] for x in t['output_inventory']}
    if t['status']!='EXECUTION_EXIT_ZERO' or not t['inputs_stable']:raise ValueError('not a completed stable run')
    if (t['settings']['burnin'],t['settings']['nsample'],t['settings']['sampfreq'])!=(20000,5000,20):raise ValueError('unexpected sample contract')
    data=(folder/'matched-synthetic.txt').read_bytes()
    if hashlib.sha256(data).hexdigest()!=t['input_hashes_before']['alignment']:raise ValueError('alignment changed')
    expected=expected_locus_labels(data)
    def output(name):
        raw=(folder/name).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=inv[name]:raise ValueError('output changed: '+name)
        return raw
    header=output('result.mcmc.txt').decode().splitlines()[0].split()
    theta_labels={int(k.split(':')[1]):k.split(':')[2] for k in header if k.startswith('theta:')}
    if set(theta_labels)!=set(range(1,8)):raise ValueError('wrong fixed-tree theta identities')
    scalar=FIXED.summarize(name)
    rates=tuning(output('stdout.log').decode(),theta_labels)
    loci=[]
    for i,labels in enumerate(expected,1):
        fname=f'result.gtree.L{i}';raw=output(fname)
        loci.append({'locus':i,'file':fname,'sha256':hashlib.sha256(raw).hexdigest(),**genealogy_stats(raw,labels,5000)})
    return {'run':name,'scalars':scalar,'tuning':rates,'loci':loci,'output_watchdog':t['watchdog_result'],'aggregate_final_bytes':t['aggregate_final_bytes'],'cap_overshoot_final_bytes':t['cap_overshoot_final_bytes'],'convergence_claimed':False}
if __name__=='__main__':
    reports=list(map(summarize,NAMES))
    print(json.dumps({'schema':'bpp-matched-layout-auxiliary-diagnostic-v1','data_role':'newly simulated matched-layout auxiliary; not the empirical frog alignment','scalar_helper_sha256':HELPER_SHA,'runs':reports,'status':'DIAGNOSTIC_ONLY; NOT_A_STATIONARITY_OR_ADMISSION_PROOF'},indent=2))
