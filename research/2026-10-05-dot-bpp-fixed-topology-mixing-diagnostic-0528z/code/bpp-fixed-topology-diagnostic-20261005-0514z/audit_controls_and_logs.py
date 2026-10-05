"""Audit matched-target controls, labelled scalars, and actual tuning logs."""
import hashlib,json,re
from pathlib import Path
BASE=Path(__file__).resolve().parent
RUNS=BASE.parent/'bpp-sequence-pilot-20261005'/'runs'
NAMES=['A00-fixed-leading-seed9101','A00-fixed-leading-seed9202']
def sha(data):return hashlib.sha256(data).hexdigest()
def audit():
    records=[];normalized=[]
    for name in NAMES:
        folder=RUNS/name;t=json.loads((folder/'TERMINAL.json').read_text());inv={x['path']:x['sha256'] for x in t['output_inventory']}
        files={key:(folder/key).read_bytes() for key in ['control.ctl','stdout.log','result.txt','result.mcmc.txt']}
        if any(sha(data)!=inv[key] for key,data in files.items()):raise ValueError('runtime artifact hash mismatch')
        ctl=files['control.ctl'].decode();log=files['stdout.log'].decode();result=files['result.txt'].decode();header=files['result.mcmc.txt'].decode().splitlines()[0].split()
        target={}
        for key,want in [('thetaprior','gamma 2 2000'),('tauprior','gamma 2 1000'),('phase','1 1 1 1'),('usedata','1'),('cleandata','0'),('speciestree','0'),('speciesdelimitation','0'),('finetune','1'),('burnin','20000'),('nsample','50000'),('sampfreq','2')]:
            matches=re.findall(r'(?m)^\s*'+key+r'\s*=\s*([^\n]+)',ctl)
            if len(matches)!=1:raise ValueError('missing/duplicate target option')
            value=' '.join(re.split(r'[#*]',matches[0])[0].split())
            if value!=want:raise ValueError('effective target option differs')
            target[key]=value
        for key in ['burnin','nsample','sampfreq','usedata','speciestree','finetune']:
            if t['settings'][key]!=int(target[key]):raise ValueError('control/terminal settings mismatch')
        compact=''.join(ctl.split())
        if compact.count('(((H,L),C),K);')!=1 or t['conditional_topology']!='(((H,L),C),K);':raise ValueError('fixed topology mismatch')
        conditional=result.split('Summarizing parameter estimates using file result.conditional_a1b1.txt',1)[1]
        conditional_K=re.search(r'^theta:1\s+([.\d]+)\s+',conditional,re.M)
        if not conditional_K:raise ValueError('missing existing engine conditional theta summary')
        normalized.append(re.sub(r'(?m)^\s*seed\s*=.*$','seed = <independent>',ctl))
        if header[1]!='theta:1:K':raise ValueError('population K header moved')
        if not re.search(r'^0\s+0.000000\s+[.\d]+\s+K\s+\[ K \]',result,re.M):raise ValueError('population K node summary mismatch')
        warnings=[line for line in log.splitlines() if re.search(r'\[(?:WARNING|ERROR)\]|(?:^|\s)(?:Warning|WARNING|ERROR):',line)]
        pjumps=re.findall(r'Current Pjump:\s*([^\r\n]+)',log)
        steps=re.findall(r'New finetune:\s*([^\r\n]+)',log)
        if len(pjumps)!=len(steps) or not pjumps:raise ValueError('missing tuning rounds')
        names=['Gage','Gspr','th1','th2','tau','mix'];p=list(map(float,pjumps[-1].split()));eps=list(map(float,steps[-1].split()))
        if len(p)!=6 or len(eps)!=6:raise ValueError('unexpected tuning columns')
        model_rows=re.findall(r'^\s*\d+\s*\|\s*([A-Za-z][A-Za-z0-9]*)\s*\|',log,re.M)
        if not model_rows or set(model_rows)!={'JC69'}:raise ValueError('unexpected runtime model')
        rows=files['result.mcmc.txt'].decode().splitlines()[1:]
        if len(rows)!=50000 or rows[0].split()[0]!='2' or rows[-1].split()[0]!='100000':raise ValueError('incorrect retained generations')
        records.append({'run':name,'control_sha256':sha(files['control.ctl']),'stdout_sha256':sha(files['stdout.log']),'binary_alignment_map_hashes':{k:t['input_hashes_before'][k] for k in ['binary','alignment','map']},'effective_control_target':target,'engine_conditional_theta_K_mean':float(conditional_K[1]),'theta_K_header':'theta:1:K','theta_K_node_summary_verified':True,'fixed_topology':t['conditional_topology'],'retained_generation_first':2,'retained_generation_last':100000,'retained_rows':50000,'configured_burnin':int(target['burnin']),'autotune_rounds':len(pjumps),'final_tuning_acceptance':dict(zip(names,p)),'final_tuning_step':dict(zip(names,eps)),'runtime_substitution_models':sorted(set(model_rows)),'warning_error_lines':warnings})
    if normalized[0]!=normalized[1]:raise ValueError('control target differs beyond seed')
    if records[0]['binary_alignment_map_hashes']!=records[1]['binary_alignment_map_hashes']:raise ValueError('input target differs')
    return {'schema':'matched-fixed-tree-control-audit-v1','controls_identical_except_seed':True,'binary_alignment_map_identical':True,'records':records,'no_label_switching_claim':'Extant K is fixed by population label/header/runtime node summary; this is not a claim about hidden genealogy exploration.','postburnin_source_rule':'Pinned method.c records samples only when i>=0 and (i+1)%sampfreq==0; configured burnin precedes those generation labels.','interpretation':'Autotuning and moderate acceptance do not certify mixing or stationarity.'}
if __name__=='__main__':print(json.dumps(audit(),indent=2))
