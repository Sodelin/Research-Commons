"""Bounded known-truth BPP simulation/inference fixture; no new sampler.
Simulation and inference use distinct fixed seeds. Output is not calibration.
"""
import argparse, datetime, hashlib, json, os, resource, shutil, signal, subprocess, time
from pathlib import Path
BASE=Path(__file__).resolve().parent
BPPROOT=BASE.parent/'bpp-sequence-pilot-20261005'
BIN=BPPROOT/'runtime/bpp-4.8.7-linux-x86_64/bin/bpp'
PIN='6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write_json(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def cleanup(proc):
    if proc is None or proc.poll() is not None:return
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:os.killpg(proc.pid,signal.SIGKILL)
        except ProcessLookupError:pass
        proc.wait()
def execute(folder, control, mode, settings, inputs):
    if sha(BIN)!=PIN:raise ValueError('official executable pin mismatch')
    folder.mkdir(parents=True,exist_ok=False)
    proc=None;t0=time.monotonic()
    receipt={'schema':'bpp-known-truth-attempt-v1','command':['bpp',mode,'control.ctl'],'settings':settings,'status':'PREPARING','wall_limit_seconds':300,'address_space_limit_bytes':2147483648,'threads':1,'posterior_convergence_claimed':False,'simulation_calibration_claimed':False,'host_clock_start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        for name,path in inputs.items():shutil.copyfile(path,folder/name)
        (folder/'control.ctl').write_text(control)
        pins={'binary':sha(BIN),'runner':sha(Path(__file__)),'control.ctl':sha(folder/'control.ctl'),**{name:sha(folder/name) for name in inputs}}
        receipt.update(status='RUNNING',input_hashes_before=pins)
        write_json(folder/'ATTEMPT.json',receipt)
        def limits():resource.setrlimit(resource.RLIMIT_AS,(2147483648,2147483648))
        with (folder/'stdout.log').open('w') as out:
            proc=subprocess.Popen([str(BIN),mode,'control.ctl'],cwd=folder,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
            write_json(folder/'PID.json',{'pid':proc.pid})
            try:
                rc=proc.wait(timeout=300); status='EXECUTION_EXIT_ZERO' if rc==0 else 'EXECUTION_FAILED'
            except subprocess.TimeoutExpired:
                cleanup(proc);rc=proc.returncode;status='RESOURCE_TIME_LIMIT'
        after={'binary':sha(BIN),'runner':sha(Path(__file__)),'control.ctl':sha(folder/'control.ctl'),**{name:sha(folder/name) for name in inputs}}
        receipt.update(status=status,exit_code=rc,input_hashes_after=after,inputs_stable=(pins==after))
        if pins!=after:receipt['status']='INPUT_CHANGED'
    except BaseException as error:
        cleanup(proc);receipt.update(status='RUNNER_FAILURE',error_type=type(error).__name__,error=str(error));raise
    finally:
        receipt.update(elapsed_seconds=time.monotonic()-t0,host_clock_end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        receipt['output_inventory']=[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(folder.iterdir()) if p.is_file() and p.name not in {'ATTEMPT.json','PID.json','TERMINAL.json'}]
        write_json(folder/'TERMINAL.json',receipt)
    print(json.dumps({'folder':folder.name,'status':receipt['status'],'elapsed_seconds':receipt['elapsed_seconds']}))
    if receipt['status']!='EXECUTION_EXIT_ZERO':raise RuntimeError('synthetic control not completed')
    return folder

def simulate():
    control='''seed = 7001
seqfile = synthetic.txt
treefile = truth-gene-trees.txt
Imapfile = synthetic.Imap.txt
species&tree = 4 K C L H
  2 2 2 2
  ((K #0.001, C #0.001):0.001 #0.001, (L #0.001, H #0.001):0.0015 #0.001):0.002 #0.001;
phase = 1 1 1 1
loci&length = 5 500
clock = 1
locusrate = 0
model = 0
'''
    return execute(BASE/'synthetic-runs'/'simulation-seed7001',control,'--simulate',{'seed':7001,'loci':5,'length':500,'individuals_per_population':2,'phase':[1,1,1,1],'model':'JC69','truth':'((K,C),(L,H));','tau_KC':.001,'tau_LH':.0015,'tau_root':.002,'theta_all':.001},{})

def infer(seed):
    if seed not in {8001,8002}:raise ValueError('predeclared inference seed required')
    sim=BASE/'synthetic-runs'/'simulation-seed7001'
    t=json.loads((sim/'TERMINAL.json').read_text())
    if t['status']!='EXECUTION_EXIT_ZERO' or not t['inputs_stable']:raise ValueError('simulation must complete stably')
    inventory={x['path']:x['sha256'] for x in t['output_inventory']}
    for name in ['synthetic.txt','synthetic.Imap.txt']:
        if sha(sim/name)!=inventory[name]:raise ValueError('simulation output changed')
    control=f'''seed = {seed}
seqfile = synthetic.txt
Imapfile = synthetic.Imap.txt
jobname = result
speciesdelimitation = 0
speciestree = 1 0.4 0.2 0.1
speciesmodelprior = 1
species&tree = 4 K C L H
  2 2 2 2
  (((K,H),L),C);
phase = 1 1 1 1
usedata = 1
nloci = 5
cleandata = 0
model = JC69
clock = 1
thetaprior = gamma 2 2000
tauprior = gamma 2 1000
finetune = 1
print = 1 0 0 0
burnin = 8000
sampfreq = 2
nsample = 20000
threads = 1
'''
    return execute(BASE/'synthetic-runs'/f'A01-synthetic-seed{seed}',control,'--cfile',{'seed':seed,'burnin':8000,'nsample':20000,'sampfreq':2,'usedata':1,'simulation_terminal_sha256':sha(sim/'TERMINAL.json')},{name:sim/name for name in ['synthetic.txt','synthetic.Imap.txt']})
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('action',choices=['simulate','infer']);p.add_argument('--seed',type=int);a=p.parse_args()
    if a.action=='simulate':
        if a.seed is not None:p.error('simulation seed is fixed 7001')
        simulate()
    else:infer(a.seed)
