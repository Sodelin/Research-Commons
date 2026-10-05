"""One reviewed fresh recovery attempt; same seed, dataset and engine target, larger finite wall cap."""
import argparse,datetime,hashlib,importlib.util,json,os,re,resource,shutil,subprocess,time
from pathlib import Path
BASE=Path(__file__).resolve().parent;DESIGN=BASE.parent/'bpp-matched-difficulty-design-20261005-0607z'
BIN=BASE.parent/'bpp-sequence-pilot-20261005/runtime/bpp-4.8.7-linux-x86_64/bin/bpp'
BIN_SHA='6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e'
WATCHDOG=BASE.parent/'bpp-instrumented-diagnostic-20261005-0535z/watchdog.py'
PROJECTOR=BASE/'project_fixture.py'
ADMISSION=BASE/'admit_fixture.py'
PROJECTOR_SHA='2aa59713f21b7e018b23b372984cd5e42afa86cd91ec0b1145f2f78713251cb1'
ADMISSION_SHA='3cc842ad5ab6276d991d39eed5a6dd82fb71d8c28780ddbb69544744e4909768'
WATCHDOG_SHA='c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sha(WATCHDOG)!=WATCHDOG_SHA:raise ValueError('reviewed watchdog changed')
spec=importlib.util.spec_from_file_location('watchdog',WATCHDOG);watchdog=importlib.util.module_from_spec(spec);spec.loader.exec_module(watchdog)
def write_json(p,v):p.write_text(json.dumps(v,indent=2)+'\n')

def check_dependencies():
    if sha(PROJECTOR)!=PROJECTOR_SHA or sha(ADMISSION)!=ADMISSION_SHA:raise ValueError('reviewed admission/projector dependency changed')

def execute(name,control,mode,settings,inputs,wall):
    check_dependencies()
    if name not in {'simulation-seed21001','A00-matched-recovery-seed21101'} or wall not in {60,1800}:raise ValueError('undeclared attempt')
    if name=='simulation-seed21001':
        if mode!='--simulate' or wall!=60 or settings.get('seed')!=21001 or hashlib.sha256(control.encode()).hexdigest()!='dad49392999ddf8a908286d588406fd119e77aac98b48d69b0ffc07665d4e5b8' or inputs:
            raise ValueError('simulation profile mismatch')
    else:
        seed=int(name.rsplit('seed',1)[1]);normalized,n=re.subn(r'(?m)^seed = '+str(seed)+'$', 'seed = 21101',control)
        if mode!='--cfile' or wall!=1800 or n!=1 or hashlib.sha256(normalized.encode()).hexdigest()!='e653b2a121d85d5cde534de9d18373319e9a7459879ddccedcfc660d18485098' or any(settings.get(k)!=v for k,v in {'seed':seed,'burnin':20000,'nsample':5000,'sampfreq':20,'usedata':1}.items()) or set(inputs)!={'alignment','map'}:
            raise ValueError('inference profile mismatch')
    if sha(BIN)!=BIN_SHA or sha(WATCHDOG)!=WATCHDOG_SHA:raise ValueError('runtime/helper pin mismatch')
    folder=BASE/'runs'/name;folder.mkdir(parents=True,exist_ok=False);proc=None;t0=time.monotonic()
    cmd=[str(BIN),mode,'control.ctl']+(['--theta_mode','3','--theta-showeps'] if mode=='--cfile' else [])
    receipt={'schema':'bounded-matched-synthetic-attempt-v1','status':'PREPARING','settings':settings,'command':['bpp']+cmd[1:],'wall_limit_seconds':wall,'address_space_limit_bytes':2147483648,'aggregate_attempt_limit_bytes':268435456,'threads':1,'conditional_topology':'(((H,L),C),K);','host_clock_start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'empirical_admission_claimed':False,'posterior_convergence_claimed':False,'simulation_calibration_claimed':False}
    try:
        for logical,(name_in,path) in inputs.items():shutil.copyfile(path,folder/name_in)
        (folder/'control.ctl').write_text(control)
        before={'binary':sha(BIN),'watchdog':sha(WATCHDOG),'runner':sha(Path(__file__)),'projector':sha(PROJECTOR),'admission':sha(ADMISSION),'control':sha(folder/'control.ctl'),**{logical:sha(folder/name_in) for logical,(name_in,path) in inputs.items()}}
        receipt.update(status='RUNNING',input_hashes_before=before);write_json(folder/'ATTEMPT.json',receipt)
        def limits():resource.setrlimit(resource.RLIMIT_AS,(2147483648,2147483648))
        with (folder/'stdout.log').open('w') as out:
            proc=subprocess.Popen(cmd,cwd=folder,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=limits)
            write_json(folder/'PID.json',{'pid':proc.pid});observed=watchdog.monitor(proc,folder,wall,268435456)
        after={'binary':sha(BIN),'watchdog':sha(WATCHDOG),'runner':sha(Path(__file__)),'projector':sha(PROJECTOR),'admission':sha(ADMISSION),'control':sha(folder/'control.ctl'),**{logical:sha(folder/name_in) for logical,(name_in,path) in inputs.items()}}
        receipt.update(status=observed['status'],exit_code=observed['exit_code'],watchdog_result=observed,input_hashes_after=after,inputs_stable=before==after)
        if before!=after:receipt['status']='INPUT_CHANGED'
    except BaseException as error:
        watchdog.terminate_group(proc);receipt.update(status='RUNNER_FAILURE',error_type=type(error).__name__,error=str(error));raise
    finally:
        receipt.update(elapsed_seconds=time.monotonic()-t0,host_clock_end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        receipt['output_inventory']=[{'path':p.relative_to(folder).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(folder.rglob('*')) if p.is_file() and not p.is_symlink() and p.relative_to(folder).as_posix() not in {'ATTEMPT.json','TERMINAL.json','PID.json'}]
        for _ in range(3):
            write_json(folder/'TERMINAL.json',receipt)
            try:size=watchdog.tree_bytes(folder)
            except (ValueError,OSError) as error:
                receipt['aggregate_final_bytes']=None;receipt['aggregate_measurement_error']=str(error);receipt['status']='RUNNER_FAILURE';break
            receipt['aggregate_final_bytes']=size;receipt['cap_overshoot_final_bytes']=max(0,size-268435456)
            if size>=268435456:receipt['status']='AGGREGATE_OUTPUT_LIMIT'
        write_json(folder/'TERMINAL.json',receipt)
    print(json.dumps({'run':name,'status':receipt['status'],'elapsed_seconds':receipt['elapsed_seconds'],'bytes':receipt['aggregate_final_bytes']}))
    if receipt['status']!='EXECUTION_EXIT_ZERO':raise RuntimeError('stage did not complete successfully')
    return receipt

def simulate():
    p=DESIGN/'simulation-control.PROPOSED.ctl'
    if sha(p)!='dad49392999ddf8a908286d588406fd119e77aac98b48d69b0ffc07665d4e5b8':raise ValueError('simulation design control changed')
    return execute('simulation-seed21001',p.read_text(),'--simulate',{'seed':21001,'loci':5,'full_sites_per_locus':489,'full_diploid_individuals':32,'full_gene_copies':64,'scientific_role':'known-truth auxiliary generation'}, {},60)

def infer(seed):
    if seed != 21101:raise ValueError('predeclared inference seed required')
    check_dependencies()
    original=BASE/'runs/A00-matched-seed21101/TERMINAL.json'
    if sha(original)!='155160e2db42a91db6c8e5d393ab237554ef256999df5e9206c9f237dfbb57e8':raise ValueError('preserved original timeout receipt changed')
    gate_spec=importlib.util.spec_from_file_location('reviewed_admission',ADMISSION);gate=importlib.util.module_from_spec(gate_spec);gate_spec.loader.exec_module(gate)
    admission=gate.admit();record=BASE/'SYNTHETIC-ADMISSION.json'
    if not record.exists() or json.loads(record.read_text())!=admission:raise ValueError('fresh runtime admission receipt required')
    p=DESIGN/'inference-control.PROPOSED.ctl'
    if sha(p)!='e653b2a121d85d5cde534de9d18373319e9a7459879ddccedcfc660d18485098':raise ValueError('inference design control changed')
    ctl,n=re.subn(r'(?m)^seed = 21101$',f'seed = {seed}',p.read_text())
    if n!=1:raise ValueError('control seed replacement not unique')
    projected=BASE/'runs/projected-seed21001'
    return execute(f'A00-matched-recovery-seed{seed}',ctl,'--cfile',{'seed':seed,'burnin':20000,'nsample':5000,'sampfreq':20,'usedata':1,'speciestree':0,'finetune':1,'theta_mode':3,'theta_proposal':'mg_invg','admission_sha256':sha(record),'scientific_role':'fixed-true-topology synthetic numerical control'}, {'alignment':('matched-synthetic.txt',projected/'matched-synthetic.txt'),'map':('matched-synthetic.Imap.txt',projected/'matched-synthetic.Imap.txt')},1800)
if __name__=='__main__':
    infer(21101)
