"""Two isolated, bounded stages; producer success alone is never a certificate."""
import argparse,hashlib,importlib.util,json,os,resource,subprocess,sys,time
from pathlib import Path
BASE=Path(__file__).resolve().parent
WATCHDOG=BASE.parent/'bpp-instrumented-diagnostic-20261005-0535z/watchdog.py'
WATCHDOG_SHA='c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e'
MEMORY=512*1024**2;OUTPUT=64*1024**2;OUTER_SECONDS=40

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump_new(path,obj):
    with Path(path).open('x') as out:json.dump(obj,out,sort_keys=True,indent=2);out.write('\n')
def load_watchdog():
    if digest(WATCHDOG)!=WATCHDOG_SHA:raise ValueError('watchdog pin mismatch')
    spec=importlib.util.spec_from_file_location('accepted_watchdog',WATCHDOG);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def pin_sources(manifest_path,expected):
    if digest(manifest_path)!=expected:raise ValueError('source manifest identity mismatch')
    manifest=json.loads(Path(manifest_path).read_text())
    if set(manifest)!=set(['filter_core.py','check_cover.py','filter_worker.py','fixture_requests.py','bounded_runner.py']):raise ValueError('source manifest allowlist mismatch')
    for name,pin in manifest.items():
        if (BASE/name).is_symlink() or digest(BASE/name)!=pin:raise ValueError('source pin mismatch: '+name)
    return manifest

def limits():resource.setrlimit(resource.RLIMIT_AS,(MEMORY,MEMORY))
def stage(command,attempt,label,watchdog,wall=OUTER_SECONDS):
    proc=None
    try:
        with (attempt/(label+'.stdout')).open('xb') as stdout,(attempt/(label+'.stderr')).open('xb') as stderr:
            proc=subprocess.Popen(command,stdout=stdout,stderr=stderr,cwd=BASE,start_new_session=True,preexec_fn=limits,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'})
            result=watchdog.monitor(proc,attempt,wall,OUTPUT)
        result.update(command=command,memory_limit_bytes=MEMORY,outer_wall_seconds=wall)
        dump_new(attempt/(label+'-TERMINAL.json'),result);return result
    finally:
        if proc is not None:watchdog.terminate_group(proc)

def run(request,request_sha,attempt,manifest,manifest_sha):
    pins=pin_sources(manifest,manifest_sha);watchdog=load_watchdog()
    # Import only after the external manifest authenticates our dependencies.
    import filter_core as c
    c.load_forward();c.read_request(request,request_sha)
    raw=Path(request).read_bytes()
    if hashlib.sha256(raw).hexdigest()!=request_sha:raise ValueError('request changed after admission')
    attempt=Path(attempt).absolute();attempt.mkdir(parents=False,exist_ok=False)
    copied=attempt/'REQUEST.json'
    producer=None;checker=None;failure=None
    try:
        with copied.open('xb') as out:out.write(raw)
        dump_new(attempt/'BEFORE.json',{'sources':pins,'source_manifest_sha256':manifest_sha,'request_sha256':request_sha,'forward_sha256':c.FORWARD_SHA,'watchdog_sha256':WATCHDOG_SHA})
        common=['--request',str(copied),'--request-sha256',request_sha,'--checkpoints',str(attempt/'checkpoints')]
        producer=stage([sys.executable,str(BASE/'filter_worker.py'),*common],attempt,'producer',watchdog)
        pin_sources(manifest,manifest_sha);c.load_forward()
        checkcmd=[sys.executable,str(BASE/'check_cover.py'),*common,'--producer-sha256',pins['filter_core.py']]
        if producer['status']=='EXECUTION_EXIT_ZERO':checkcmd.append('--normal')
        checker=stage(checkcmd,attempt,'checker',watchdog)
    except Exception as error:failure={'type':type(error).__name__,'message':str(error)}
    finally:
        try:after=pin_sources(manifest,manifest_sha);c.load_forward();stable=after==pins and digest(copied)==request_sha
        except Exception:stable=False
        inventory={};inventory_failure=None;measured_bytes=None
        try:
            measured_bytes=watchdog.tree_bytes(attempt)
            for p in sorted(attempt.rglob('*')):
                if p.is_file() and not p.is_symlink():inventory[str(p.relative_to(attempt))]={'sha256':digest(p),'bytes':p.stat().st_size}
        except Exception as error:inventory_failure={'type':type(error).__name__,'message':str(error)}
        accepted=stable and inventory_failure is None and checker is not None and checker['status']=='EXECUTION_EXIT_ZERO'
        receipt={'schema':'bounded-filter-attempt-v1','producer':producer,'checker':checker,'failure':failure,'source_and_input_pins_stable':stable,'checker_output_available':accepted,'certificate_status':'VALIDATION_OUTPUT_AVAILABLE' if accepted else 'NO_COMPLETED_CERTIFICATE','inventory':inventory,'inventory_failure':inventory_failure,'bytes_before_terminal':measured_bytes,'source_manifest_sha256':manifest_sha,'request_sha256':request_sha}
        dump_new(attempt/'TERMINAL.json',receipt)
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--request',required=True);p.add_argument('--request-sha256',required=True);p.add_argument('--attempt',required=True);p.add_argument('--source-manifest',required=True);p.add_argument('--source-manifest-sha256',required=True);a=p.parse_args()
    print(json.dumps(run(a.request,a.request_sha256,a.attempt,a.source_manifest,a.source_manifest_sha256),indent=2))
