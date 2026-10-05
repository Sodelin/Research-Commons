"""One bounded global producer/replay pair with immutable receipt-first evidence."""
import hashlib,importlib.util,json,os,resource,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
BASE=Path(__file__).resolve().parent
WATCHDOG=BASE.parent/'bpp-instrumented-diagnostic-20261005-0535z/watchdog.py'
WATCHDOG_SHA='c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e'
MEMORY=512*1024**2;OUTPUT=256*1024**2;RESERVE=4*1024**2;OUTER_SECONDS=150
FILES=('interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','global_contractors.py','global_engine.py','global_check.py','bounded_runner.py','prepare_controls.py')
CORE=FILES[:7]
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump_new(path,data):
    with Path(path).open('x') as out:json.dump(data,out,sort_keys=True,indent=2);out.write('\n')
def authenticate(manifest,identity):
    if digest(manifest)!=identity:raise ValueError('external source manifest identity')
    pins=json.loads(Path(manifest).read_text())
    if set(pins)!=set(FILES):raise ValueError('source allowlist')
    for name,pin in pins.items():
        if (BASE/name).is_symlink() or digest(BASE/name)!=pin:raise ValueError('source pin mismatch')
    return pins

def load_watchdog():
    if digest(WATCHDOG)!=WATCHDOG_SHA:raise ValueError('watchdog source pin')
    spec=importlib.util.spec_from_file_location('_global_watchdog',WATCHDOG);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def limits():resource.setrlimit(resource.RLIMIT_AS,(MEMORY,MEMORY))
def stage(command,attempt,label,watchdog,wall=OUTER_SECONDS):
    process=None;started_utc=datetime.now(timezone.utc).isoformat()
    try:
        with (attempt/(label+'.stdout')).open('xb') as stdout,(attempt/(label+'.stderr')).open('xb') as stderr:
            environment={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONPYCACHEPREFIX':str(attempt/'fresh-source-cache'),'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'}
            process=subprocess.Popen(command,stdout=stdout,stderr=stderr,cwd=BASE,start_new_session=True,preexec_fn=limits,env=environment)
            receipt=watchdog.monitor(process,attempt,wall,OUTPUT,receipt_reserve_bytes=RESERVE)
        receipt.update(started_utc=started_utc,finished_utc=datetime.now(timezone.utc).isoformat(),command=command,memory_limit_bytes=MEMORY,outer_wall_seconds=wall,source_import_policy='fresh cache prefix with bytecode writes disabled')
        dump_new(attempt/(label+'-TERMINAL.json'),receipt);return receipt
    finally:
        if process is not None:watchdog.terminate_group(process)

def run(request,identity,attempt,manifest,manifest_sha):
    pins=authenticate(manifest,manifest_sha);watchdog=load_watchdog()
    import global_engine as e
    e.read_request(request,identity);raw=Path(request).read_bytes()
    if e.sha(raw)!=identity:raise ValueError('request changed after admission')
    attempt=Path(attempt).absolute();attempt.mkdir(exist_ok=False);copied=attempt/'REQUEST.json';producer=None;checker=None;failure=None
    try:
        with copied.open('xb') as out:out.write(raw)
        dump_new(attempt/'BEFORE.json',{'sources':pins,'source_manifest_sha256':manifest_sha,'request_sha256':identity,'forward_sha256':e.m.SOURCE_SHA,'baseline_parser_sha256':e.BASELINE_SHA,'watchdog_sha256':WATCHDOG_SHA,'contracts':e.CONTRACTS})
        checker_pins=attempt/'CHECKER-PINS.json';dump_new(checker_pins,{name:pins[name] for name in CORE});checker_identity=digest(checker_pins)
        common=['--request',str(copied),'--request-sha256',identity,'--checkpoints',str(attempt/'journal')]
        producer=stage([sys.executable,str(BASE/'global_engine.py'),*common],attempt,'producer',watchdog)
        authenticate(manifest,manifest_sha)
        command=[sys.executable,str(BASE/'global_check.py'),*common,'--source-pins',str(checker_pins),'--source-pins-sha256',checker_identity]
        if producer['status']=='EXECUTION_EXIT_ZERO':command.append('--normal')
        checker=stage(command,attempt,'checker',watchdog)
    except Exception as error:failure={'type':type(error).__name__,'message':str(error)}
    finally:
        try:stable=authenticate(manifest,manifest_sha)==pins and digest(copied)==identity and digest(e.m.SOURCE)==e.m.SOURCE_SHA and digest(WATCHDOG)==WATCHDOG_SHA
        except Exception:stable=False
        inventory={};inventory_failure=None;size=None
        try:
            size=watchdog.tree_bytes(attempt)
            for path in sorted(attempt.rglob('*')):
                if path.is_file() and not path.is_symlink():inventory[str(path.relative_to(attempt))]={'sha256':digest(path),'bytes':path.stat().st_size}
        except Exception as error:inventory_failure={'type':type(error).__name__,'message':str(error)}
        available=stable and inventory_failure is None and checker is not None and checker['status']=='EXECUTION_EXIT_ZERO'
        receipt={'schema':'bounded-global-triangular-attempt-v1','producer':producer,'checker':checker,'source_and_input_pins_stable':stable,'checker_output_available':available,'certificate_status':'VALIDATION_OUTPUT_AVAILABLE' if available else 'NO_COMPLETED_CERTIFICATE','failure':failure,'inventory_failure':inventory_failure,'inventory':inventory,'bytes_before_terminal':size,'request_sha256':identity,'source_manifest_sha256':manifest_sha}
        dump_new(attempt/'TERMINAL.json',receipt)
    return receipt
if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--request',required=True);parser.add_argument('--request-sha256',required=True);parser.add_argument('--attempt',required=True);parser.add_argument('--source-manifest',required=True);parser.add_argument('--source-manifest-sha256',required=True);a=parser.parse_args();print(json.dumps(run(a.request,a.request_sha256,a.attempt,a.source_manifest,a.source_manifest_sha256),sort_keys=True,indent=2))
