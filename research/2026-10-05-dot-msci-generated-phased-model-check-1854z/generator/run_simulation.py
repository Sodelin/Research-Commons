"""One isolated official-generator invocation, with a fixed compiled control."""
import hashlib,importlib.util,json,os,resource,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
BASE=Path(__file__).resolve().parent
WATCHDOG=BASE.parent/'bpp-instrumented-diagnostic-20261005-0535z/watchdog.py'
WATCHDOG_SHA='c89201b45fe65915e3130659fd4dc3522bedfcbab6970735c5b06793a2ec1d8e'
FILES=('compile_control.py','admit_generated.py','run_simulation.py')
MEMORY=512*1024**2;OUTPUT=16*1024**2;RESERVE=1024**2;WALL=60
VENDOR=BASE.parent/'bpp-sequence-pilot-20261005/upstream-bpp-v4.8.7'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump(path,value):
    with Path(path).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
def authenticate(manifest,expected):
    if Path(manifest).is_symlink() or sha(manifest)!=expected:raise ValueError('source manifest identity')
    pins=json.loads(Path(manifest).read_text())
    if set(pins)!=set(('sources','binary_sha256','control_sha256','compilation_sha256','source_audit_sha256','genealogy_parser_sha256','watchdog_sha256')) or set(pins['sources'])!=set(FILES):raise ValueError('source manifest schema')
    for name,h in pins['sources'].items():
        if (BASE/name).is_symlink() or sha(BASE/name)!=h:raise ValueError('source pin mismatch')
    import compile_control as d
    if pins['binary_sha256']!=d.BINARY_SHA or d.BINARY.is_symlink() or sha(d.BINARY)!=d.BINARY_SHA:raise ValueError('official binary pin')
    if pins['watchdog_sha256']!=WATCHDOG_SHA or sha(WATCHDOG)!=WATCHDOG_SHA:raise ValueError('watchdog pin')
    if sha(BASE/'SOURCE-AUDIT.json')!=pins['source_audit_sha256']:raise ValueError('source audit pin')
    audit=json.loads((BASE/'SOURCE-AUDIT.json').read_text())
    for name,h in audit['files'].items():
        path=VENDOR/name
        if path.is_symlink() or sha(path)!=h:raise ValueError('vendor source/manual changed')
    import admit_generated as a
    if pins['genealogy_parser_sha256']!=a.PARSER_SHA or sha(a.PARSER)!=a.PARSER_SHA:raise ValueError('retained parser pin')
    if sha(BASE/'compiled/control.ctl')!=pins['control_sha256'] or sha(BASE/'compiled/COMPILATION.json')!=pins['compilation_sha256']:raise ValueError('compiled control pin')
    control,receipt=d.compile_control()
    if control!=(BASE/'compiled/control.ctl').read_bytes() or d.canonical(receipt)!=(BASE/'compiled/COMPILATION.json').read_bytes():raise ValueError('compiler reproduction')
    return pins,d

def load_watchdog():
    if sha(WATCHDOG)!=WATCHDOG_SHA:raise ValueError('watchdog changed')
    spec=importlib.util.spec_from_file_location('_semantic_watchdog',WATCHDOG);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def limits():resource.setrlimit(resource.RLIMIT_AS,(MEMORY,MEMORY))
def run(attempt,manifest,expected):
    pins,d=authenticate(manifest,expected);watchdog=load_watchdog();attempt=Path(attempt).absolute();attempt.mkdir(exist_ok=False);proc=None;outcome=None;failure=None;cleanup_failure=None;command=[str(d.BINARY),'--simulate','control.ctl'];started=datetime.now(timezone.utc).isoformat()
    try:
        with (attempt/'control.ctl').open('xb') as f:f.write((BASE/'compiled/control.ctl').read_bytes())
        dump(attempt/'BEFORE.json',{'source_manifest_sha256':expected,'pins':pins,'control_sha256':sha(attempt/'control.ctl'),'command':command,'memory_limit_bytes':MEMORY,'outer_wall_seconds':WALL,'output_polling_limit_bytes':OUTPUT,'receipt_reserve_bytes':RESERVE})
        with (attempt/'stdout.log').open('xb') as stdout,(attempt/'stderr.log').open('xb') as stderr:
            proc=subprocess.Popen(command,cwd=attempt,stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=limits,env={**os.environ,'OMP_NUM_THREADS':'1','OPENBLAS_NUM_THREADS':'1'})
            dump(attempt/'PID.json',{'pid':proc.pid,'process_group':proc.pid})
            outcome=watchdog.monitor(proc,attempt,WALL,OUTPUT,receipt_reserve_bytes=RESERVE)
    except Exception as error:failure={'type':type(error).__name__,'message':str(error)}
    finally:
        if proc is not None:
            try:watchdog.terminate_group(proc)
            except ProcessLookupError:pass
            except Exception as error:cleanup_failure={'type':type(error).__name__,'message':str(error)}
        try:stable=authenticate(manifest,expected)[0]==pins and sha(attempt/'control.ctl')==pins['control_sha256']
        except Exception:stable=False
        inventory={};size=None;inventory_failure=None
        try:
            size=watchdog.tree_bytes(attempt)
            for path in sorted(attempt.rglob('*')):
                if path.is_file() and not path.is_symlink():inventory[str(path.relative_to(attempt))]={'sha256':sha(path),'bytes':path.stat().st_size}
        except Exception as error:inventory_failure={'type':type(error).__name__,'message':str(error)}
        status=outcome['status'] if outcome is not None and failure is None and cleanup_failure is None else 'RUNNER_FAILURE'
        terminal={'schema':'bounded-single-msci-generator-attempt-v1','status':status,'source_manifest_sha256':expected,'command':command,'started_utc':started,'finished_utc':datetime.now(timezone.utc).isoformat(),'pins_stable':stable,'runner_failure':failure,'cleanup_failure':cleanup_failure,'inventory_failure':inventory_failure,'watchdog':outcome,'bytes_before_terminal':size,'inventory':inventory,'synthetic_model_check_only':True,'finite_program_law_certified':False,'data_confidence_certificate_issued':False,'automatic_retry':False}
        dump(attempt/'TERMINAL.json',terminal)
    return terminal
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--attempt',required=True);p.add_argument('--source-manifest',required=True);p.add_argument('--source-manifest-sha256',required=True);a=p.parse_args();print(json.dumps(run(a.attempt,a.source_manifest,a.source_manifest_sha256),sort_keys=True,indent=2))
