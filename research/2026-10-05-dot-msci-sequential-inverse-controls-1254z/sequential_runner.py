"""Bounded sequential producer/checker wrapper, reusing the accepted process monitor."""
import hashlib,importlib.util,json,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
RUNNER=BASE.parent/'msci-bounded-inverse-filter-20261005-1102z/bounded_runner.py'
RUNNER_SHA='bc3cea6a8bb51fcbd888ba2e8ae2b25a87ad1a56e79ee69a8b3c3e5780d930db'
if hashlib.sha256(RUNNER.read_bytes()).hexdigest()!=RUNNER_SHA:raise ValueError('accepted runner source mismatch')
spec=importlib.util.spec_from_file_location('_accepted_bounded_runner',RUNNER);prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
FILES=('interval_math.py','contractors.py','seq_engine.py','seq_check.py','sequential_runner.py','prepare_controls.py')
CORE=('interval_math.py','contractors.py','seq_engine.py','seq_check.py')

def authenticate(manifest,identity):
    if prior.digest(manifest)!=identity:raise ValueError('external source manifest identity')
    pins=json.loads(Path(manifest).read_text())
    if set(pins)!=set(FILES):raise ValueError('source allowlist')
    for name,digest in pins.items():
        if (BASE/name).is_symlink() or prior.digest(BASE/name)!=digest:raise ValueError('source identity mismatch')
    return pins

def run(request,request_sha,attempt,manifest,manifest_sha):
    pins=authenticate(manifest,manifest_sha);watchdog=prior.load_watchdog()
    import seq_engine as e
    e.read_request(request,request_sha);raw=Path(request).read_bytes()
    if e.sha(raw)!=request_sha:raise ValueError('request changed after admission')
    attempt=Path(attempt).absolute();attempt.mkdir(exist_ok=False);copied=attempt/'REQUEST.json';producer=None;checker=None;failure=None
    try:
        with copied.open('xb') as out:out.write(raw)
        prior.dump_new(attempt/'BEFORE.json',{'sources':pins,'source_manifest_sha256':manifest_sha,'request_sha256':request_sha,'forward_sha256':e.m.SOURCE_SHA,'baseline_admission_sha256':e.BASELINE_SHA,'prior_runner_sha256':RUNNER_SHA,'watchdog_sha256':prior.WATCHDOG_SHA})
        core=attempt/'CHECKER-PINS.json';prior.dump_new(core,{name:pins[name] for name in CORE});core_sha=prior.digest(core)
        common=['--request',str(copied),'--request-sha256',request_sha,'--checkpoints',str(attempt/'checkpoints')]
        producer=prior.stage([sys.executable,str(BASE/'seq_engine.py'),*common],attempt,'producer',watchdog)
        authenticate(manifest,manifest_sha)
        command=[sys.executable,str(BASE/'seq_check.py'),*common,'--source-pins',str(core),'--source-pins-sha256',core_sha]
        if producer['status']=='EXECUTION_EXIT_ZERO':command.append('--normal')
        checker=prior.stage(command,attempt,'checker',watchdog)
    except Exception as error:failure={'type':type(error).__name__,'message':str(error)}
    finally:
        try:stable=authenticate(manifest,manifest_sha)==pins and prior.digest(copied)==request_sha and prior.digest(e.m.SOURCE)==e.m.SOURCE_SHA and prior.digest(RUNNER)==RUNNER_SHA
        except Exception:stable=False
        inventory={};inventory_failure=None;size=None
        try:
            size=watchdog.tree_bytes(attempt)
            for p in sorted(attempt.rglob('*')):
                if p.is_file() and not p.is_symlink():inventory[str(p.relative_to(attempt))]={'sha256':prior.digest(p),'bytes':p.stat().st_size}
        except Exception as error:inventory_failure={'type':type(error).__name__,'message':str(error)}
        available=stable and inventory_failure is None and checker is not None and checker['status']=='EXECUTION_EXIT_ZERO'
        receipt={'schema':'bounded-sequential-attempt-v1','producer':producer,'checker':checker,'source_and_input_pins_stable':stable,'checker_output_available':available,'certificate_status':'VALIDATION_OUTPUT_AVAILABLE' if available else 'NO_COMPLETED_CERTIFICATE','failure':failure,'inventory_failure':inventory_failure,'inventory':inventory,'bytes_before_terminal':size,'request_sha256':request_sha,'source_manifest_sha256':manifest_sha}
        prior.dump_new(attempt/'TERMINAL.json',receipt)
    return receipt

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--request',required=True);p.add_argument('--request-sha256',required=True);p.add_argument('--attempt',required=True);p.add_argument('--source-manifest',required=True);p.add_argument('--source-manifest-sha256',required=True);a=p.parse_args();print(json.dumps(run(a.request,a.request_sha256,a.attempt,a.source_manifest,a.source_manifest_sha256),indent=2))
