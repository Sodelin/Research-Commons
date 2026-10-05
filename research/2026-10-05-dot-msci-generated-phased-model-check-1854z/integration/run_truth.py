"""Bounded, once-only ideal truth arithmetic with receipt-first provenance."""
import json,sys
from pathlib import Path
import compose_run as r
BASE=Path(__file__).resolve().parent
def run(manifest,identity,attempt):
    pins=r.authenticate(manifest,identity)
    import integration_core as c
    c.load_provider();import bounded_runner as runner
    attempt=Path(attempt).absolute();attempt.mkdir(exist_ok=False);stage=None;error=None;stable=False;inv={}
    try:
        r.write_new(attempt/'BEFORE.json',{'manifest_sha256':identity,'pins':pins})
        stage=runner.stage([sys.executable,str(BASE/'evaluate_truth.py'),'--output',str(attempt/'TRUTH.json')],attempt,'truth',runner.load_watchdog(),wall=30)
        if stage['status']!='EXECUTION_EXIT_ZERO':raise ValueError('truth arithmetic did not complete')
    except Exception as exc:error={'type':type(exc).__name__,'reason':str(exc)}
    finally:
        try:stable=r.authenticate(manifest,identity)==pins
        except Exception as exc:error=error or {'type':type(exc).__name__,'reason':str(exc)}
        try:
            for path in sorted(attempt.rglob('*')):
                if path.is_symlink():raise ValueError('symlink output')
                if path.is_file():inv[str(path.relative_to(attempt))]={'bytes':path.stat().st_size,'sha256':r.digest(path)}
        except Exception as exc:error=error or {'type':type(exc).__name__,'reason':str(exc)}
        result={'schema':'one-truth-arithmetic-terminal-v1','source_manifest_sha256':identity,'pins_stable':stable,'stage':stage,'error':error,'inventory':inv}
        r.write_new(attempt/'TERMINAL.json',result)
    return result
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--manifest',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--attempt',required=True);a=p.parse_args();print(json.dumps(run(a.manifest,a.manifest_sha256,a.attempt),sort_keys=True,indent=2))
