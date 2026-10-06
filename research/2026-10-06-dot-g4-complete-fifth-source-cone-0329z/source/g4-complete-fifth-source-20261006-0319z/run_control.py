"""One complete natural fifth-source derivation; no parameter search or retry."""
import hashlib,json,os,resource,signal,subprocess,sys,time
from pathlib import Path
BASE=Path(__file__).resolve().parent
PINS={'derive_fifth.py': '1fae51171639a4cf115a549568c4e817c7376fbb5800f814f8e2aad86ec345bf', 'test_fifth.py': 'b73ecb1c54416e65841a8b4b197549ac9b958fa0e8e7e2a5874c8079613ad700', 'UNIFORM-SOURCE-REDUCTION.md': '036749108dd08a58299f623796a14ecc578b0b3a7f0a8c0659d471877775ab17', 'EXECUTION-PLAN.md': 'a0e6ec4ea3d1533bac4a0b8328d235c831c4cd0560814c098daf3dc836e3c6de'}
PROVIDERS={'../g4-rare-route-fixed-functional-20261006-0204z/check_rare.py':'d462babef7afd0b5f6fa6c74328a6df9b2d31576e50e4832caef3c63fe137788','../g4-rare-linked-history-20261006-0224z/CONNECTED-SUPPORT-CANDIDATE.md':'fc87e7ce3dca675cb3d761215a31505a3e1cc1f56e0ecebca12a646d1c7e3ded','../g4-rare-linked-history-20261006-0224z/GENERAL-QUARTIC-BALANCE-CANDIDATE.md':'45ed9fa8dc154842ef495fa02492f67c88f8f7df630351ce54054268ff56b072','../g4-rare-linked-history-20261006-0224z/FIFTH-STAGE-COUPLED-REDUCTION-WORKING.md':'12725a66a79b0116cd5e7562b0caa9c9a5d3051ac4c36d7a3dbf18bef1e2be80','../g4-complete-weight30-cone-20261005-2332z/check_weight30.py':'cfaea34e1da58d8a1e14a003bdafc4ceccc074ec2392dc42f689cd4d5440c2f5','../g4-fifth-source-cone-20261005-2246z/check_source_premises.py':'51c876c74fe53ba198aadcd6179f8eb7e0669ae59914459b5417485f21d9ab17','../g4-coherent-sixth-jet-20261005-2058z/source_coefficients.py':'aed745dd0d3fc37a8b5eef838f000675ad3fb6c37a66116f14eacfe01192f998','../g4-lossless-resonance-20261005-2042z/lossless_resonance.py':'3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def authenticate():
    for name,pin in {**PINS,**PROVIDERS}.items():
        p=BASE/name
        if p.is_symlink() or sha(p)!=pin:raise ValueError('frozen source changed')
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
    resource.setrlimit(resource.RLIMIT_FSIZE,(8*1024**2,)*2)
def run():
    authenticate();out=BASE/'attempt1';out.mkdir(exist_ok=False)
    proc=None;error=None;exit_code=None;stable=False;start=time.monotonic()
    try:
        (out/'BEFORE.json').write_text(json.dumps({'source_pins':PINS,'provider_pins':PROVIDERS},sort_keys=True,indent=2)+'\n')
        with (out/'RESULT.json').open('xb') as stdout,(out/'stderr').open('xb') as stderr:
            proc=subprocess.Popen([sys.executable,str(BASE/'derive_fifth.py')],stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=limits,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'})
            exit_code=proc.wait(timeout=30)
        authenticate();stable=True
    except Exception as exc:error={'type':type(exc).__name__,'reason':str(exc)}
    finally:
        if proc is not None:
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            proc.wait()
        inventory={};inventory_error=None
        try:
            for p in out.iterdir():
                if p.is_symlink():raise ValueError('unexpected output symlink')
                if p.is_file():inventory[p.name]={'sha256':sha(p),'bytes':p.stat().st_size}
        except Exception as exc:inventory_error={'type':type(exc).__name__,'reason':str(exc)}
        terminal={'exit_code':exit_code,'error':error,'inventory_error':inventory_error,'pins_stable':stable,'elapsed_seconds':time.monotonic()-start,'source_pins':PINS,'provider_pins':PROVIDERS,'runner_sha256':sha(Path(__file__)),'bounds':{'address_bytes':512*1024**2,'wall_seconds':30,'per_output_file_bytes':8*1024**2},'inventory':inventory}
        (out/'TERMINAL.json').write_text(json.dumps(terminal,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':run()
