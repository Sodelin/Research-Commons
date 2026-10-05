"""One bounded universal-identity decision; no retry or coefficient retuning."""
import hashlib,json,os,resource,signal,subprocess,sys,time
from pathlib import Path
BASE=Path(__file__).resolve().parent
PINS={'check_identity.py': 'a3ce0c82136599b07ab41ae2456abe0d2f09d8e22a7f1969a887573c5fada18a', 'test_identity.py': 'ce55e26f0b506c6e1bb2a0de8b4a814582e528130ea99fbfdcaa14ad1620487b', 'CONTRACT-AND-LOCALITY.md': 'ff9ecbc5e54804f6844b45532674088141e66182b3781b3d76630724db2c988b'}
PROVIDERS={'../g4-coherent-sixth-jet-20261005-2058z/source_coefficients.py':'aed745dd0d3fc37a8b5eef838f000675ad3fb6c37a66116f14eacfe01192f998','../g4-lossless-resonance-20261005-2042z/lossless_resonance.py':'3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be'}
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
            proc=subprocess.Popen([sys.executable,str(BASE/'check_identity.py')],stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=limits,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'})
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
