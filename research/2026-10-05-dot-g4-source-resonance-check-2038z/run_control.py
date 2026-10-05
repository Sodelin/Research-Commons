"""One bounded exact resonance control; no automatic retry."""
import hashlib,json,os,resource,signal,subprocess,sys,time
from pathlib import Path
BASE=Path(__file__).resolve().parent
PINS={'resonance.py':'ede62afabb8533eb941786bea7575b67c0a008034f364366a7eea378047f50ec','test_resonance.py':'2d96edebed3c0be540c287e00d06cfe0f1103cd6858415e532905215b95e09a3','CONTRACT-AND-INTERTWINING.md':'95d7aded991438364face485a7cfd4eb775566671039ffc3f16c0def6df821d0'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def authenticate():
    for name,pin in PINS.items():
        if (BASE/name).is_symlink() or sha(BASE/name)!=pin:raise ValueError('frozen source changed')
def limits():
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_FSIZE,(8*1024**2,)*2)
def run():
    authenticate();out=BASE/'attempt1';out.mkdir(exist_ok=False);proc=None;error=None;exit_code=None;start=time.monotonic();stable=False
    try:
        (out/'BEFORE.json').write_text(json.dumps(PINS,sort_keys=True,indent=2)+'\n')
        with (out/'RESULT.json').open('xb') as stdout,(out/'stderr').open('xb') as stderr:
            proc=subprocess.Popen([sys.executable,str(BASE/'resonance.py')],stdout=stdout,stderr=stderr,start_new_session=True,preexec_fn=limits,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'})
            exit_code=proc.wait(timeout=30)
        authenticate();stable=True
    except Exception as exc:error={'type':type(exc).__name__,'reason':str(exc)}
    finally:
        if proc is not None:
            try:os.killpg(proc.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            proc.wait()
        inv={p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in out.iterdir() if p.is_file()}
        (out/'TERMINAL.json').write_text(json.dumps({'exit_code':exit_code,'error':error,'pins_stable':stable,'elapsed_seconds':time.monotonic()-start,'source_pins':PINS,'runner_sha256':sha(Path(__file__)),'bounds':{'address_bytes':512*1024**2,'wall_seconds':30,'per_output_file_bytes':8*1024**2},'inventory':inv},sort_keys=True,indent=2)+'\n')
if __name__=='__main__':run()
