"""Sample one failed compiler process without changing its resource ceilings."""
from pathlib import Path
import json
import subprocess
import sys
import time

from build_mathlib_serial import setup


def main():
    mathlib,lean_bin,state,out=map(Path,sys.argv[1:5])
    index=int(sys.argv[5])
    out.mkdir(parents=True,exist_ok=False)
    _,_,env=setup(mathlib,lean_bin)
    row=json.loads((state/'PLAN.json').read_text())['modules'][index]
    cmd=[str(lean_bin/'lean'),'-j','1','-s','8192','-R',row['repo'],
         '-o',str(out/'diagnostic.olean'),row['source']]
    samples=[]
    with (out/'stdout').open('xb') as stdout,(out/'stderr').open('xb') as stderr:
        child=subprocess.Popen(cmd,cwd=row['repo'],env=env,stdout=stdout,stderr=stderr)
        started=time.monotonic()
        while child.poll() is None:
            try:
                lines=Path(f'/proc/{child.pid}/status').read_text().splitlines()
                sample={k:int(v.split()[0])*1024 for line in lines if ':' in line
                        for k,v in [line.split(':',1)] if k in {'VmPeak','VmSize','VmRSS','RssAnon','RssFile'}}
                sample['seconds']=time.monotonic()-started
                samples.append(sample)
            except FileNotFoundError:
                break
            time.sleep(0.01)
        code=child.wait()
    result=dict(command=cmd,exit_code=code,samples=samples,
                maxima={k:max(s.get(k,0) for s in samples) for k in ['VmPeak','VmSize','VmRSS','RssAnon','RssFile']})
    (out/'DIAGNOSIS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='samples'}))
    return 0 if code==0 else 1


if __name__=='__main__':
    raise SystemExit(main())
