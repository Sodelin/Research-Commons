"""Check new acquisition capability against the preserved older real binary."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'2026-10-13-astra-unified-solver-0645z'

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--old-binary',required=True)
    a=p.parse_args(); a.output.mkdir(parents=True,exist_ok=False)
    rows=[]
    for name,flag,status,code in [('python-acquisition',False,'GENERATED_AND_CHECKED',0),
                                 ('native-capability-missing',True,'UNKNOWN',2)]:
        out=a.output/name
        command=[sys.executable,'-B',str(BASE/'solve.py'),'--request',
                 str(BASE/'examples/singleton-generator.json'),'--output',str(out),
                 '--rust-binary',a.old_binary]
        if flag: command.append('--native-generation')
        r=subprocess.run(command,capture_output=True,text=True,timeout=10)
        result=json.loads((out/'RESULT.json').read_text())
        assert r.returncode==code and result['status']==status
        assert result['source_feasibility_certified'] is False
        if flag: assert result['native_generation']['agree'] is False
        rows.append(dict(name=name,status=status,exit_code=r.returncode,command=command))
    (a.output/'TEST-RESULT.json').write_text(json.dumps(dict(status='PASS',cases=rows),indent=2)+'\n')
    print(json.dumps(dict(status='PASS',cases=len(rows))))

if __name__=='__main__': main()
