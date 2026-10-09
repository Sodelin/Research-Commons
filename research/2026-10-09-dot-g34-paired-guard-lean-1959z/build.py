import os,pathlib,subprocess,time,json,hashlib,sys
D=pathlib.Path(__file__).parent;R=pathlib.Path('/workspace/shared/lean-runtime-20261009');M=R/'mathlib'
paths=[D,R/'baseline181-build',M/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (M/'.lake/packages').iterdir() if p.is_dir()]
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
i=1
while (D/f'attempt{i}.json').exists():i+=1
module=sys.argv[1] if len(sys.argv)>1 else 'PairedFairGuard'; src=D/(module+'.lean');(D/f'attempt{i}.lean').write_bytes(src.read_bytes())
cmd=[str(R/'lean-4.33.1-linux/bin/lean'),'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str(D/(module+'.olean')),str(src)]
t=time.time();r=subprocess.run(cmd,cwd=D,env=env,capture_output=True,text=True,timeout=180)
(D/f'attempt{i}.stdout').write_text(r.stdout);(D/f'attempt{i}.stderr').write_text(r.stderr)
(D/f'attempt{i}.json').write_text(json.dumps(dict(command=cmd,exit_code=r.returncode,seconds=time.time()-t,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest()),indent=2))
print(r.returncode,r.stdout,r.stderr)
