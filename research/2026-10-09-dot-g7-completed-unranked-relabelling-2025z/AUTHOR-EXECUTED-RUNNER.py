from pathlib import Path
import hashlib,json,os,subprocess,sys,time
P=Path(__file__).resolve().parent; R=Path('/workspace/shared/lean-runtime-20261009'); M=R/'mathlib'
module,label=sys.argv[1:3]; source=P/'sources'/(module+'.lean'); output=P/'build'/(module+'.olean')
paths=[P/'build',R/'baseline181-build',M/'.lake/build/lib/lean']+[x/'.lake/build/lib/lean' for x in (M/'.lake/packages').iterdir() if x.is_dir()]
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)),PATH=str(R/'lean-4.33.1-linux/bin')+':'+os.environ['PATH'])
cmd=[str(R/'lean-4.33.1-linux/bin/lean'),'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str(output),str(source)]
(P/'evidence'/(label+'.source.lean')).write_bytes(source.read_bytes())
t=time.time()
with (P/'evidence'/(label+'.stdout')).open('w') as out,(P/'evidence'/(label+'.stderr')).open('w') as err:
 try: code=subprocess.run(cmd,cwd=P/'sources',env=env,stdout=out,stderr=err,timeout=180).returncode
 except subprocess.TimeoutExpired: code=124
receipt={'module':module,'status':'ELABORATION_PASS' if code==0 else 'FAILED','exit_code':code,'seconds':time.time()-t,'command':cmd,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(output.read_bytes()).hexdigest() if code==0 and output.exists() else None}
(P/'evidence'/(label+'.json')).write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));print((P/'evidence'/(label+'.stdout')).read_text());print((P/'evidence'/(label+'.stderr')).read_text());sys.exit(code)
