import pathlib,os,subprocess,json,time,hashlib,sys
R=pathlib.Path(__file__).resolve().parent;T=pathlib.Path('/workspace/shared/lean-runtime-20261009');M=T/'mathlib';mod=sys.argv[1];label=sys.argv[2];p=R/'recovered-timed-sources'/f'{mod}.lean'
paths=[R/'build',pathlib.Path('/workspace/shared/g5-literal-cut-integration-20261009-1855z/clean-replay-v1/build'),pathlib.Path('/workspace/shared/g5-timed-provider-reuse-20261009-1925z/build'),pathlib.Path('/workspace/shared/g5-modular-integration-20261009-1754z/build'),T/'baseline181-build',M/'.lake/build/lib/lean']+[x/'.lake/build/lib/lean' for x in (M/'.lake/packages').iterdir() if x.is_dir()]
cmd=[str(T/'lean-4.33.1-linux/bin/lean'),'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str(R/'build'/f'{mod}.olean'),str(p)];start=time.time();(R/'evidence'/f'{label}.lean').write_bytes(p.read_bytes())
q=subprocess.run(cmd,cwd=R/'recovered-timed-sources',env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths))),capture_output=True,text=True,timeout=240)
for k,v in [('stdout',q.stdout),('stderr',q.stderr)]: (R/'evidence'/f'{label}.{k}').write_text(v)
r={'command':cmd,'exit_code':q.returncode,'seconds':time.time()-start,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()};(R/'evidence'/f'{label}.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));print(q.stdout);print(q.stderr);sys.exit(q.returncode)
