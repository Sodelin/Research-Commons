import os,pathlib,subprocess,json,time
stage=pathlib.Path('/workspace/solver-overlay/lean');ov=pathlib.Path('/workspace/cache-candidate-ingest/overlay');work=pathlib.Path('/workspace/jc-check');root=pathlib.Path('/workspace/tooling-delivery/setup/jc-candidate');lean='/workspace/toolchains/lean-4.33.1-linux/bin/lean';lake='/workspace/toolchains/lean-4.33.1-linux/bin/lake';env=os.environ.copy();env['PATH']='/workspace/toolchains/lean-4.33.1-linux/bin:'+env['PATH'];orig=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=stage,env=env,text=True).strip();env['LEAN_PATH']=str(work/'lib')+':'+':'.join(str(ov/p/'lib/lean') for p in ['mathlib','batteries','proofwidgets'])+':'+orig;summary=[]
for name in ['NamedAudit','OwnedAudit']:
 start=time.monotonic(); cmd=[lean,'-j1','-M6144','-Ddebug.skipKernelTC=false',str(root/(name+'.lean'))]
 try:r=subprocess.run(cmd,cwd=stage,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=240)
 except subprocess.TimeoutExpired:summary.append({'audit':name,'status':'TIMEOUT'});break
 (root/(name+'.log')).write_text(r.stdout);summary.append({'audit':name,'exit':r.returncode,'seconds':time.monotonic()-start});print(name,'exit',r.returncode,flush=True)
 if r.returncode:break
(root/'audit-execution.json').write_text(json.dumps({'records':summary},indent=2)+'\n')
