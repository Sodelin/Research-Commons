import hashlib,json,os,pathlib,subprocess,time,shutil
setup=pathlib.Path('/workspace/tooling-delivery/setup');cand=setup/'jc-candidate'; m=json.load(open(cand/'SOURCE-MANIFEST.json')); plan=json.load(open(setup/'source-preparation-after-full60-intake.json')); snap=json.load(open(cand/'context-snapshot.json')); done={r['module'] for r in snap['objects']}; expected=m['selected_project_dependencies']; assert len(expected)==170
stage=pathlib.Path('/workspace/solver-overlay/lean'); generated=stage/'.generated'; work=pathlib.Path('/workspace/jc-check'); outroot=work/'lib'; source=work/'source/ResearchCommons/MSCI/JC69Factorization.lean';source.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(cand/'ResearchCommons/MSCI/JC69Factorization.lean',source);assert hashlib.sha256(source.read_bytes()).hexdigest()==m['sha256']
lean='/workspace/toolchains/lean-4.33.1-linux/bin/lean';lake='/workspace/toolchains/lean-4.33.1-linux/bin/lake';env=os.environ.copy();env['PATH']='/workspace/toolchains/lean-4.33.1-linux/bin:'+env['PATH'];orig=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=stage,env=env,text=True).strip();overlay=pathlib.Path('/workspace/cache-candidate-ingest/overlay');env['LEAN_PATH']=str(outroot)+':'+':'.join(str(overlay/p/'lib/lean') for p in ['mathlib','batteries','proofwidgets'])+':'+orig
queue=[n for n in plan['order'] if n in expected and n not in done];assert len(queue)==43; queue.append('ResearchCommons.MSCI.JC69Factorization'); deadline=time.monotonic()+300;records=[]
for name in queue:
 rel=pathlib.Path(*name.split('.')); candidate=name=='ResearchCommons.MSCI.JC69Factorization'; src=source if candidate else generated/rel.with_suffix('.lean');assert hashlib.sha256(src.read_bytes()).hexdigest()==(m['sha256'] if candidate else expected[name]),name
 obj=outroot/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);remaining=deadline-time.monotonic()
 if remaining<=0:break
 cmd=[lean,'-j1','-M6144','-Ddebug.skipKernelTC=false','--root='+str(work/'source' if candidate else generated),'-o',str(obj),str(src)];started=time.monotonic()
 try:r=subprocess.run(cmd,cwd=stage,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=remaining)
 except subprocess.TimeoutExpired:records.append({'module':name,'status':'timeout'});break
 record={'module':name,'exit':r.returncode,'seconds':time.monotonic()-started,'output':r.stdout,'source_sha256':m['sha256'] if candidate else expected[name], 'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None};records.append(record);print(name, r.returncode,flush=True);(cand/'compile-context-results.json').write_text(json.dumps({'status':'RUNNING','records':records},indent=2)+'\n')
 if r.returncode:break
status='COMPLETED' if len(records)==len(queue) and records[-1].get('exit')==0 else ('FAILED' if records and records[-1].get('exit') not in (None,0) else 'TIME_BOUND')
(cand/'compile-context-results.json').write_text(json.dumps({'status':status,'selected_project_dependencies':170,'reused_receipt_verified':len(done),'records':records},indent=2)+'\n')
