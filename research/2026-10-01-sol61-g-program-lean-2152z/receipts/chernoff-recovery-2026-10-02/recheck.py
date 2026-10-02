import os,pathlib,subprocess,time,hashlib,json,resource,datetime
B=pathlib.Path('/workspace/shared/lean-formalization'); O=pathlib.Path('/tmp/chernoff-recovery'); H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[O,B/'build/objects',B/'build/mathlib/.lake/build/lib/lean']+list((B/'build/mathlib/.lake/packages').glob('*/.lake/build/lib/lean')))); rows=[]
for name in ['ExponentialClockMoments','KingmanFiniteClockTail','KingmanFiniteChernoff']:
 src=B/'program'/f'{name}.lean'; cmd=['timeout','120',str(B/'tooling/lean-4.33.1-linux/bin/lean'),'-j1','-M4096','-o',str(O/f'{name}.olean'),src.name];t=time.monotonic()
 with (O/f'{name}-recheck.log').open('w') as f:r=subprocess.run(cmd,cwd=src.parent,env=env,stdout=f,stderr=subprocess.STDOUT)
 a={'module':name,'exit_code':r.returncode,'command':cmd,'elapsed_seconds':time.monotonic()-t,'source_sha256':H(src),'log_sha256':H(O/f'{name}-recheck.log')};
 if r.returncode==0:a['olean_sha256']=H(O/f'{name}.olean');a['matches_existing_object']=a['olean_sha256']==H(B/'build/objects'/f'{name}.olean')
 rows.append(a)
 if r.returncode:break
receipt={'status':'PASS_THREE_COMPONENT_RECHECK' if len(rows)==3 and all(x['exit_code']==0 for x in rows) else 'FAILED','verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'child_max_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'compiler':'Lean4.33.1 Linux commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6','mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474','scope':'Recompiled three source modules sequentially into isolated object directory; other imports use existing local builds. Not a full dependency or legacy rebuild.','results':rows};(O/'three-component-recheck.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
