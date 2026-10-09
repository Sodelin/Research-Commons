"""Serialized G5 source build; invoke only after the shared slot is released."""
import hashlib,json,os,pathlib,subprocess,sys,time
R=pathlib.Path('/workspace/shared/g5-modular-integration-20261009-1754z')
T=pathlib.Path('/workspace/shared/lean-runtime-20261009')
S=R/'sources'; B=R/'build'; E=R/'evidence'; B.mkdir(exist_ok=True);E.mkdir(exist_ok=True)
order=['UnifiedLean.Source.SourceCrossCarrierNatural','G5OriginalProgramSurvival','G5OriginalSelectedPosterior','G5OriginalConditionedContinuation','G5ActualNoMergerReadout','G5SelectedSingletonCarrier','G5SelectedDiscreteSurvival','G5SelectedSingletonRates','G5TriplePartitionReadout','G5ActualTripleMoments','G5TripleMomentReconstruction','G5ActualFrozenTripleRow','G5ActualPosteriorGerm','G5IntegrationAudit']
M=T/'mathlib';paths=[B,T/'baseline181-build',M/'.lake/build/lib/lean']+[x/'.lake/build/lib/lean' for x in (M/'.lake/packages').iterdir() if x.is_dir()]
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)),PATH=str(T/'lean-4.33.1-linux/bin')+':'+os.environ['PATH'])
selected=sys.argv[1:] or order
records=[]
for mod in selected:
 assert mod in order
 p=S/(mod.replace('.','/')+'.lean'); o=B/(mod.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
 stamp=time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())+'-'+str(time.time_ns()%1000000)
 label=stamp+'-'+mod;cmd=[str(T/'lean-4.33.1-linux/bin/lean'),'--trust=0','-j1','-M4096','-Ddebug.skipKernelTC=false','-o',str(o),str(p)]
 start=time.time()
 with open(E/(label+'.stdout'),'w') as out,open(E/(label+'.stderr'),'w') as err:
  try: q=subprocess.run(cmd,cwd=S,env=env,stdout=out,stderr=err,timeout=180);code=q.returncode
  except subprocess.TimeoutExpired: code=124
 rec={'module':mod,'command':cmd,'exit_code':code,'seconds':time.time()-start,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'object_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if code==0 and o.exists() else None,'stdout':label+'.stdout','stderr':label+'.stderr'}
 (E/(label+'.json')).write_text(json.dumps(rec,indent=2)+'\n');records.append(rec)
 print(json.dumps(rec),flush=True)
 if code: raise SystemExit(code)
(E/(stamp+'-batch.json')).write_text(json.dumps({'records':records,'mathlib':'official cache','baseline':'separate fresh verified source objects','full_axiom_audit':'pending'},indent=2)+'\n')
