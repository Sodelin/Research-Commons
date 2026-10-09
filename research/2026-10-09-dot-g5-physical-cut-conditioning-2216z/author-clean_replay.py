"""Fresh own-module sequential replay; existing provider objects are read-only."""
import pathlib,sys,shutil,subprocess,json,hashlib
R=pathlib.Path(__file__).resolve().parent;D=R/sys.argv[1];D.mkdir(exist_ok=False)
for sub in ['sources','build','evidence']:(D/sub).mkdir()
mods=['G5ActualActivatedPrefix','G5ActivatedPosteriorPlacement','G5OriginalEpochChart','G5PhysicalCutChart','G5PhysicalCutConditionalLaw','G5PhysicalCutAudit','G5OlderSideCutChart','G5OlderSideCutConditionalLaw','G5OlderSideCutAudit']
for q in (R/'build').rglob('*.olean'):
 if q.is_symlink():
  d=D/'build'/q.relative_to(R/'build');d.parent.mkdir(parents=True,exist_ok=True);d.symlink_to(q.resolve())
for m in mods:shutil.copyfile(R/'sources'/f'{m}.lean',D/'sources'/f'{m}.lean')
shutil.copyfile(R/'build_one.py',D/'build_one.py');rows=[]
for n,m in enumerate(mods):
 label=f'replay-{n+1:02}-{m}';q=subprocess.run([sys.executable,str(D/'build_one.py'),m,label],capture_output=True,text=True)
 for ext,txt in [('stdout',q.stdout),('stderr',q.stderr)]:(D/'evidence'/f'{label}.runner-{ext}').write_text(txt)
 rows.append({'module':m,'exit_code':q.returncode,'sha256':hashlib.sha256((D/'sources'/f'{m}.lean').read_bytes()).hexdigest(),'receipt':f'evidence/{label}.json'})
 (D/'CLEAN-REPLAY-RECEIPT.json').write_text(json.dumps({'sequential':True,'fresh_own_objects':True,'all_pass':len(rows)==len(mods) and all(x['exit_code']==0 for x in rows),'rows':rows},indent=2)+'\n')
 print(m,q.returncode,flush=True)
 if q.returncode:print(q.stdout,flush=True);raise SystemExit(q.returncode)
