from pathlib import Path
import sys,re,json,hashlib,subprocess,base64,gzip,shutil,collections
repo=Path('/workspace/cloud-lean');run_id=sys.argv[1];commit=sys.argv[2];packet=repo/'research/2026-10-07-cloud-g6-sol-ultra-1601z'
sha=lambda b:hashlib.sha256(b).hexdigest()
snapshot=Path('/tmp/g6-frozen-'+commit)
snapshot_readback=json.loads((snapshot/'source-readback.json').read_text());assert snapshot_readback['commit']==commit
def frozen_bytes(path):
 data=(snapshot/path).read_bytes();assert sha(data)==snapshot_readback['files'][path],path
 return data

metadata=json.loads(Path('/tmp/g6-run-'+run_id+'.json').read_text());assert metadata['head_sha']==commit and metadata['status']=='completed';result='PASS' if metadata['conclusion']=='success' else 'FAILED'
evidence=packet/'verification/evidence'/('g6-run-'+run_id+'-'+result);evidence.mkdir(parents=True,exist_ok=True)
lines=[re.sub(r'^.*?\t.*?\t\S+\s','',line) for line in Path('/tmp/g6-run-'+run_id+'.log').read_text(encoding='utf-8-sig').splitlines()]
inputs=next(json.loads(line[10:]) for line in lines if line.startswith('G6_INPUTS '));assert inputs['source_commit']==commit
plan_name=sys.argv[3] if len(sys.argv)>3 else 'finite-tag-bin-clock-ownership.json';plan=json.loads(frozen_bytes('research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/freeze-plans/'+plan_name));assert set(inputs['modules'])==set(plan['modules'])
sources={};source_readback={}
for name,record in inputs['modules'].items():
 path=plan['modules'][name]['repository_path'];data=frozen_bytes(path)
 assert sha(data)==record['sha256']==plan['modules'][name]['sha256'],name
 sources[name]=data.decode();source_readback[name]={'repository_path':path,'sha256':sha(data)}
receipts=[json.loads(line[11:]) for line in lines if line.startswith('G6_RECEIPT ')];outputs={};stdout_readback={};failed=[]
for i,line in enumerate(lines):
 if not line.startswith('G6_COMMAND '):continue
 command=json.loads(line[len('G6_COMMAND '):]);end=next(j for j in range(i+1,len(lines)) if lines[j].startswith('G6_RECEIPT '));receipt=json.loads(lines[end][11:]);body=lines[i+1:end];data=('\n'.join(body)+ ('\n' if body else '')).encode()
 if '-o' not in command['argv'] and not command['argv'][-1].endswith(('DeclarationAudit.lean','CompleteEnvironmentAudit.lean')):continue
 assert sha(data)==receipt['output_sha256'],(command['argv'],sha(data),receipt['output_sha256'])
 name=command['argv'][-1].rsplit('/',1)[-1];outputs[name]=data;stdout_readback[name]=sha(data)
 if receipt['exit']:failed.append({'source':name,'receipt':receipt})
 if name in {target.rsplit('.',1)[-1]+'.lean' for target in inputs['targets']} or name in ['DeclarationAudit.lean','CompleteEnvironmentAudit.lean']:(evidence/(name[:-5]+'-actual.log')).write_bytes(data)
counts=next(json.loads(line[len('CLOUD_SELECTED_AXIOM_AUDIT_PASSED '):]) for line in lines if line.startswith('CLOUD_SELECTED_AXIOM_AUDIT_PASSED '));audited=[name for name in inputs['targets'] if name in counts]
by_module={}
for name in audited:
 namespace=re.search(r'^namespace\s+(\S+)\s*$',sources[name],re.M);assert namespace
 by_module[name]=[namespace[1]+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)",sources[name],re.M)]
text=outputs['DeclarationAudit.lean'].decode();reports={name:[a.strip() for a in axioms.split(',') if a.strip()] for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)};reports.update({name:[] for name in re.findall(r"'([^']+)' does not depend on any axioms",text)})
declarations=[name for rows in by_module.values() for name in rows];assert len(set(declarations))==len(declarations);assert set(declarations)==set(reports);assert all(not(set(axes)-{'propext','Classical.choice','Quot.sound'}) for axes in reports.values());assert {name:len(rows) for name,rows in by_module.items()}==counts
named_source='\n'.join('import '+name for name in audited)+'\n\n'+'\n'.join('#print axioms '+name for name in declarations)+'\n';(evidence/'DeclarationAudit-reconstructed.lean').write_text(named_source)
payload=next(json.loads(line[len('G6_COMPLETE_ENVIRONMENT_PAYLOAD '):]) for line in lines if line.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '));begin=lines.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN');end=lines.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END');payload_rows=lines[begin+1:end]; discarded=[line for line in payload_rows if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}',line)]; raw=gzip.decompress(base64.b64decode(''.join(line for line in payload_rows if re.fullmatch(r'[A-Za-z0-9+/]+={0,2}',line))));assert len(raw)==payload['bytes'] and sha(raw)==payload['sha256'];owned=json.loads(raw)
assert not owned['owned_axioms'] and not owned['nonstandard_axiom_rows'] and not owned['missing_modules'];rows=owned['declarations'];assert owned['declaration_count']==len(rows);assert owned['theorem_declaration_count']==sum(row['kind']=='theorem' for row in rows);assert len({row['name'] for row in rows})==len(rows)
failed_names={n[:-5] for n in outputs if any(f['source']==n for f in failed)}
assert all(row['module'] in owned['selected_modules'] and 'type_references' in row and 'body_references' in row and not(set(row['axioms'])-{'propext','Classical.choice','Quot.sound'}) for row in rows)
assert set(owned['selected_modules'])<=set(inputs['modules']);assert payload['selected_custom_modules']==len(owned['selected_modules'])
if result=='PASS':assert set(owned['selected_modules'])==set(inputs['modules']) and not failed and all(receipt['exit']==0 for receipt in receipts)
template_path='research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean';template=frozen_bytes(template_path).decode();old='#['+'"NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]';assert template.count(old)==1;template=template.replace(old,'#['+', '.join(json.dumps(name) for name in owned['selected_modules'])+']');complete_source='\n'.join('import '+name for name in owned['selected_modules'])+'\n'+template;assert sha(complete_source.encode())==payload['audit_source_sha256'];(evidence/'CompleteEnvironmentAudit-reconstructed.lean').write_text(complete_source);(evidence/'complete-environment-inventory.json').write_bytes(raw)
complete_receipt={'payload':payload,'interleaved_stderr_lines':discarded,'all_owned_counts_by_module':dict(sorted(collections.Counter(row['module'] for row in rows).items())),'all_owned_counts_by_kind':dict(collections.Counter(row['kind'] for row in rows)),'complete_audit_stdout_sha256':stdout_readback['CompleteEnvironmentAudit.lean'],'inventory_source_sha256':sha(complete_source.encode()),'owned_axioms':[],'nonstandard_axiom_rows':[],'missing_modules':[]}
audit={'named_declarations':declarations,'transitive_axioms':reports,'declarations_by_module':by_module,'module_counts':counts,'named_source_sha256':sha(named_source.encode()),'named_stdout_sha256':stdout_readback['DeclarationAudit.lean'],'source_hash_readback':source_readback,'custom_and_audit_stdout_readback':stdout_readback,'failed_commands':failed,'missing_reports':[],'unexpected_axioms':{}}
for filename,obj in [('inputs-recovered.json',inputs),('receipts-recovered.json',receipts),('axiom-audit-recovered.json',audit),('complete-ownership-receipt.json',complete_receipt)]: (evidence/filename).write_text(json.dumps(obj,indent=2)+'\n')
for src,dest in [('log','actions.log'),('json','run.json'),('jobs.json','jobs.json')]:shutil.copyfile(Path('/tmp/g6-run-'+run_id+'.'+src),evidence/dest)
print(json.dumps({'path':str(evidence.relative_to(repo)),'result':result,'custom':len(inputs['modules']),'receipts':len(receipts),'zero_exits':sum(receipt['exit']==0 for receipt in receipts),'named_reports':len(reports),'named_counts':counts,'complete_payload':payload,'complete_kind_counts':complete_receipt['all_owned_counts_by_kind'],'new_target_ownership':{name:complete_receipt['all_owned_counts_by_module'].get(name,0) for name in ['FiniteTagDecoder','UnifiedLean.G6.BinClock','LiteralSameBinTrace','UnifiedLean.G6.ResidualProgram','UnifiedLean.G6.UpperMeanCommon','CompleteCalendarBinReadout','ActualTailBinRow','CompleteCalendarJointLaw']},'failed':failed,'stdout_exact':len(stdout_readback)},indent=2))
