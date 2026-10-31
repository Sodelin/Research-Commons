import test from 'node:test';import assert from 'node:assert/strict';
import {readFile,mkdtemp,writeFile,rm,chmod} from 'node:fs/promises';
import {tmpdir} from 'node:os';import {join} from 'node:path';import {execFileSync,spawnSync} from 'node:child_process';import {fileURLToPath} from 'node:url';
import {identity} from '../tools/source-cache.mjs';import {mergeSources,validateCorpus} from '../tools/source-merge.mjs';
import {loadPackage,solverBinding,coverageLedger,solverSearchCards,packageFile,supportedRepositoryOrigin,canonicalSourceURL,searchPackageModules} from '../tools/solver-bindings.mjs';
import {readObservations} from '../tools/check-observations.mjs';
import {classifyCheck} from '../tools/check-result.mjs';import {search} from '../dist/model.mjs';import {searchSources} from '../dist/source-search.mjs';
const root=new URL('../',import.meta.url),tool=n=>fileURLToPath(new URL(`tools/${n}`,root));
const data=JSON.parse(await readFile(new URL('dist/claims.json',root)));
test('new proof body is discoverable with exactly unchanged claim cards and immutable identity',()=>{
 const before=JSON.stringify(data);const body='# New supplier\nUniqueNewSupplierLemma retained observer and same bank.\n';
 const base=Buffer.from(JSON.stringify({schema:1,coverage:{indexed:0,limitation:'Selected.'},documents:[]}));
 const supplement={schema:1,base_corpus_sha256:identity(base).sha256,source_delta:{from:'a'.repeat(40),to:'b'.repeat(40)},documents:[{url:`https://github.com/Sodelin/Research-Commons/blob/${'b'.repeat(40)}/research/new-proof.md`,title:'New supplier',body,...identity(Buffer.from(body)),bindings:[{role:'git_tree_delta_source',label:'No acceptance inferred'}]}]};
 const merged=mergeSources(base,supplement),hit=searchSources(merged,'UniqueNewSupplierLemma');
 assert.equal(hit.length,1);assert(!hit[0].bindings.some(b=>b.claim_id));assert.equal(JSON.stringify(data),before);assert.deepEqual(merged.coverage.supplements[0].source_delta,supplement.source_delta);
 assert.throws(()=>mergeSources(Buffer.from('{}'),supplement),/base/);
 const changed=structuredClone(supplement);changed.documents[0].body+='tamper';assert.throws(()=>mergeSources(base,changed),/identity/);
 assert.throws(()=>validateCorpus({...merged,documents:[...merged.documents,...merged.documents]}),/Duplicate/);
});
test('source-only path identifiers resolve even when absent from body and canonical cards',()=>{
 const url=`https://github.com/Sodelin/Research-Commons/blob/${'a'.repeat(40)}/research/unique-supplier-path-key/README.md`;
 const document={url,title:'Scoped report',body:'Existing bounded result; no master acceptance.',bindings:[{role:'git_tree_delta_source',label:'Source navigation only'}]};
 const before=JSON.stringify(data);assert.equal(searchSources({documents:[document]},'unique-supplier-path-key')[0].url,url);
 assert.equal(JSON.stringify(data),before);assert.equal(document.bindings[0].claim_id,undefined);
});
test('successful process exit cannot replace complete kernel/source/owner evidence',()=>{
 const binding={claim_id:'C',lean:{module:'M',declarations:['M.d']},declarations:[{name:'M.d',owner:'M'}]};
 const pkg={modules:new Map([['M',{sha256:'a'.repeat(64),imports:['Base']}],['Base',{sha256:'b'.repeat(64),imports:['Mathlib.Data.Nat.Basic']}],['Extra',{sha256:'c'.repeat(64),imports:['Base']}]])};
 const record={kernel_check_passed:true,exact_source_context_and_owned_audit_revalidated:true,all_claims_formalized:false,target:'M',claims:[{claim_id:'C',declarations:['M.d'],declaration_modules:{'M.d':'M'}}],checked_modules:['Base','M'],module_hashes:{M:'a'.repeat(64),Base:'b'.repeat(64)}};
 const result=r=>({exit_code:0,stdout:'Lean output\n'+JSON.stringify(r)});
 assert.equal(classifyCheck(result(record),binding,pkg).outcome,'CHECKED_SCOPED_DECLARATIONS');
 const omitted={...record,checked_modules:['M'],module_hashes:{M:'a'.repeat(64)}};
 assert.equal(classifyCheck(result(omitted),binding,pkg).outcome,'UNKNOWN');
 assert.match(classifyCheck(result(omitted),binding,pkg).blockers[0],/dependency/);
 assert.equal(classifyCheck(result({...record,checked_modules:['Base','M','M']}),binding,pkg).outcome,'UNKNOWN');
 const larger={...record,checked_modules:['Base','M','Extra'],module_hashes:{...record.module_hashes,Extra:'c'.repeat(64)}};
 assert.equal(classifyCheck(result(larger),binding,pkg).outcome,'CHECKED_SCOPED_DECLARATIONS');
 const deletedProject={modules:new Map(pkg.modules)};deletedProject.modules.delete('Base');
 assert.equal(classifyCheck(result(omitted),binding,deletedProject).outcome,'UNKNOWN');
 assert.match(classifyCheck(result(omitted),binding,deletedProject).blockers[0],/Unknown missing project import/);
 const lookalikeProvider={modules:new Map([['M',{sha256:'a'.repeat(64),imports:['MathlibProjectMissing']} ]])};
 assert.equal(classifyCheck(result(omitted),binding,lookalikeProvider).outcome,'UNKNOWN');
 for(const bad of [{}, {...record,kernel_check_passed:false},{...record,target:'Wrong'},{...record,module_hashes:{M:'b'.repeat(64)}},{...record,claims:[]},{...record,all_claims_formalized:true}])assert.equal(classifyCheck(result(bad),binding,pkg).outcome,'UNKNOWN');
 assert.equal(classifyCheck({...result(record),exit_code:2},binding,pkg).outcome,'UNKNOWN');
 assert.equal(classifyCheck({...result(record),signal:'SIGKILL'},binding,pkg).outcome,'UNKNOWN');
});
test('observation correspondence is explicitly limited to listed metadata, even after runtime changes',async()=>{
 const directory=await mkdtemp(join(tmpdir(),'observation-scope-'));
 try{const path=join(directory,'result.json'),files=[{path:'integration/claims.json',sha256:'a'.repeat(64)}];
  await writeFile(path,JSON.stringify({schema:1,record_kind:'bounded_declaration_check_observation',claim_id:'C',outcome:'UNKNOWN',package_source:{files,runtime_sha256:'old'}}));
  const [record]=await readObservations([path],{cards:new Map([['C',{}]]),identity:{files,runtime_sha256:'changed'}});
  assert.equal(record.current_package_metadata_files_match,true);assert(!Object.hasOwn(record,'current_package_inputs_match'));
  assert.match(record.identity_match_scope,/does not establish correspondence of checker\/runtime\/Cargo\/toolchain/);
 }finally{await rm(directory,{recursive:true,force:true});}
});
test('unrelated clean checkouts and noncanonical package paths cannot acquire canonical source URLs',()=>{
 assert.equal(supportedRepositoryOrigin('https://github.com/other/Research-Commons.git'),false);
 assert.equal(supportedRepositoryOrigin('https://github.com/Sodelin/Research-Commons.evil.git'),false);
 const checkout={commit:'a'.repeat(40),package_worktree_clean:true,supported_repository_origin:false,canonical_package_path:true};
 assert.equal(canonicalSourceURL(checkout,'lean/M.lean'),null);
 assert.equal(canonicalSourceURL({...checkout,supported_repository_origin:true,canonical_package_path:false},'lean/M.lean'),null);
 assert.match(canonicalSourceURL({...checkout,supported_repository_origin:true},'lean/M.lean'),/Sodelin\/Research-Commons\/blob\/a{40}\/packages\/research\/lean\/M.lean$/);
});
test('exact module evidence and unbound supplier names are discoverable without inventing claim acceptance',()=>{
 const before=JSON.stringify(data),source={module:'Supplier',path:'lean/Supplier.lean',sha256:'a'.repeat(64),imports:[]};
 const evidence={source_module:'Supplier',source_sha256:source.sha256,selected_names:['Supplier.exact_endpoint'],source_modules:60,full1500_build_passed:false,whole118_complete:false};
 const pkg={modules:new Map([['Supplier',source]]),rows:new Map(),externalEvidence:new Map([['Supplier',evidence]])};
 const hits=searchPackageModules(pkg,'Supplier.exact_endpoint');assert.equal(hits.length,1);assert.equal(hits[0].module,'Supplier');
 assert.deepEqual(hits[0].direct_named_claim_bindings,[]);assert.equal(hits[0].external_context_evidence.full1500_build_passed,false);
 assert.match(hits[0].scope,/does not establish a canonical claim/);assert.equal(JSON.stringify(data),before);
});
test('exact declaration lookup hands off to the existing checker and all claims remain in ledger',{skip:!process.env.RESEARCH_PACKAGE_ROOT},async()=>{
 const pkg=await loadPackage(process.env.RESEARCH_PACKAGE_ROOT),ledger=coverageLedger(data.claims,pkg);
 assert.equal(ledger.rows.length,118);assert.equal(ledger.all_current_claims_accounted_for,true);assert.equal(ledger.full_package_complete,null);
 assert.equal(pkg.modules.size,1833);
 const card=data.claims.find(c=>c.id==='CB-MEMORY-004'),b=solverBinding(card,pkg);
 assert(b.declarations.length>0);assert(b.declarations.every(d=>d.source.sha256.length===64));
 assert(b.declarations.some(d=>d.historical_types.some(t=>/EventRate/.test(t.printed_type))));
 const nanuq=solverBinding(data.claims.find(c=>c.id==='CB-NANUQ-002'),pkg);
 assert(nanuq.declarations.find(d=>d.name==='ResearchCommons.Claims.NANUQ.raw_tensor_eq_actual').historical_types.some(t=>/rawRho/.test(t.printed_type)));
 const exact=b.declarations[0].name;assert(search(solverSearchCards(data.claims,pkg),{q:exact}).some(c=>c.id===card.id));
 assert.deepEqual(b.check.args.slice(-4),['--target',b.lean.module,'--claim',card.id]);assert(b.check.args.includes('--offline'));
 const open=ledger.rows.find(r=>r.claim_id==='CB-G3-004');assert.equal(open.mathematical_status,data.claims.find(c=>c.id===open.claim_id).mathematical_status);
 await assert.rejects(packageFile(pkg.root,'../../etc/passwd'),/Unsafe/);
 const out=JSON.parse(execFileSync(process.execPath,[tool('query.mjs'),'--package-root',pkg.root,'--query',exact,'--limit','1'],{encoding:'utf8',maxBuffer:4*1024*1024}));
 assert.equal(out.results[0].claim_id,card.id);assert.equal(out.results[0].solver.declarations[0].name,exact);
 if(pkg.externalEvidence.has('DiscriminatingStatusTransport')){
  assert.equal([...pkg.externalEvidence.values()].filter(r=>r.source_module==='DiscriminatingStatusTransport').length,60);
  assert.deepEqual(pkg.externalEvidence.get('FiniteDependencyInduction').selected_names,[]);
  assert.equal(pkg.externalEvidence.get('FiniteDependencyInduction').module_member_sha256,pkg.modules.get('FiniteDependencyInduction').sha256);
  const moduleResult=JSON.parse(execFileSync(process.execPath,[tool('query.mjs'),'--modules','--package-root',pkg.root,'--query','RestrictedCausal.DiscriminatingStatus.witness_status_transfer','--limit','1'],{encoding:'utf8',maxBuffer:4*1024*1024}));
  assert.equal(moduleResult.total,1);
  assert.equal(moduleResult.results[0].module,'DiscriminatingStatusTransport');
  assert.equal(moduleResult.results[0].external_context_evidence.owned_declarations,1549);
  assert.equal(moduleResult.results[0].external_context_evidence.full1500_build_passed,false);
  const facetRefusal=spawnSync(process.execPath,[tool('query.mjs'),'--modules','--package-root',pkg.root,'--topic','G3'],{encoding:'utf8'});assert.notEqual(facetRefusal.status,0);assert.equal(facetRefusal.stdout,'');
 }
 const directory=await mkdtemp(join(tmpdir(),'check-result-preserve-'));
 try{const path=join(directory,'existing.json');await writeFile(path,'preserve');
  const refusal=spawnSync(process.execPath,[tool('check-claim.mjs'),'--package-root',pkg.root,'--claim',card.id,'--execute','--receipt',path],{encoding:'utf8'});
  assert.notEqual(refusal.status,0);assert.match(refusal.stderr,/EEXIST/);assert.equal(refusal.stdout,'');assert.equal(await readFile(path,'utf8'),'preserve');
 }finally{await rm(directory,{recursive:true,force:true});}
 const fakeGit=await mkdtemp(join(tmpdir(),'unrelated-git-'));
 try{
  await writeFile(join(fakeGit,'git'),'#!/bin/sh\ncase "$3:$4" in\nrev-parse:HEAD) printf "%s\\n" "$MOCK_COMMIT";;\nstatus:--porcelain) exit 0;;\nremote:get-url) printf "%s\\n" "https://github.com/unrelated/repository.git";;\nrev-parse:--show-toplevel) printf "%s\\n" "$MOCK_REPO_TOP";;\n*) exit 1;;\nesac\n');
  await chmod(join(fakeGit,'git'),0o700);
  const source=new URL('../tools/solver-bindings.mjs',import.meta.url).href;
  const script=`import {loadPackage} from ${JSON.stringify(source)};const p=await loadPackage(process.env.RESEARCH_PACKAGE_ROOT);console.log(JSON.stringify({checkout:p.identity.checkout,urls:[...p.modules.values()].filter(m=>m.url).length}));`;
  const actual=JSON.parse(execFileSync(process.execPath,['--input-type=module','-e',script],{encoding:'utf8',env:{...process.env,PATH:fakeGit+':'+process.env.PATH,MOCK_COMMIT:'a'.repeat(40),MOCK_REPO_TOP:pkg.root.replace(/\/packages\/research$/,'')}}));
  assert.equal(actual.checkout.package_worktree_clean,true);assert.equal(actual.checkout.supported_repository_origin,false);assert.equal(actual.urls,0);
 }finally{await rm(fakeGit,{recursive:true,force:true});}
});
test('offline merger refuses existing output and leaves original bytes intact',async()=>{
 const directory=await mkdtemp(join(tmpdir(),'source-merge-'));
 try{
  const base=Buffer.from(JSON.stringify({schema:1,coverage:{limitation:'Selected'},documents:[]}));
  const supplement={schema:1,base_corpus_sha256:identity(base).sha256,documents:[]};
  await writeFile(join(directory,'base'),base);await writeFile(join(directory,'supp'),JSON.stringify(supplement));await writeFile(join(directory,'output'),'preserve');
  const result=spawnSync(process.execPath,[tool('merge-sources.mjs'),join(directory,'base'),join(directory,'supp'),join(directory,'output')],{encoding:'utf8'});
  assert.notEqual(result.status,0);assert.equal(await readFile(join(directory,'output'),'utf8'),'preserve');assert.deepEqual(await readFile(join(directory,'base')),base);
 }finally{await rm(directory,{recursive:true,force:true});}
});
