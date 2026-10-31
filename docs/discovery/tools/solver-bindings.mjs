// Read-only projection of the existing package. Never a second completion engine.
import {readFile,readdir,realpath} from 'node:fs/promises';
import {resolve,relative,isAbsolute} from 'node:path';
import {identity} from './source-cache.mjs';
import {execFileSync} from 'node:child_process';
import {searchSources} from '../dist/source-search.mjs';

export function supportedRepositoryOrigin(origin){
 return ['https://github.com/Sodelin/Research-Commons.git','https://github.com/Sodelin/Research-Commons','git@github.com:Sodelin/Research-Commons.git'].includes(origin);
}
export function canonicalSourceURL(checkout,path){
 if(!checkout?.package_worktree_clean||!checkout?.supported_repository_origin||!checkout?.canonical_package_path||!/^[a-f0-9]{40}$/.test(checkout.commit))return null;
 return `https://github.com/Sodelin/Research-Commons/blob/${checkout.commit}/packages/research/${path}`;
}

export async function packageFile(root,path){
 if(typeof path!=='string'||isAbsolute(path)||path.split(/[\\/]/).some(p=>p==='..'||!p))throw Error('Unsafe package path');
 const full=await realpath(resolve(root,path));
 const rel=relative(root,full);if(rel==='..'||rel.startsWith('../')||isAbsolute(rel))throw Error('Package path escapes root');
 const bytes=await readFile(full);return {bytes,identity:{path,...identity(bytes)}};
}
export async function loadPackage(directory){
 const root=await realpath(resolve(directory));const files=[];
 let checkout=null;
 try{const commit=execFileSync('git',['-C',root,'rev-parse','HEAD'],{encoding:'utf8',timeout:5000,stdio:['ignore','pipe','ignore']}).trim();
  const dirty=execFileSync('git',['-C',root,'status','--porcelain','--','.'],{encoding:'utf8',timeout:5000,maxBuffer:1024*1024,stdio:['ignore','pipe','ignore']});
  const origin=execFileSync('git',['-C',root,'remote','get-url','origin'],{encoding:'utf8',timeout:5000,stdio:['ignore','pipe','ignore']}).trim();
  const top=await realpath(execFileSync('git',['-C',root,'rev-parse','--show-toplevel'],{encoding:'utf8',timeout:5000,stdio:['ignore','pipe','ignore']}).trim());
  checkout={commit,package_worktree_clean:dirty.length===0,supported_repository_origin:supportedRepositoryOrigin(origin),canonical_package_path:relative(top,root)==='packages/research'};
 }catch{/* Source digests remain available outside a Git checkout. */}
 async function json(path){const f=await packageFile(root,path);files.push(f.identity);return JSON.parse(f.bytes);}
 const lock=await json('source-lock.json');
 // Use the producer's complete lock, including retained engine bytes.
 for(const row of lock.files){const f=await packageFile(root,row.path);if(row.sha256&&f.identity.sha256!==row.sha256)throw Error(`Package pin mismatch: ${row.path}`);}
 const canonical=await json('registry/claims.json'),bindings=await json('integration/claims.json');
 const graph=await json(`${lock.lean_profile.directory}/DEPENDENCY-GRAPH.json`);
 if(files.at(-1).sha256!==lock.lean_profile.graph_sha256)throw Error('Package graph mismatch');
 const target=Object.values(graph.targets).sort((a,b)=>Object.keys(b.modules).length-Object.keys(a.modules).length)[0];
 if(Object.keys(target.modules).length!==lock.lean_profile.module_count)throw Error('Retained module count mismatch');
 const modules=new Map();
 for(const [module,row]of Object.entries(target.modules))modules.set(module,{module,path:`${lock.lean_profile.directory}/source-store/${row.sha256}.lean`,sha256:row.sha256,imports:row.imports,role:'retained_source'});
 const additions=await json('integration/lean-modules.json');
 for(const row of additions.modules){if(modules.has(row.module))throw Error('Duplicate package module');modules.set(row.module,{...row,role:'integration_source'});}
 // Verify every source body, not just a convenient selected count.
 for(const row of modules.values()){const f=await packageFile(root,row.path);if(f.identity.sha256!==row.sha256)throw Error(`Module pin mismatch: ${row.module}`);row.git_blob=f.identity.git_blob;}
 for(const row of modules.values()){const url=canonicalSourceURL(checkout,row.path);if(url)row.url=url;}
 const cards=new Map(canonical.claims.map(c=>[c.id,c]));
 const rows=new Map(bindings.claims.map(b=>[b.claim_id,b]));
 if(cards.size!==canonical.claims.length||rows.size!==bindings.claims.length||cards.size!==rows.size||[...cards.keys()].some(id=>!rows.has(id)))throw Error('Package must account for every canonical claim exactly once');
 const types=new Map();
 const externalEvidence=new Map();
 const contextReceipts=new Map();
 for(const source of modules.values()){
  const path=source.provenance?.external_current_context_verification;if(!path)continue;
  if(!contextReceipts.has(path))contextReceipts.set(path,await json(path));
  const receipt=contextReceipts.get(path);
  const member=receipt.selected_sources?.find(r=>r.module===source.module);
  const expected=receipt.source_module===source.module?receipt.source_sha256:member?.sha256;
  if(expected!==source.sha256||(member?.git_blob&&member.git_blob!==source.git_blob))throw Error('External context receipt source identity differs');
  const {selected_sources,selected_names,...context}=receipt;
  externalEvidence.set(source.module,{record:path,...context,module_member:source.module,module_member_sha256:source.sha256,
   selected_names:receipt.source_module===source.module?selected_names:[],evidence_role:'external_scoped_context_receipt_not_whole_claim_or_cache_admission'});
 }
 for(const name of (await readdir(resolve(root,'integration'))).sort().filter(n=>/complete-printed-types.*\.json$/.test(n))){
  const receipt=await json(`integration/${name}`);
  for(const row of receipt.rows??[]){const printed=row.printed_type??row.type;if(typeof row.name!=='string'||typeof printed!=='string')continue;
   if(!types.has(row.name))types.set(row.name,[]);
   types.get(row.name).push({...row,printed_type:printed,record:`integration/${name}`,source_commit:receipt.source_commit??receipt.source,run_id:receipt.run_id??receipt.run,job_id:receipt.job_id??receipt.job,evidence_role:'historical_printed_type_not_current_execution'});
  }
 }
 for(const b of rows.values())for(const d of b.lean?.declarations??[]){
  const owner=b.lean.declaration_modules?.[d]??b.lean.module;
  if(!modules.has(owner))throw Error(`Missing declaration owner source: ${owner}`);
 }
 return {root,lock,cards,rows,modules,types,externalEvidence,identity:{files,checkout,canonical_registry:lock.canonical_registry,selected_modules:modules.size,limitation:'Exact local source identities. Historical verification is not a current build; selected counts are not all-claim closure.'}};
}
export function searchPackageModules(pkg,query){
 const records=new Map(),documents=[];
 for(const source of pkg.modules.values()){
  const names=[];for(const binding of pkg.rows.values())for(const name of binding.lean?.declarations??[]){
   if((binding.lean.declaration_modules?.[name]??binding.lean.module)===source.module)names.push({name,claim_id:binding.claim_id});
  }
  const evidence=pkg.externalEvidence?.get(source.module)??null;
  const key=source.module;
  const record={...source,direct_named_claim_bindings:names,external_context_evidence:evidence,
   scope:'Exact package module/source and recorded declarations only. Module evidence does not establish a canonical claim, native runtime refinement, new execution or cache admission. Reuse closed scoped evidence before executing another check.'};
  records.set(key,record);
  documents.push({url:key,title:key,body:[source.path,...source.imports,JSON.stringify(source.provenance??{}),JSON.stringify(evidence??{}),names.map(n=>n.name).join(' ')].join('\n'),bindings:[{role:'package_module_source_navigation'}]});
 }
 return searchSources({documents},query).map(hit=>records.get(hit.url));
}
export function solverBinding(card,pkg){
 const b=pkg.rows.get(card.id),pinned=pkg.cards.get(card.id);
 if(!b)return {claim_id:card.id,status:'UNBOUND_IN_PACKAGE',mathematical_status:card.mathematical_status};
 const ds=b.lean?.declarations??[];
 const declarations=ds.map(name=>{const owner=b.lean.declaration_modules?.[name]??b.lean.module;return {name,owner,source:pkg.modules.get(owner),historical_types:pkg.types.get(name)??[],type_status:pkg.types.has(name)?'historical_type_available':'TYPE_NOT_INDEXED_USE_ACTUAL_CHECK'};});
 return {claim_id:card.id,canonical_scope:card.exact_statement_and_scope,mathematical_status:card.mathematical_status,completion:card.completion,
  package_canonical_scope:pinned.exact_statement_and_scope,package_canonical_mathematical_status:pinned.mathematical_status,
  scientific_obligation:card.remaining_obligation,separate_downstream_or_validation_work:card.separate_downstream_or_validation_work,
  package_obligation:b.obligation,source_artifacts:b.source_artifacts,dependencies:b.dependencies,
  lean:b.lean,rust:b.rust,declarations,historical_verification:b.verification??[],
  check:ds.length?{program:'cargo',args:['run','--offline','--locked','-p','research-commons-package','--','check-exports','--target',b.lean.module,'--claim',card.id],cwd:pkg.root,
   prerequisite:'An existing exact audited target build and installed pinned toolchains. This command checks declarations/owners; it does not solve the scientific question.'}:null,
  gaps:[...(!ds.length?['NO_NAMED_LEAN_BINDING']:[]),...(b.rust?.state!=='verified_binding'?['NATIVE_BINDING_NOT_FULLY_VERIFIED']:[]),'SOURCE_SNAPSHOT_DOES_NOT_ESTABLISH_FRESH_EXECUTION'],
  acceptance:'Use the existing coverage --strict gate for package completeness; this projection grants no new acceptance.'};
}
export function solverSearchCards(cards,pkg,observations=[]){
 return cards.map(c=>{const b=solverBinding(c,pkg);const words=[b.lean?.module,b.rust?.module,...(b.declarations??[]).flatMap(d=>[d.name,d.owner,...d.historical_types.map(t=>t.printed_type)]),...observations.filter(o=>o.claim_id===c.id).map(o=>o.outcome)];
  return {...c,aliases:[...(c.aliases??[]),...words.filter(Boolean)]};});
}
export function coverageLedger(cards,pkg){
 const current=new Set(cards.map(c=>c.id));
 return {current_claims:cards.length,package_claims:pkg.cards.size,all_current_claims_accounted_for:cards.every(c=>pkg.rows.has(c.id)),package_only_claims:[...pkg.cards.keys()].filter(id=>!current.has(id)),
  rows:cards.map(c=>solverBinding(c,pkg)),full_package_complete:null,completion_authority:'Existing Rust coverage --strict; no metadata projection can satisfy that gate.'};
}
