import {readFile,realpath,stat} from 'node:fs/promises';
import {dirname,resolve,sep} from 'node:path';
import {identity} from './source-cache.mjs';
import {searchSources} from '../dist/source-search.mjs';
const allowed=new Set(['propext','Classical.choice','Quot.sound']);
const nameOK=s=>typeof s==='string' && /^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(s);
async function resource(root,entry,max){
 if(!entry||typeof entry.path!=='string'||!entry.path||!/^([a-f0-9]{64})$/.test(entry.sha256)||entry.path.includes('\\'))throw Error('Invalid scoped evidence resource');
 const candidate=resolve(root,entry.path);if(!candidate.startsWith(root+sep))throw Error('Scoped evidence path escapes its directory');
 const path=await realpath(candidate),info=await stat(path);if(!path.startsWith(root+sep)||!info.isFile())throw Error('Scoped evidence resource is not an in-directory file');
 if(info.size>max)throw Error('Scoped evidence resource exceeds its bound');const bytes=await readFile(path);if(bytes.length>max)throw Error('Scoped evidence resource exceeds its bound');
 if(identity(bytes).sha256!==entry.sha256)throw Error('Scoped evidence resource hash mismatch');return {path:entry.path,sha256:entry.sha256,bytes};
}
export async function loadScopedEvidence(paths){
 if(!paths.length||paths.length>20)throw Error('Use 1..20 explicit scoped evidence manifests');
 const records=[],ids=new Set();
 for(const file of paths){
  const manifestPath=await realpath(file),root=await realpath(dirname(manifestPath)),info=await stat(manifestPath);if(!info.isFile()||info.size>1024*1024)throw Error('Scoped evidence manifest exceeds its bound');const raw=await readFile(manifestPath);if(raw.length>1024*1024)throw Error('Scoped evidence manifest exceeds its bound');
  const m=JSON.parse(raw);if(m.schema!==1||m.kind!=='local_scoped_lean_audit'||!nameOK(m.id)||ids.has(m.id)||typeof m.scope!=='string'||!m.scope||m.scope.length>4000||!Array.isArray(m.limitations)||!m.limitations.length||m.limitations.some(x=>typeof x!=='string'||!x||x.length>2000))throw Error('Invalid scoped evidence manifest');ids.add(m.id);
  if(!Array.isArray(m.sources)||!m.sources.length||m.sources.length>20||!Array.isArray(m.named_declarations)||!m.named_declarations.length||m.named_declarations.length>100||!Number.isSafeInteger(m.selected_module_count)||m.selected_module_count<1||m.selected_module_count>5000)throw Error('Invalid scoped evidence selection');
  const sources=[];for(const s of m.sources){if(!nameOK(s.module)||sources.some(x=>x.module===s.module))throw Error('Invalid or duplicate source module');const x=await resource(root,s,2*1024*1024);sources.push({module:s.module,path:x.path,sha256:x.sha256,body:x.bytes.toString('utf8')});}
  const named=await resource(root,m.named_audit,2*1024*1024),owned=await resource(root,m.owned_audit,32*1024*1024),log=named.bytes.toString('utf8'),audit=JSON.parse(owned.bytes);
  if(!Array.isArray(audit.selected_modules)||audit.selected_modules.some(n=>!nameOK(n))||audit.selected_modules.length!==m.selected_module_count||new Set(audit.selected_modules).size!==audit.selected_modules.length||!Array.isArray(audit.declarations)||audit.declaration_count!==audit.declarations.length||!Array.isArray(audit.owned_axioms)||audit.owned_axioms.length||!Array.isArray(audit.nonstandard_axiom_rows)||audit.nonstandard_axiom_rows.length||!Array.isArray(audit.missing_modules)||audit.missing_modules.length)throw Error('Scoped owned audit is incomplete or rejected');
  const selected=new Set(audit.selected_modules),declarations=new Map();let theoremCount=0;for(const row of audit.declarations){if(typeof row.name!=='string'||!row.name||row.name.length>1000||!nameOK(row.module)||!selected.has(row.module)||declarations.has(row.name)||!['theorem','definition','opaque','inductive','constructor','recursor','quotient'].includes(row.kind)||!Array.isArray(row.axioms)||row.axioms.some(a=>!allowed.has(a)))throw Error('Invalid owned audit declaration');if(row.kind==='theorem')theoremCount++;declarations.set(row.name,row);}if(theoremCount!==audit.theorem_declaration_count)throw Error('Owned theorem count mismatch');
  const names=new Set();for(const d of m.named_declarations){
   if(!nameOK(d.name)||!nameOK(d.module)||names.has(d.name)||!sources.some(s=>s.module===d.module)||!selected.has(d.module))throw Error('Invalid named declaration owner');names.add(d.name);
   const row=declarations.get(d.name);if(!row||row.module!==d.module)throw Error('Named declaration absent from owned source module');
   const escaped=d.name.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');const match=log.match(new RegExp("'"+escaped+"' depends on axioms:\\s*\\[([^\\]]*)\\]"));const none=log.includes("'"+d.name+"' does not depend on any axioms");if((!!match)===none)throw Error('Missing or ambiguous named axiom output');
   const occurrences=log.split("'"+d.name+"' depends on axioms:").length-1+log.split("'"+d.name+"' does not depend on any axioms").length-1;if(occurrences!==1)throw Error('Missing or ambiguous named axiom output');
   const actual=match?match[1].split(',').map(x=>x.trim()).filter(Boolean):[];if(actual.some(a=>!allowed.has(a))||JSON.stringify([...new Set(actual)].sort())!==JSON.stringify([...new Set(row.axioms)].sort()))throw Error('Named and owned axiom output disagree');
   if(!new RegExp(String.raw`^@?${escaped}(?:\.\{|\s|:)`,'m').test(log))throw Error('Named type output missing');
  }
  records.push({id:m.id,scope:m.scope,limitations:m.limitations,execution_context:m.execution_context??null,manifest:{path:file,sha256:identity(raw).sha256},sources:sources.map(({body,...s})=>s),named_declarations:m.named_declarations,selected_module_count:m.selected_module_count,owned_audit:{path:owned.path,sha256:owned.sha256,declarations:audit.declaration_count,theorems:audit.theorem_declaration_count},named_audit:{path:named.path,sha256:named.sha256,type_and_axiom_output:log},trust:'Explicit local receipt and file-integrity checks; source-to-execution association is asserted by the receipt, not independently authenticated. No new execution, claim-status change, native binding, or complete-package acceptance.',_body:sources.map(s=>s.body).join('\n')+'\n'+log});
 }
 return records;
}
export function searchScopedEvidence(records,query){
 const byId=new Map(records.map(r=>[r.id,r]));const documents=records.map(r=>({url:r.id,title:r.id,body:[r.scope,...r.limitations,r._body,...r.named_declarations.map(x=>x.name)].join('\n'),bindings:[{role:'explicit_local_scoped_evidence'}]}));
 return searchSources({documents},query).map(hit=>{const {_body,...record}=byId.get(hit.url);return record;});
}
