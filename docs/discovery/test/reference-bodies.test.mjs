import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,writeFile,readFile,rm,mkdir} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {loadReferenceBodies,REFERENCED_PUBLIC_INPUTS} from '../tools/reference-bodies.mjs';
import {queryResearchResults} from '../tools/research-results.mjs';

function document(repository,path,body){
 const bytes=Buffer.from(body),commit=REFERENCED_PUBLIC_INPUTS.get(repository);
 return {repository,commit,url:`https://github.com/${repository}/blob/${commit}/${path}`,title:path,source_paths:[path],body,bytes:bytes.length,git_blob:createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),sha256:createHash('sha256').update(bytes).digest('hex'),bindings:[],license_status:'No license found; no general license inferred',evidence_role:'Source body only; no scientific status, review, execution or license acceptance inferred.'};
}
test('same search engine joins exact referenced versions with ranking and global pagination',async()=>{
 const root=await mkdtemp(join(tmpdir(),'ref-bodies-'));try{
  const manifest=join(root,'manifest.json'),file=join(root,'refs.json');
  await writeFile(manifest,JSON.stringify({schema:1,repository:'Sodelin/Research-Commons',commit:'a'.repeat(40),inventory:[],shards:[],coverage:{},limitation:'Fixture empty tree; no claim cards edited'}));
  const a=document('Sodelin/Formalizing-Soft-Sciences','SocialScience/shared.lean','Related all size anchor nonnegative words'),b=document('Sodelin/Cross-Scale-Causal-Formalization','SocialScience/shared.lean','theorem all_size_anchor_nonnegative : True := by trivial');
  await writeFile(file,JSON.stringify({schema:1,view:'exact_canonical_reference_bodies',documents:[a,b],unavailable:[{reference:'https://github.com/other/owner',reason:'link-only'}]}));
  const first=await queryResearchResults(manifest,'all_size_anchor_nonnegative',{referenceBodies:file,limit:1});assert.equal(first.total,2);assert.equal(first.next_offset,1);assert.equal(first.results[0].url,b.url);assert.equal(first.results[0].sha256,b.sha256);assert.deepEqual(first.results[0].canonical_claim_references,[]);
  const second=await queryResearchResults(manifest,'all_size_anchor_nonnegative',{referenceBodies:file,limit:1,offset:1});assert.equal(second.results[0].url,a.url);assert.equal(second.next_offset,null);
  const exact=await queryResearchResults(manifest,b.url,{referenceBodies:file});assert.equal(exact.results[0].url,b.url);
  for(const mutate of [x=>x.body+=' tamper',x=>x.repository='other/owner',x=>x.commit='f'.repeat(40),x=>x.source_paths=['../escape'],x=>x.license_status='',x=>x.bindings=[{claim_id:'CB-UNKNOWN',role:'accepted'}]]){
   const changed=structuredClone(b);mutate(changed);await writeFile(file,JSON.stringify({schema:1,view:'exact_canonical_reference_bodies',documents:[changed],unavailable:[]}));await assert.rejects(loadReferenceBodies(file));
  }
  await writeFile(file,JSON.stringify({schema:1,view:'exact_canonical_reference_bodies',documents:[b,b],unavailable:[]}));await assert.rejects(loadReferenceBodies(file),/Duplicate/);
 }finally{await rm(root,{recursive:true,force:true});}
});

test('a missing exact pinned research body is unresolved, not outside selected roots',async()=>{
 const root=await mkdtemp(join(tmpdir(),'ref-missing-'));try{
  const git=(...args)=>execFileSync('git',['-C',root,...args],{stdio:'pipe'});git('init');git('config','user.email','fixture@example.invalid');git('config','user.name','Fixture');await mkdir(join(root,'docs'));await writeFile(join(root,'docs/claims.json'),'{}');git('add','.');git('commit','-m','Initial');const pin=git('rev-parse','HEAD').toString().trim();
  const missing=`https://github.com/Sodelin/Research-Commons/blob/${pin}/research/missing.json`,outside=`https://github.com/Sodelin/Research-Commons/blob/${pin}/docs/claims.json`;
  await writeFile(join(root,'docs/claims.json'),JSON.stringify({claims:[{id:'CB-FIXTURE',urls:[missing,outside]}]}));git('add','.');git('commit','-m','Citations');const current=git('rev-parse','HEAD').toString().trim();
  const manifest=join(root,'manifest.json'),output=join(root,'coverage.json');await writeFile(manifest,JSON.stringify({commit:current,inventory:[],roots:['research/']}));execFileSync('python3',[fileURLToPath(new URL('../tools/reconcile-result-references.py',import.meta.url)),'--repo',root,'--manifest',manifest,'--output',output]);
  const report=JSON.parse(await readFile(output));assert.equal(report.records.find(r=>r.reference===missing).coverage,'repository_artifact_missing_at_pinned_ref');assert.equal(report.records.find(r=>r.reference===outside).coverage,'repository_artifact_outside_selected_roots');
 }finally{await rm(root,{recursive:true,force:true});}
});

test('offline reference intake deduplicates anchors, retains third-party links and rejects changed source bytes',async()=>{
 const root=await mkdtemp(join(tmpdir(),'ref-intake-'));try{
  const doc=document('Sodelin/Formalizing-Soft-Sciences','SocialScience/supplier.lean','theorem source_only_supplier : True := by trivial\n'),bodyRoot=join(root,'bodies'),dir=join(bodyRoot,doc.repository.replace('/','--'),doc.commit,'SocialScience');await mkdir(dir,{recursive:true});await writeFile(join(dir,'supplier.lean'),doc.body);
  const inputs=join(root,'inputs.json'),references=join(root,'references.json'),output=join(root,'corpus.json');
  const source={reference:doc.url,status:'VERIFIED_EXACT_PUBLIC_BODY',entry:{sha:doc.git_blob},bytes:doc.bytes,sha256:doc.sha256,license_status:doc.license_status};
  await writeFile(inputs,JSON.stringify({repository_checks:[...REFERENCED_PUBLIC_INPUTS].map(([repository])=>({repository,private:false,visibility:'public'})),records:[source,{...source,reference:doc.url+'#L1'}]}));
  await writeFile(references,JSON.stringify({tree_source_commit:'a'.repeat(40),records:[doc.url,doc.url+'#L1','https://github.com/other/owner/blob/'+('b'.repeat(40))+'/proof.lean'].map(reference=>({reference,coverage:'external_repository_body_unbound',bindings:[{record_id:'CB-FIXTURE',metadata_path:'docs/claims.json'}]}))}));
  const args=[fileURLToPath(new URL('../tools/index-referenced-bodies.py',import.meta.url)),'--verified-inputs',inputs,'--body-root',bodyRoot,'--references',references,'--repo',root,'--output',output];execFileSync('python3',args);
  const corpus=await loadReferenceBodies(output);assert.equal(corpus.documents.length,1);assert.equal(corpus.unavailable.length,1);assert.match(corpus.unavailable[0].reason,/link-only/);assert.equal(corpus.documents[0].sha256,doc.sha256);assert.equal(corpus.documents[0].license_status,doc.license_status);
  await writeFile(join(dir,'supplier.lean'),doc.body+'changed');assert.throws(()=>execFileSync('python3',args,{stdio:'pipe'}));
 }finally{await rm(root,{recursive:true,force:true});}
});
