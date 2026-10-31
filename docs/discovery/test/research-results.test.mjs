import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtemp,writeFile,mkdir,readFile,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {queryResearchResults} from '../tools/research-results.mjs';
test('source-only proofs and failed receipts are searchable without claim edits',async()=>{
 const root=await mkdtemp(join(tmpdir(),'result-search-'));const repo=join(root,'repo'),index=join(root,'index');await mkdir(repo);const git=(...a)=>execFileSync('git',['-C',repo,...a]);
 try{git('init');git('config','user.name','Fixture');git('config','user.email','fixture@example.invalid');git('remote','add','origin','https://github.com/Sodelin/Research-Commons.git');await mkdir(join(repo,'research'));await writeFile(join(repo,'research/result.md'),'# Partial supplier\nCounterexample XenonNeedle, full theorem remains open. Related older all size anchor nonnegative words.');await writeFile(join(repo,'research/proof.lean'),'-- XenonNeedle proof source, no execution receipt');await writeFile(join(repo,'research/failed.json'),' {"result":"XenonNeedle failed approach", "accepted":false}');await writeFile(join(repo,'research/image.png'),Buffer.from([0,255]));await mkdir(join(repo,'docs'));await writeFile(join(repo,'docs/claims.json'),JSON.stringify({claims:[{id:'CB-FIXTURE',accepted_artifacts:[{url:'https://github.com/Sodelin/Other/blob/'+('a'.repeat(40))+'/proof.lean'},{url:'docs/proof.md'}]}]}));git('add','.');git('commit','-m','Fixture');const pin=git('rev-parse','HEAD').toString().trim();
 const script=fileURLToPath(new URL('../tools/index-research-results.py',import.meta.url));execFileSync('python3',[script,'--repo',repo,'--commit',pin,'--output',index]);execFileSync('python3',[script,'--repo',repo,'--output',index,'--check']);
 const r=await queryResearchResults(join(index,'manifest.json'),'XenonNeedle',{offset:1,limit:1});assert.equal(r.total,3);assert.equal(r.results.length,1);assert.equal(r.next_offset,2);assert.equal(r.coverage.path_only_paths,1);assert.equal(r.results[0].canonical_claim_references.length,0);
 await writeFile(join(repo,'research/later.md'),'Later source only');await writeFile(join(repo,'research/exact.lean'),'theorem all_size_anchor_nonnegative : 0 ≤ (0 : Nat) := by omega');git('add','.');git('commit','-m','New result without card edit');assert.throws(()=>execFileSync('python3',[script,'--repo',repo,'--output',index,'--check'],{stdio:'pipe'}));
 const extended=join(root,'extended');execFileSync('python3',[script,'--repo',repo,'--base',index,'--output',extended]);const ranked=await queryResearchResults(join(extended,'manifest.json'),'all_size_anchor_nonnegative');assert.equal(ranked.total,2);assert(ranked.results[0].source_paths.includes('research/exact.lean'));const urlHit=await queryResearchResults(join(extended,'manifest.json'),ranked.results[0].url);assert.equal(urlHit.total,1);const scoped=await queryResearchResults(join(extended,'manifest.json'),'XenonNeedle',{pathPrefix:'research/proof.lean'});assert.equal(scoped.total,1);
 const referenceOutput=join(root,'references.json');execFileSync('python3',[fileURLToPath(new URL('../tools/reconcile-result-references.py',import.meta.url)),'--repo',repo,'--manifest',join(extended,'manifest.json'),'--output',referenceOutput]);const references=JSON.parse(await readFile(referenceOutput));assert.equal(references.reference_count,2);assert.equal(references.coverage_counts.external_repository_body_unbound,1);assert.equal(references.coverage_counts.relative_artifact_outside_selected_roots,1);
 const file=join(index,'manifest.json'),m=JSON.parse(await readFile(file));m.inventory=m.inventory.filter(x=>x.path!=='research/proof.lean');await writeFile(file,JSON.stringify(m));await assert.rejects(queryResearchResults(file,'XenonNeedle'),/inventory/i);
 }finally{await rm(root,{recursive:true,force:true});}
});

test('an explicit source prefix selects its immutable alias without transferring acceptance',async()=>{
 const root=await mkdtemp(join(tmpdir(),'result-alias-'));const repo=join(root,'repo'),index=join(root,'index');await mkdir(repo);const git=(...a)=>execFileSync('git',['-C',repo,...a]);
 try{
  git('init');git('config','user.name','Fixture');git('config','user.email','fixture@example.invalid');git('remote','add','origin','https://github.com/Sodelin/Research-Commons.git');await mkdir(join(repo,'research'));
  const body='theorem preserved_source : True := by trivial';
  await writeFile(join(repo,'research/a-candidate.lean'),body);await writeFile(join(repo,'research/z-reviewed.lean'),body);git('add','.');git('commit','-m','Same source, separate evidence locations');const pin=git('rev-parse','HEAD').toString().trim();
  execFileSync('python3',[fileURLToPath(new URL('../tools/index-research-results.py',import.meta.url)),'--repo',repo,'--output',index]);
  const manifest=join(index,'manifest.json');const ordinary=await queryResearchResults(manifest,'preserved_source');assert.equal(ordinary.total,1);assert(ordinary.results[0].url.endsWith('/research/a-candidate.lean'));
  const selected=await queryResearchResults(manifest,'preserved_source',{pathPrefix:'research/z-reviewed.lean'});const hit=selected.results[0];assert.equal(selected.total,1);assert.equal(hit.url,`https://github.com/Sodelin/Research-Commons/blob/${pin}/research/z-reviewed.lean`);assert.equal(hit.body_document_url,ordinary.results[0].url);assert.equal(hit.sha256,ordinary.results[0].sha256);assert.deepEqual(hit.source_paths,['research/a-candidate.lean','research/z-reviewed.lean']);assert.deepEqual(hit.canonical_claim_references,[]);assert.match(hit.evidence_role,/No claim status inferred/);
  assert.equal(hit.title,'research/z-reviewed.lean');const exact=await queryResearchResults(manifest,hit.url,{pathPrefix:'research/z-reviewed.lean'});assert.equal(exact.total,1);assert.equal(exact.results[0].url,hit.url);
 }finally{await rm(root,{recursive:true,force:true});}
});
