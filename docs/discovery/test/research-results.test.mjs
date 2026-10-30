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
 try{git('init');git('config','user.name','Fixture');git('config','user.email','fixture@example.invalid');git('remote','add','origin','https://github.com/Sodelin/Research-Commons.git');await mkdir(join(repo,'research'));await writeFile(join(repo,'research/result.md'),'# Partial supplier\nCounterexample XenonNeedle, full theorem remains open.');await writeFile(join(repo,'research/proof.lean'),'-- XenonNeedle proof source, no execution receipt');await writeFile(join(repo,'research/failed.json'),' {"result":"XenonNeedle failed approach", "accepted":false}');await writeFile(join(repo,'research/image.png'),Buffer.from([0,255]));git('add','.');git('commit','-m','Fixture');const pin=git('rev-parse','HEAD').toString().trim();
 const script=fileURLToPath(new URL('../tools/index-research-results.py',import.meta.url));execFileSync('python3',[script,'--repo',repo,'--commit',pin,'--output',index]);execFileSync('python3',[script,'--repo',repo,'--output',index,'--check']);
 const r=await queryResearchResults(join(index,'manifest.json'),'XenonNeedle',{offset:1,limit:1});assert.equal(r.total,3);assert.equal(r.results.length,1);assert.equal(r.next_offset,2);assert.equal(r.coverage.path_only_paths,1);assert.equal(r.results[0].canonical_claim_references.length,0);
 await writeFile(join(repo,'research/later.md'),'Later source only');git('add','.');git('commit','-m','New result without card edit');assert.throws(()=>execFileSync('python3',[script,'--repo',repo,'--output',index,'--check'],{stdio:'pipe'}));
 const extended=join(root,'extended');execFileSync('python3',[script,'--repo',repo,'--base',index,'--output',extended]);const scoped=await queryResearchResults(join(extended,'manifest.json'),'XenonNeedle',{pathPrefix:'research/proof.lean'});assert.equal(scoped.total,1);
 const file=join(index,'manifest.json'),m=JSON.parse(await readFile(file));m.inventory=m.inventory.filter(x=>x.path!=='research/proof.lean');await writeFile(file,JSON.stringify(m));await assert.rejects(queryResearchResults(file,'XenonNeedle'),/inventory/i);
 }finally{await rm(root,{recursive:true,force:true});}
});
