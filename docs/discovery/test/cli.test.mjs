import test from 'node:test';import assert from 'node:assert/strict';import {execFileSync,spawnSync}from'node:child_process';import{fileURLToPath}from'node:url';
const cli=fileURLToPath(new URL('../tools/query.mjs',import.meta.url));
const run=(...args)=>JSON.parse(execFileSync(process.execPath,[cli,...args],{encoding:'utf8',maxBuffer:2*1024*1024,timeout:15000}));
test('agent archive pagination is bounded and deterministic, and refuses scientific-facet transfer',()=>{
 const a=run('--archive','--query','calendar metric','--limit','1');
 const b=run('--archive','--query','calendar metric','--limit','1','--offset','1');
 assert.equal(a.total,2);assert.equal(a.results.length,1);assert.equal(a.next_offset,1);assert.equal(b.next_offset,null);assert.notEqual(a.results[0].path,b.results[0].path);
 const fail=spawnSync(process.execPath,[cli,'--archive','--status','open'],{encoding:'utf8',timeout:10000});assert.notEqual(fail.status,0);assert.equal(fail.stdout,'');
});
test('agent recovered-component export and combined subjective claim lookup retain separate roles',()=>{
 const recovered=run('--sources','--query','G3-SUPPLIED-WORD-ADMISSION','--limit','1');
 assert(recovered.total>0);assert(!Object.hasOwn(recovered.results[0],'body'));
 assert(recovered.results[0].bindings.every(b=>!b.claim_id));assert(recovered.results[0].bindings.some(b=>b.catalogue_record?.gap));
 const ranked=run('--kind','theorem','--review','accepted_scoped_hand_review','--sort','subjective_reuse','--limit','1');
 assert.equal(ranked.results[0].claim_id,'CB-G6-001');assert.equal(ranked.results[0].subjective_reuse.entry.rank,2);
 assert.match(ranked.results[0].subjective_reuse.purpose,/Not mathematical acceptance/);
});
