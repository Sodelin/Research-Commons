import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {performance} from 'node:perf_hooks';
import {validate,search,bucket,neighbors,reusePacket,safeLink} from '../dist/model.mjs';
const data=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));
const meta=JSON.parse(await readFile(new URL('../dist/source.json',import.meta.url)));
const card=id=>data.claims.find(c=>c.id===id);

test('canonical claim source validates without changing scientific statuses',()=>{
 assert.equal(validate(data),data);assert.equal(data.claims.length,meta.claim_count);
 const before=JSON.stringify(data);search(data.claims,{q:'quantum'});assert.equal(JSON.stringify(data),before);
});
test('exact identity and typo-tolerant search recover accepted suppliers',()=>{
 assert.equal(search(data.claims,{q:'CB-G4-003'})[0].id,'CB-G4-003');
 assert(search(data.claims,{q:'independant routing'}).some(c=>c.programme.startsWith('G4')));
 assert(search(data.claims,{q:'observ'}).length>0);
});
test('published questions and classical work retain their actual attribution',()=>{
 const published=search(data.claims,{origin:'published_open_problem'});
 assert(published.length>0);assert(published.every(c=>c.origin.source_url));
 assert(search(data.claims,{origin:'classical_prior'}).some(c=>c.id==='CB-CM-001'));
 assert(!published.some(c=>c.id==='CB-CM-001'));
});
test('unfinished formalization never turns a completed hand result into open mathematics',()=>{
 assert.equal(bucket(card('CB-G6-001')),'established');assert.equal(bucket(card('CB-G7-001')),'established');
 assert.equal(bucket(card('CB-PHYS-P5-004')),'counterexample');
 const open=search(data.claims,{status:'open'}).map(c=>c.id);
 assert(open.includes('CB-G3-004'));assert(open.includes('CB-G4-008'));assert(!open.includes('CB-PHYS-P5-004'));
});
test('typed relationship navigation preserves the actual relation kind and direction',()=>{
 for(const c of data.claims)for(const d of c.dependencies){
  const n=neighbors(data.claims,c.id);assert(n.outgoing.some(r=>r.claim.id===d.claim_id&&r.relation_type===d.relation_type));
  assert(neighbors(data.claims,d.claim_id).incoming.some(r=>r.claim.id===c.id));
 }
 assert(data.claims.some(c=>c.dependencies.some(d=>d.relation_type==='same_principle')));
});
test('reuse record preserves exact claim scope, evidence axes and actual remaining obligation',()=>{
 const c=card('CB-G4-008'),p=reusePacket(c,meta);
 assert.equal(p.exact_scope,c.exact_statement_and_scope);assert.equal(p.genuine_remaining_obligation,c.remaining_obligation);
 assert.equal(p.registry_source.commit,meta.commit);assert.deepEqual(p.completion_evidence,c.accepted_artifacts);
});
test('empty/malformed/duplicate and dangling-reference registers are refused',()=>{
 assert.throws(()=>validate({claims:[]}));
 const duplicate=structuredClone(data);duplicate.claims.push(duplicate.claims[0]);assert.throws(()=>validate(duplicate));
 const dangling=structuredClone(data);dangling.claims[0].dependencies=[{claim_id:'NOT-INDEXED',relation_type:'reused_theorem'}];assert.throws(()=>validate(dangling));
});
test('untrusted source links cannot introduce active URL schemes',()=>{
 assert.equal(safeLink('javascript:alert(1)'),null);assert.equal(safeLink('data:text/html,hi'),null);
 assert.equal(safeLink('https://github.com/Sodelin/Research-Commons'),'https://github.com/Sodelin/Research-Commons');
});
test('priority evidence joins reference current card IDs and immutable public sources',async()=>{
 const joins=JSON.parse(await readFile(new URL('../dist/reading-joins.json',import.meta.url)));
 for(const j of joins.joins){for(const id of j.claim_ids)assert(card(id));for(const l of j.links){assert(safeLink(l.url));assert(!l.url.includes('/blob/main/'));}}
});
test('warm ranked lookup is measured over the actual current register',()=>{
 search(data.claims,{q:'routing'});const start=performance.now();
 for(let i=0;i<100;i++)search(data.claims,{q:i%2?'independent routing':'quantum'});
 const elapsed=performance.now()-start;assert(elapsed<2000,`100 warm queries took ${elapsed}ms`);
 console.log(`Actual register: ${data.claims.length} cards; 100 warm queries ${elapsed.toFixed(1)}ms (this Node/phone host only).`);
});
