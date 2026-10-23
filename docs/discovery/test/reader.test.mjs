import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {performance} from 'node:perf_hooks';
import {validate,search,bucket,neighbors,reusePacket,safeLink,literatureSources,validateAssessments,sortClaims,validateRanking} from '../dist/model.mjs';
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
 assert(published.length>0);assert(published.every(c=>c.origin.category==='published_open_problem'));
 assert(published.find(c=>c.id==='CB-SEQ-001').origin.source_url);
 assert(published.every(c=>c.origin.detail));
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
test('later authored subjective assessment exports as a dated source without rewriting the historical ordering',async()=>{
 const nav=JSON.parse(await readFile(new URL('../dist/reading-joins.json',import.meta.url))),notes=validateAssessments(nav.subjective_assessments);
 const ranking=validateRanking(JSON.parse(await readFile(new URL('../dist/subjective-reuse-ranking.json',import.meta.url))));
 const before=JSON.stringify(ranking),order=sortClaims(data.claims,'subjective_reuse',ranking).map(c=>c.id);
 const p=reusePacket(card('CB-MEMORY-003'),meta,nav.joins,ranking,null,notes);
 assert.equal(p.subjective_reuse.later_assessments[0].source_count,110);assert.match(p.subjective_reuse.later_assessments[0].scope,/Not objective importance/);
 assert.equal(p.subjective_reuse.entry,null);assert.deepEqual(sortClaims(data.claims,'subjective_reuse',ranking).map(c=>c.id),order);assert.equal(JSON.stringify(ranking),before);
 assert.throws(()=>validateAssessments([{...notes[0],source_url:notes[0].source_url+'#access_token=synthetic'}]),/Invalid/);
 assert.throws(()=>validateAssessments([{...notes[0],source_count:0}]),/Invalid/);
 assert.throws(()=>validateAssessments([{...notes[0],subjective:false}]),/Invalid/);
});
test('warm ranked lookup is measured over the actual current register',()=>{
 search(data.claims,{q:'routing'});const start=performance.now();
 for(let i=0;i<100;i++)search(data.claims,{q:i%2?'independent routing':'quantum'});
 const elapsed=performance.now()-start;assert(elapsed<2000,`100 warm queries took ${elapsed}ms`);
 console.log(`Actual register: ${data.claims.length} cards; 100 warm queries ${elapsed.toFixed(1)}ms (this Node/phone host only).`);
});


test('schema1.1 completion and downstream obligations survive agent export separately',()=>{
 for(const id of ['CB-G6-001','CB-G7-001','CB-PHYS-P5-004']){
  const c=card(id),packet=reusePacket(c,meta);
  assert.equal(packet.completion.mathematical_claim_complete,true);
  assert.equal(packet.completion.proof_derivation_required,false);
  assert.equal(packet.separate_downstream_or_validation_work,c.separate_downstream_or_validation_work);
  assert(packet.genuine_remaining_obligation.startsWith('None for this exact proved claim'));
 }
 assert.equal(card('CB-G3-004').completion.proof_derivation_required,true);
});


test('downstream-only text is searchable without reopening completed mathematics',()=>{
 const c=structuredClone(card('CB-G6-001'));
 c.separate_downstream_or_validation_work='zephyrnativebinding';
 const result=search([c],{q:'zephyrnativebinding'});
 assert.equal(result.length,1);assert.equal(result[0].id,'CB-G6-001');
 assert.equal(result[0].completion.mathematical_claim_complete,true);
 assert.equal(search([c],{q:'zephyrnativebinding',status:'open'}).length,0);
});
test('historical schema1.0 completion fallback remains available',()=>{
 const c=structuredClone(card('CB-G6-001'));delete c.completion;delete c.separate_downstream_or_validation_work;
 const result=reusePacket(c,meta);
 assert.equal(result.completion,null);assert.equal(result.separate_downstream_or_validation_work,null);
 assert.equal(result.genuine_remaining_obligation,c.remaining_obligation);
 assert.equal(search([c],{q:'CB-G6-001'})[0].id,c.id);
});


test('NANUQ literature is recovered from canonical prior-work artifacts without inventing origin fields',()=>{
 const c=structuredClone(card('CB-NANUQ-002'));delete c.origin.source_url;
 const refs=literatureSources(c);assert(refs.some(a=>a.url==='https://link.springer.com/article/10.1007/s11538-025-01549-4'&&a.role==='prior_work'));
 assert(!refs.some(a=>a.role==='proof_or_status'));assert.equal(c.origin.source_url,undefined);
 assert(reusePacket(c,meta).provenance.literature_sources.some(a=>a.url.includes('10.1007/s11538')));
});
test('bibliography links deduplicate and retain HTTPS trust boundary',()=>{
 const c=structuredClone(card('CB-SEQ-001'));const url=c.origin.source_url;
 c.accepted_artifacts.push({label:'Same original source',url,role:'prior_work'},{label:'Unsafe',url:'javascript:alert(1)',role:'prior_work'});
 const refs=literatureSources(c);assert.equal(refs.filter(a=>a.url===url).length,1);assert(refs.every(a=>a.url.startsWith('https:')));
});
test('literature DOI is searchable through the same canonical provenance adapter',()=>{
 assert(search(data.claims,{q:'10.1007/s11538-025-01549-4'}).some(c=>c.id==='CB-NANUQ-002'));
});


test('recovered Atlas credential-bearing source-link controls preserve scientific URL support',()=>{
 assert.equal(safeLink('https://token:secret@example.org/proof'),null);
 assert.equal(safeLink('https://example.org/proof?access_token=hidden'),null);
 assert.equal(safeLink('https://example.org:8443/proof'),null);
 assert.equal(safeLink('https://link.springer.com/article/10.1007/s11538-025-01549-4'),'https://link.springer.com/article/10.1007/s11538-025-01549-4');
 assert.equal(safeLink('https://arxiv.org/abs/1234.5678?context=math'),'https://arxiv.org/abs/1234.5678?context=math');
});


test('registry validation refuses credential/signed source links before accepting a replacement',()=>{
 for(const url of ['https://token:secret@example.org/proof','https://example.org/proof?X-Amz-Signature=hidden']){
  const d=structuredClone(data);d.claims[0].accepted_artifacts[0].url=url;
  assert.throws(()=>validate(d));
 }
 const d=structuredClone(data);d.claims[0].origin.source_url='https://example.org/paper?access_token=hidden';assert.throws(()=>validate(d));
});

test('combinable source-defined facets and subjective ranking preserve unassessed/unranked distinctions',async()=>{
 const {sortClaims}=await import('../dist/model.mjs');
 const ranking=JSON.parse(await readFile(new URL('../dist/subjective-reuse-ranking.json',import.meta.url)));
 const filtered=search(data.claims,{kind:'theorem',review:'accepted_scoped_hand_review'});
 assert(filtered.length>0);assert(filtered.every(c=>c.claim_kind==='theorem'&&c.completion.independent_review==='accepted_scoped_hand_review'));
 assert.equal(sortClaims(filtered,'subjective_reuse',ranking)[0].id,'CB-G6-001');
 const all=sortClaims(data.claims,'subjective_reuse',ranking),ranked=new Set(ranking.entries.map(e=>e.claim_id));
 const unranked=data.claims.filter(c=>!ranked.has(c.id));assert(all.slice(-unranked.length).every(c=>!ranked.has(c.id)));assert.equal(all.length,data.claims.length);
 const newCard=data.claims.find(c=>c.id==='CB-SEQ-004');
 const packet=reusePacket(newCard,meta,[],ranking);assert.equal(packet.subjective_reuse.entry,null);assert.match(packet.subjective_reuse.unranked_means,/not low importance/);
 assert.match(newCard.novelty_status,/unassessed/);assert.equal(sortClaims(data.claims,'',ranking),data.claims);
});


test('recovered feedback and genome components keep scoped historical formal evidence and excluded extensions',()=>{
 const ids=data.claims.filter(c=>/^CB-(FEEDBACK|GENOME)-/.test(c.id));assert.equal(ids.length,9);
 for(const c of ids){assert.equal(bucket(c),'established');assert.deepEqual(reusePacket(c,meta).formal_status,c.evidence.formal);assert(c.separate_downstream_or_validation_work);}
 const finite=card('CB-FEEDBACK-004');assert.match(finite.evidence.formal.status,/recorded_exit_limit/);assert.match(finite.separate_downstream_or_validation_work,/exit was not retrieved/);
 const iap=card('CB-FEEDBACK-005');assert.equal(iap.completion.mathematical_claim_complete,true);assert.match(iap.separate_downstream_or_validation_work,/does not reopen/);
});

test('credential-bearing fragments and router parameters are refused while scientific anchors survive',async()=>{
 const {validateRanking}=await import('../dist/model.mjs');
 for(const fragment of ['access_token=synthetic','?auth=synthetic','/route?step=1&api_key=synthetic','section&token=synthetic','%61ccess_token=synthetic','access_token%3Dsynthetic','!/?X-Amz-Signature=synthetic']){
  const url='https://example.org/proof#'+fragment;assert.equal(safeLink(url),null,fragment);
  for(const field of ['origin','artifact']){const copy=structuredClone(data);if(field==='origin')copy.claims[0].origin.source_url=url;else copy.claims[0].accepted_artifacts[0].url=url;assert.throws(()=>validate(copy));}
  assert.throws(()=>validateRanking({subjective:true,entries:[{source_url:url}]}));
 }
 for(const anchor of ['cb-g7-001','theorem-4.7','eq:3','token','section=3','route?section=3','formula=E%3Dmc2'])assert(safeLink('https://example.org/proof#'+anchor),anchor);
});

test('bibliography normalizes host/default-port spelling but retains distinct scientific anchors',()=>{
 const c=structuredClone(data.claims[0]);c.origin.source_url='https://example.org/paper';
 c.accepted_artifacts=[{label:'Same source',role:'prior_work',url:'https://EXAMPLE.org:443/paper'}];
 const before=JSON.stringify(c);assert.equal(literatureSources(c).length,1);assert.equal(literatureSources(c)[0].url,'https://example.org/paper');
 c.accepted_artifacts.push({label:'Specific theorem',role:'prior_work',url:'https://EXAMPLE.org:443/paper#theorem-2'});
 const result=literatureSources(c);assert.equal(result.length,2);assert.equal(result[1].url,'https://example.org/paper#theorem-2');
 assert.equal(c.accepted_artifacts[0].url,'https://EXAMPLE.org:443/paper');
 assert(before.includes('EXAMPLE.org:443'));
});
