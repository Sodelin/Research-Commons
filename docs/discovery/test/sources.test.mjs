import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {artifactReferences,recoveredReferences,readingReferences,assessmentReferences,searchSources,sourceExcerpt,searchArchive} from '../dist/source-search.mjs';
const data=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));
const corpus=JSON.parse(await readFile(new URL('../dist/source-corpus.json',import.meta.url)));
const navigation=JSON.parse(await readFile(new URL('../dist/reading-joins.json',import.meta.url))),joins=navigation.joins;
test('public body corpus accounts for every selected immutable artifact and exact source bytes',()=>{
 const refs=artifactReferences(data.claims),byURL=new Map(refs.map(r=>[r.url,r]));
 assert.equal(corpus.coverage.canonical_artifact_references,refs.length);
 const reading=readingReferences(joins,data.claims);
 assert.equal(corpus.coverage.owned_reading_join_references,reading.length);
 const assessments=assessmentReferences(navigation.subjective_assessments??[]);
 assert.equal(corpus.coverage.authored_assessment_references,assessments.length);
 for(const ref of [...reading,...assessments]){if(byURL.has(ref.url))byURL.get(ref.url).bindings.push(...ref.bindings);else byURL.set(ref.url,ref);}
 assert.equal(corpus.documents.length+corpus.coverage.unavailable.length,corpus.coverage.selected_references);
 assert.equal(new Set(corpus.documents.map(d=>d.url)).size,corpus.documents.length);
 for(const d of corpus.documents){
  if(byURL.has(d.url))assert.deepEqual(d.bindings.filter(b=>b.claim_id||b.role==='subjective_assessment_not_scientific_acceptance'),byURL.get(d.url).bindings);
  else assert(d.bindings.every(b=>!b.claim_id&&b.role.startsWith('recovered_')));
  const bytes=Buffer.from(d.body);assert.equal(bytes.length,d.bytes);
  assert.equal(createHash('sha256').update(bytes).digest('hex'),d.sha256);
  assert.equal(createHash('sha1').update('blob '+bytes.length+'\0').update(bytes).digest('hex'),d.git_blob);
  assert(!Object.hasOwn(d,'mathematical_status'));
 }
});
test('owned formal supplier lookup retains exact declarations and source scope without new acceptance',()=>{
 const hits=searchSources(corpus,'actual_total_original_strategy_has_bounded_plan',new Set(['CB-G7-001']));
 const hit=hits.find(d=>d.url.endsWith('/docs/EXISTING-LEAN-CLAIM-BINDINGS.md'));
 assert(hit);assert(hit.url.includes('/fa627492d9521a72a604952527d570571fe0fff7/'));
 assert(hit.bindings.some(b=>b.claim_id==='CB-G7-001'&&b.role==='owned_reading_join_source'&&b.source_join_kind==='formal_source_binding_not_new_acceptance'));
 assert.match(hit.body,/CorrectRun/);assert.match(hit.body,/cofacial/i);
 assert(!Object.hasOwn(hit,'mathematical_status'));
 assert.match(joins.find(j=>j.kind==='formal_source_binding_not_new_acceptance').explanation,/not new mathematics/);
});
test('reading-source projection validates identity and URLs before fetching and normalizes artifact hosts',()=>{
 const prefix='https://github.com/Sodelin/Research-Commons/blob/'+'a'.repeat(40)+'/';
 const link={url:prefix+'proof.md',label:'Owned source'},join={claim_ids:['TEST'],kind:'source_only',links:[link]};
 assert.throws(()=>readingReferences([join],[]),/identity/);
 assert.throws(()=>readingReferences([{...join,links:[{...link,url:link.url+'#access_token=secret'}]}],[{id:'TEST'}]),/Unsafe/);
 const pinned={...link,expected_sha256:'a'.repeat(64),expected_bytes:5};
 assert.throws(()=>readingReferences([{...join,links:[pinned,{...pinned,expected_bytes:6}]}],[{id:'TEST'}]),/Conflicting/);
 assert.throws(()=>readingReferences([{...join,links:[{...pinned,expected_sha256:'invalid'}]}],[{id:'TEST'}]),/Invalid owned/);
 assert.equal(readingReferences([{...join,links:[{...link,url:prefix+'proof.md#theorem'}]}],[{id:'TEST'}]).length,0);
 const claim={id:'TEST',accepted_artifacts:[{...link,url:link.url.replace('github.com','GITHUB.com:443')}]},before=JSON.stringify(claim);
 assert.equal(artifactReferences([claim])[0].url,link.url);
 assert.equal(JSON.stringify(claim),before);
});
test('all58 recovered G3 notes retain public byte pins and literal component roles, not master acceptance',()=>{
 const notes=corpus.documents.filter(d=>d.expected_sha256&&d.bindings.some(b=>b.role.startsWith('recovered_')));assert.equal(notes.length,58);
 assert.equal(corpus.catalogues[0].git_blob,'b9fdb781d1455d42d28033939bc07fd77f9b8dd2');
 for(const d of notes){assert.equal(d.expected_sha256,d.sha256);assert.equal(d.expected_git_blob,d.git_blob);assert.equal(d.expected_bytes,d.bytes);assert(d.url.endsWith('.md'));assert(d.bindings.every(b=>!b.claim_id));}
 const results=searchSources(corpus,'G3-SUPPLIED-WORD-ADMISSION');assert(results.length>0);
 const binding=results.flatMap(d=>d.bindings).find(b=>b.catalogue_key==='G3-SUPPLIED-WORD-ADMISSION');
 assert.equal(binding.catalogue_record.proof_authorship,'complete_for_the_named_claim_not_for_its_broader_extension');
 assert.match(binding.catalogue_record.independent_review,/not_newly/);
 assert.match(binding.catalogue_record.gap,/formal receiver gap/);
 assert.throws(()=>recoveredReferences({entries:[]},{files:[{kind:'authored_mathematical_note',name:'../escape.md'}]},'https://github.com/Sodelin/Research-Commons/blob/'+'a'.repeat(40)+'/notes/'));
});
test('older external G3 suppliers retain owner pins and later reviews without closing the master or changing the frozen census',()=>{
 const j=joins.find(j=>j.kind==='completed_external_suppliers_not_master_acceptance');assert(j);
 assert.match(j.explanation,/G3 recognition remains OPEN/);assert.match(j.explanation,/outside the frozen 58-note/);
 const pins=j.links.filter(l=>l.expected_sha256);assert.equal(pins.length,6);
 for(const p of pins){const d=corpus.documents.find(d=>d.url===p.url);assert(d);assert.equal(d.bytes,p.expected_bytes);assert.equal(d.sha256,p.expected_sha256);if(p.expected_git_blob)assert.equal(d.git_blob,p.expected_git_blob);assert(d.bindings.some(b=>b.source_join_kind===j.kind));}
 const hits=searchSources(corpus,'COMPLETED SUPPORT',new Set(['CB-G3-004']));assert(hits.some(d=>d.url.endsWith('/COMPLETED-SUPPORT-BOUND-ATTEMPT.md')));
 assert.equal(data.claims.find(c=>c.id==='CB-G3-004').mathematical_status,'open');
 const assessment=searchSources(corpus,'subjective reuse update').find(d=>d.url.endsWith('/SUBJECTIVE-REUSE-UPDATE-110.md'));assert(assessment);
 assert(assessment.bindings.every(b=>!b.claim_id&&b.role==='subjective_assessment_not_scientific_acceptance'));
});
test('wider archive paths are unique immutable regular-source links with explicit exclusions',async()=>{
 const catalog=JSON.parse(await readFile(new URL('../dist/archive-catalog.json',import.meta.url)));
 assert.equal(catalog.documents.length,catalog.coverage.documents);assert.equal(catalog.documents.length,5829);
 assert.equal(new Set(catalog.documents.map(d=>d.path)).size,catalog.documents.length);
 assert(catalog.coverage.excluded_subtrees.includes('docs/discovery'));
 for(const d of catalog.documents){assert(d.url.includes('/blob/'+catalog.commit+'/'));assert.match(d.git_blob,/^[a-f0-9]{40}$/);assert(!Object.hasOwn(d,'mathematical_status'));assert(!d.path.startsWith('sessions/'));}
 const hits=searchArchive(catalog,'calendar metric');assert(hits.length>0);assert(hits.every(d=>/calendar/i.test(d.path)&&/metric/i.test(d.path)));
 assert.equal(searchArchive(catalog,'zzzz-missing-source-path').length,0);
});
test('source retrieval finds body content and preserves source roles and claim facet boundaries',()=>{
 const before=JSON.stringify(corpus),hits=searchSources(corpus,'calibrated decoder');
 assert(hits.length>0);assert(hits.some(d=>d.body.toLowerCase().includes('calibrated')));
 assert(hits.every(d=>(d.body+' '+JSON.stringify(d.bindings)).toLowerCase().includes('calibrated')));
 assert(searchSources(corpus,'calibrated decoder',new Set(['NONEXISTENT'])).length===0);
 assert.equal(searchSources(corpus,'zzzz-absent-body-token').length,0);
 assert.equal(JSON.stringify(corpus),before);
 assert(sourceExcerpt('a '.repeat(200)+'needle target','needle').includes('needle'));
});
test('artifact projection refuses private services, mutable revisions and signed URLs',()=>{
 const claim={id:'TEST',accepted_artifacts:[
  {url:'https://github.com/Sodelin/Research-Commons/blob/main/source.md'},
  {url:'https://drive.google.com/file/d/test'},
  {url:'https://github.com/Sodelin/Research-Commons/blob/'+'a'.repeat(40)+'/source.md?token=secret'},
 ]};assert.deepEqual(artifactReferences([claim]),[]);
});

test('fixed-base arithmetic supplier remains author-complete only and outside original G3 closure',()=>{
 const j=joins.find(j=>j.kind==='author_complete_hand_supplier_not_independent_acceptance');assert(j);
 assert.match(j.explanation,/not independently reviewed/);assert.match(j.explanation,/ONE shared count vector/);assert.match(j.explanation,/stays OPEN/);assert.match(j.explanation,/Signs, retuned/);
 const p=j.links.find(l=>l.expected_sha256),d=corpus.documents.find(d=>d.url===p.url);assert(d);
 assert.equal(d.bytes,14796);assert.equal(d.sha256,p.expected_sha256);assert.equal(d.git_blob,p.expected_git_blob);
 assert(d.bindings.some(b=>b.claim_id==='CB-G3-004'&&b.source_join_kind===j.kind));
 assert(searchSources(corpus,'G3-ARITH-INDEP-RECIP-EQ-01',new Set(['CB-G3-004'])).some(d=>d.url===p.url));
 assert(!data.claims.find(c=>c.id==='CB-G3-004').accepted_artifacts.some(a=>a.url===p.url));
 assert.equal(data.claims.find(c=>c.id==='CB-G3-004').mathematical_status,'open');
});

test('P1 conditional testing transfer remains complete while its uniform-risk premise stays unsupplied',()=>{
 const j=joins.find(j=>j.kind==='recovered_conditional_transfer_not_uniform_rate');assert(j);
 assert.deepEqual(j.claim_ids,['CB-PHYS-P1-001','CB-PHYS-P1-002']);assert.match(j.explanation,/EVERY prior/);assert.match(j.explanation,/exactly n physical copies per unknown source/);assert.match(j.explanation,/remains UNSUPPLIED/);assert.match(j.explanation,/completed suppliers/);
 for(const p of j.links.filter(p=>p.expected_sha256)){const d=corpus.documents.find(d=>d.url===p.url);assert(d);assert.equal(d.bytes,p.expected_bytes);assert.equal(d.sha256,p.expected_sha256);assert.equal(d.git_blob,p.expected_git_blob);assert(d.bindings.some(b=>b.source_join_kind===j.kind));}
 const hits=searchSources(corpus,'finite minimax',new Set(['CB-PHYS-P1-002']));assert(hits.some(d=>j.links.some(l=>l.url===d.url)));
 assert.equal(data.claims.find(c=>c.id==='CB-PHYS-P1-002').completion.mathematical_claim_complete,true);
});

test('nanowire all-pair decision theorem does not masquerade as an executed original-instance certificate',()=>{
 const j=joins.find(j=>j.kind==='reviewed_decidability_not_executed_instance');assert(j);assert.deepEqual(j.claim_ids,['CB-NANO-001','CB-NANO-005']);
 for(const pattern of [/TWO FIXED/,/EVERY field/,/outside the universal field quantifier/,/actual original-instance decision/,/BOTH margin classes/,/greater than 2epsilon/,/No decision\/separation certificate/])assert.match(j.explanation,pattern);
 for(const p of j.links.filter(l=>l.expected_sha256)){const d=corpus.documents.find(d=>d.url===p.url);assert(d);assert.equal(d.bytes,p.expected_bytes);assert.equal(d.sha256,p.expected_sha256);assert.equal(d.git_blob,p.expected_git_blob);assert(d.bindings.some(b=>b.source_join_kind===j.kind));}
 const hits=searchSources(corpus,'bounded class',new Set(['CB-NANO-001']));assert(hits.some(d=>j.links.some(l=>l.url===d.url)));
 assert.match(data.claims.find(c=>c.id==='CB-NANO-001').separate_downstream_or_validation_work,/existence is unresolved/);
});

test('root-order logarithm-zero classification preserves its different count contract and missing decider',()=>{
 const j=joins.find(j=>j.kind==='author_complete_order_logzero_classification_not_decider');assert(j);
 for(const pattern of [/ONE common integer/,/Turing-equivalent/,/not a cap\/rank ladder/,/not independently reviewed/,/DIFFERENT count\/equality-only contract/,/physical enforcement.*NOT proved/,/No total log-zero algorithm/])assert.match(j.explanation,pattern);
 const p=j.links.find(l=>l.expected_sha256),d=corpus.documents.find(d=>d.url===p.url);assert(d);assert.equal(d.bytes,p.expected_bytes);assert.equal(d.sha256,p.expected_sha256);assert.equal(d.git_blob,p.expected_git_blob);
 assert(searchSources(corpus,'G3-ARITH-ROOT-ORDER-LOGZERO-01',new Set(['CB-G3-004'])).some(d=>d.url===p.url));
 assert(d.bindings.some(b=>b.source_join_kind===j.kind));assert.equal(data.claims.find(c=>c.id==='CB-G3-004').mathematical_status,'open');
 assert(joins.some(j=>j.kind==='author_complete_hand_supplier_not_independent_acceptance'));
});

test('dated successor lookup exposes retired suppliers and remaining master quantifiers',()=>{
 const progress=joins.find(j=>j.kind==='owner_adopted_progress_not_master_closure');
 assert(progress);assert.match(progress.explanation,/cap9.*cap12/);
 assert.match(progress.explanation,/total input-computable ONE-witness/);
 assert.match(progress.explanation,/not independent correctness/);
 const body=corpus.documents.find(d=>d.url===progress.links[0].url);
 assert(body);assert.match(body.body,/Retire from the derivation queue/);
 assert.match(body.body,/EVERY finite admitted rival/);
 const terminal=joins.find(j=>j.kind==='retained_profile_pass_not_all_claim_acceptance');
 assert.match(terminal.explanation,/workflow failed overall/);
 assert.match(terminal.explanation,/do not automatically inherit/);
 assert(corpus.documents.some(d=>d.url===terminal.links[0].url));
});

test('original successor proofs are retrievable by their literal stable keys with source-only roles',()=>{
 const j=joins.find(j=>j.kind==='author_hand_original_supplier_bodies_not_master_closure');
 assert.deepEqual(j.claim_ids,['CB-G3-004']);assert.equal(j.links.length,3);
 for(const [i,key] of ['G3-MATCHED-FULL-BAND-LINEAR-ABSORPTION-01','G3-RESONANT-ORDINARY-FORCING-ENERGY-01','G3-OBSERVED-COHORT-SURVIVAL-01'].entries()){
  const l=j.links[i],d=corpus.documents.find(d=>d.url===l.url);assert(d);
  assert.equal(d.bytes,l.expected_bytes);assert.equal(d.sha256,l.expected_sha256);assert.equal(d.git_blob,l.expected_git_blob);
  assert(searchSources(corpus,key,new Set(['CB-G3-004'])).some(d=>d.url===l.url));
  assert(d.bindings.every(b=>b.claim_id==='CB-G3-004'));
 }
 assert.match(j.explanation,/complete cap9/);assert.match(j.explanation,/complete cap12/);
 assert.match(j.explanation,/older linear proof.*reopen the completed successor/);
 assert.match(j.explanation,/Empty palette is not automatic NO/);
 assert.equal(data.claims.find(c=>c.id==='CB-G3-004').mathematical_status,'open');
});
