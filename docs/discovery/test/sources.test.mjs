import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {artifactReferences,recoveredReferences,searchSources,sourceExcerpt,searchArchive} from '../dist/source-search.mjs';
const data=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));
const corpus=JSON.parse(await readFile(new URL('../dist/source-corpus.json',import.meta.url)));
test('public body corpus accounts for every selected immutable artifact and exact source bytes',()=>{
 const refs=artifactReferences(data.claims),byURL=new Map(refs.map(r=>[r.url,r]));
 assert.equal(corpus.coverage.canonical_artifact_references,refs.length);
 assert.equal(corpus.documents.length+corpus.coverage.unavailable.length,corpus.coverage.selected_references);
 assert.equal(new Set(corpus.documents.map(d=>d.url)).size,corpus.documents.length);
 for(const d of corpus.documents){
  if(byURL.has(d.url))assert.deepEqual(d.bindings.filter(b=>b.claim_id),byURL.get(d.url).bindings);
  else assert(d.bindings.every(b=>!b.claim_id&&b.role.startsWith('recovered_')));
  const bytes=Buffer.from(d.body);assert.equal(bytes.length,d.bytes);
  assert.equal(createHash('sha256').update(bytes).digest('hex'),d.sha256);
  assert.equal(createHash('sha1').update('blob '+bytes.length+'\0').update(bytes).digest('hex'),d.git_blob);
  assert(!Object.hasOwn(d,'mathematical_status'));
 }
});
test('all58 recovered G3 notes retain public byte pins and literal component roles, not master acceptance',()=>{
 const notes=corpus.documents.filter(d=>d.expected_sha256);assert.equal(notes.length,58);
 assert.equal(corpus.catalogues[0].git_blob,'b9fdb781d1455d42d28033939bc07fd77f9b8dd2');
 for(const d of notes){assert.equal(d.expected_sha256,d.sha256);assert.equal(d.expected_git_blob,d.git_blob);assert.equal(d.expected_bytes,d.bytes);assert(d.url.endsWith('.md'));assert(d.bindings.every(b=>!b.claim_id));}
 const results=searchSources(corpus,'G3-SUPPLIED-WORD-ADMISSION');assert(results.length>0);
 const binding=results.flatMap(d=>d.bindings).find(b=>b.catalogue_key==='G3-SUPPLIED-WORD-ADMISSION');
 assert.equal(binding.catalogue_record.proof_authorship,'complete_for_the_named_claim_not_for_its_broader_extension');
 assert.match(binding.catalogue_record.independent_review,/not_newly/);
 assert.match(binding.catalogue_record.gap,/formal receiver gap/);
 assert.throws(()=>recoveredReferences({entries:[]},{files:[{kind:'authored_mathematical_note',name:'../escape.md'}]},'https://github.com/Sodelin/Research-Commons/blob/'+'a'.repeat(40)+'/notes/'));
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
