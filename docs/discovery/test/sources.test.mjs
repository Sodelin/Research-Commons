import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {artifactReferences,searchSources,sourceExcerpt} from '../dist/source-search.mjs';
const data=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));
const corpus=JSON.parse(await readFile(new URL('../dist/source-corpus.json',import.meta.url)));
test('public body corpus accounts for every selected immutable artifact and exact source bytes',()=>{
 const refs=artifactReferences(data.claims),byURL=new Map(refs.map(r=>[r.url,r]));
 assert.equal(corpus.coverage.selected_references,refs.length);
 assert.equal(corpus.documents.length+corpus.coverage.unavailable.length,refs.length);
 assert.equal(new Set(corpus.documents.map(d=>d.url)).size,corpus.documents.length);
 for(const d of corpus.documents){
  assert.deepEqual(d.bindings,byURL.get(d.url).bindings);
  const bytes=Buffer.from(d.body);assert.equal(bytes.length,d.bytes);
  assert.equal(createHash('sha256').update(bytes).digest('hex'),d.sha256);
  assert.equal(createHash('sha1').update('blob '+bytes.length+'\0').update(bytes).digest('hex'),d.git_blob);
  assert(!Object.hasOwn(d,'mathematical_status'));
 }
});
test('source retrieval finds body content and preserves source roles and claim facet boundaries',()=>{
 const before=JSON.stringify(corpus),hits=searchSources(corpus,'calibrated decoder');
 assert(hits.length>0);assert(hits.every(d=>d.body.toLowerCase().includes('calibrated')));
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
