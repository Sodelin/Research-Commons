import test from 'node:test';import assert from 'node:assert/strict';import {readFile} from 'node:fs/promises';
import {JSDOM} from 'jsdom';
const root=new URL('../dist/',import.meta.url);
const html=await readFile(new URL('index.html',root),'utf8');
const docs={};for(const name of ['claims.json','source.json','reading-joins.json'])docs[name]=JSON.parse(await readFile(new URL(name,root)));
const wait=async fn=>{for(let i=0;i<80;i++){if(fn())return;await new Promise(r=>setTimeout(r,10));}assert.fail('Reader did not reach the expected DOM state.');};
test('reader journeys: deep link, search, evidence, origin, graph, reuse, stale-source recovery',async t=>{
 const dom=new JSDOM(html,{url:'https://reader.test/?q=quantum#CB-PHYS-P5-004',pretendToBeVisual:true});
 let copied='',offline=false;
 for(const k of ['window','document','location','history','navigator'])Object.defineProperty(globalThis,k,{value:dom.window[k],configurable:true});
 globalThis.innerWidth=1400;globalThis.matchMedia=()=>({matches:true});globalThis.addEventListener=dom.window.addEventListener.bind(dom.window);
 Object.defineProperty(dom.window.navigator,'clipboard',{value:{writeText:async text=>{copied=text;}}});
 globalThis.fetch=async url=>{
  if(String(url).startsWith('https://')){if(offline)throw Error('Network unavailable');return {ok:true,json:async()=>({sha:docs['source.json'].commit})};}
  const name=String(url).replace('./','');return {ok:!!docs[name],json:async()=>structuredClone(docs[name])};
 };
 await import('../dist/app.mjs');
 await wait(()=>document.querySelectorAll('.claim').length>0);
 const $=id=>document.getElementById(id);
 await t.test('deep link and source-defined P5 completion/evidence are displayed',()=>{
  assert.equal($('search').value,'quantum');assert($('detail').textContent.includes('CB-PHYS-P5-004'));
  assert($('detail').textContent.includes('Hand-proof verdict'));
  assert($('detail').textContent.includes('Mathematical claim complete'));
  assert($('detail').textContent.includes('Separate downstream or validation work'));
  assert($('detail').textContent.includes('Formal verification'));
  assert.equal($('detail').querySelectorAll('script').length,0);
 });
 await t.test('copyable agent record has canonical provenance and scoped evidence',async()=>{
  [...$('detail').querySelectorAll('button')].find(x=>x.textContent==='Copy agent reuse record').click();
  await wait(()=>copied.startsWith('{'));const packet=JSON.parse(copied);
  assert.equal(packet.claim_id,'CB-PHYS-P5-004');assert.equal(packet.completion.mathematical_claim_complete,true);assert.equal(packet.completion.proof_derivation_required,false);assert.equal(packet.registry_source.commit,docs['source.json'].commit);
 });
 await t.test('published-question filter works across the actual source data',async()=>{
  $('reset').click();$('origin').value='published_open_problem';$('origin').dispatchEvent(new dom.window.Event('change'));
  const expected=docs['claims.json'].claims.filter(c=>c.origin.category==='published_open_problem').length;assert($('count').textContent.startsWith(expected+' of'));assert(document.querySelectorAll('.claim').length>0);
 });
 await t.test('missing direct literature URL is labelled as an indexing gap',()=>{
  const missing=docs['claims.json'].claims.find(c=>c.origin.category==='published_open_problem'&&!c.origin.source_url);
  assert(missing,'This source successor includes a literature-link gap fixture');
  location.hash=missing.id;dom.window.dispatchEvent(new dom.window.HashChangeEvent('hashchange'));
  assert($('detail').textContent.includes('direct original-paper link is not indexed'));
 });
 await t.test('typing searches and no-result recovery does not claim missing mathematics',async()=>{
  $('reset').click();$('search').value='independant routing';$('search').dispatchEvent(new dom.window.Event('input'));
  await wait(()=>document.querySelectorAll('.claim').length>0&&location.search.includes('independant'));
  $('search').value='zzzz-no-such-research';$('search').dispatchEvent(new dom.window.Event('input'));
  await wait(()=>document.querySelector('.empty'));assert(document.querySelector('.empty').textContent.includes('not evidence'));
 });
 await t.test('before-work mode and completed G6 implementation links are discoverable',()=>{
  $('reset').click();document.querySelector('[data-mode="reuse"]').click();assert.equal($('reuse-guide').hidden,false);
  location.hash='CB-G6-001';dom.window.dispatchEvent(new dom.window.HashChangeEvent('hashchange'));
  assert($('detail').textContent.includes('Exact native first-writer gap'));
 });
 await t.test('offline latest-source failure preserves a usable source snapshot',async()=>{
  offline=true;$('refresh').click();await wait(()=>$('freshness').textContent.includes('Showing the verified bundled snapshot'));
  assert(document.querySelectorAll('.claim').length>0);assert($('detail').textContent.includes('CB-G6-001'));
 });
 dom.window.close();
});
