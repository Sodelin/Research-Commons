import test from 'node:test';import assert from 'node:assert/strict';import {readFile} from 'node:fs/promises';
import {JSDOM} from 'jsdom';
const root=new URL('../dist/',import.meta.url);
const html=await readFile(new URL('index.html',root),'utf8');
const docs={};for(const name of ['claims.json','source.json','reading-joins.json','source-corpus.json','archive-catalog.json','subjective-reuse-ranking.json','ranking-source.json'])docs[name]=JSON.parse(await readFile(new URL(name,root)));
const wait=async fn=>{for(let i=0;i<80;i++){if(fn())return;await new Promise(r=>setTimeout(r,10));}assert.fail('Reader did not reach the expected DOM state.');};
test('reader journeys: deep link, search, evidence, origin, graph, reuse, stale-source recovery',async t=>{
 const dom=new JSDOM(html,{url:'https://reader.test/?q=quantum#CB-PHYS-P5-004',pretendToBeVisual:true});
 let copied='',offline=false,credentialSource=false;
 for(const k of ['window','document','location','history','navigator'])Object.defineProperty(globalThis,k,{value:dom.window[k],configurable:true});
 globalThis.innerWidth=1400;globalThis.matchMedia=()=>({matches:true});globalThis.addEventListener=dom.window.addEventListener.bind(dom.window);
 Object.defineProperty(dom.window.navigator,'clipboard',{value:{writeText:async text=>{copied=text;}}});
 globalThis.fetch=async url=>{
  if(String(url).startsWith('https://')){
   if(offline)throw Error('Network unavailable');
   if(credentialSource&&String(url).includes('raw.githubusercontent.com')){const source=structuredClone(docs['claims.json']);source.claims[0].accepted_artifacts[0].url='https://example.org/proof#access_token=synthetic-fragment-value';return {ok:true,json:async()=>source};}
   return {ok:true,json:async()=>({sha:credentialSource?'b'.repeat(40):docs['source.json'].commit})};
  }
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
 await t.test('prior-work paper is reachable even without an origin URL',()=>{
  location.hash='CB-NANUQ-002';dom.window.dispatchEvent(new dom.window.HashChangeEvent('hashchange'));
  const paper=[...$('detail').querySelectorAll('a')].find(a=>a.href.includes('10.1007/s11538-025-01549-4'));
  assert(paper);assert($('detail').textContent.includes('prior work'));
  assert(!$('detail').textContent.includes('No literature URL is indexed'));
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
 await t.test('G7 declaration supplier is visible and exported with its whole-history and native exclusions',async()=>{
  location.hash='CB-G7-001';dom.window.dispatchEvent(new dom.window.HashChangeEvent('hashchange'));
  assert($('detail').textContent.includes('every admitted same source for the whole history'));
  assert([...$('detail').querySelectorAll('a')].some(a=>a.href.includes('/fa627492d9521a72a604952527d570571fe0fff7/docs/EXISTING-LEAN-CLAIM-BINDINGS.md')));
  copied='';[...$('detail').querySelectorAll('button')].find(x=>x.textContent==='Copy agent reuse record').click();
  await wait(()=>copied.startsWith('{'));
  const packet=JSON.parse(copied);
  assert(JSON.stringify(packet).includes('formal_source_binding_not_new_acceptance'));
  assert(JSON.stringify(packet).includes('native policy AST'));
 });
 await t.test('evidence-body search loads separately and links immutable sources back to claims',async()=>{
  $('reset').click();[...document.querySelectorAll('button')].find(b=>b.textContent.startsWith('Load evidence search')).click();
  await wait(()=>document.querySelector('.source-hit'));
  $('search').value='calibrated decoder';$('search').dispatchEvent(new dom.window.Event('input'));
  await wait(()=>location.search.includes('calibrated'));
  assert(document.querySelector('.source-hit a').href.includes('/blob/'));
  assert(document.querySelector('.source-results').textContent.includes('Source hits do not establish acceptance'));
  [...document.querySelectorAll('.source-hit button')].find(b=>b.textContent.includes('CB-G7-001')).click();assert($('detail').textContent.includes('CB-G7-001'));
 });
 await t.test('recovered component lookup renders literal scope/review without inventing master acceptance',async()=>{
  $('reset').click();$('search').value='G3-SUPPLIED-WORD-ADMISSION';$('search').dispatchEvent(new dom.window.Event('input'));
  await wait(()=>document.querySelector('.source-hit')?.textContent.includes('G3-SUPPLIED-WORD-ADMISSION'));
  assert(document.querySelector('.source-hit').textContent.includes('formal receiver gap'));
  assert(!document.querySelector('.source-hit').querySelector('button'));
 });
 await t.test('archive search loads wider paths and leaves unknown scientific status explicit',async()=>{
  $('reset').click();[...document.querySelectorAll('button')].find(b=>b.textContent==='Load wider archive search').click();
  await wait(()=>document.querySelector('.archive-hit'));
  $('search').value='calendar metric';$('search').dispatchEvent(new dom.window.Event('input'));
  await wait(()=>location.search.includes('calendar'));
  assert(document.querySelector('.archive-hit a').href.includes('/blob/'));
  assert(document.querySelector('.archive-hit').textContent.includes('status unverified'));
 });
 await t.test('combined claim/review filters and dated subjective ordering keep unranked entries distinct',()=>{
  $('reset').click();$('kind').value='theorem';$('review').value='accepted_scoped_hand_review';$('sort').value='subjective_reuse';$('kind').dispatchEvent(new dom.window.Event('change'));
  assert(document.querySelector('.claim').textContent.includes('CB-G6-001'));
  assert($('ranking-note').textContent.includes('not an importance'));
  assert(location.search.includes('review='));
  $('reset').click();$('topic').value='Sequences';$('sort').value='subjective_reuse';$('topic').dispatchEvent(new dom.window.Event('change'));
  assert($('ranking-note').textContent.includes('newer/unranked'));
 });
 await t.test('historical component receipts retain exact process-exit and written/formal boundaries',()=>{
  $('reset').click();location.hash='CB-FEEDBACK-004';dom.window.dispatchEvent(new dom.window.HashChangeEvent('hashchange'));
  assert($('detail').textContent.includes('exit was not retrieved'));
  assert($('detail').textContent.includes('written/reviewed, not formally proved'));
  assert($('detail').textContent.includes('kernel checked components with recorded exit limit'));
 });
 await t.test('credential-bearing latest source is refused while bundled data and safe links remain usable',async()=>{
  credentialSource=true;$('refresh').click();await wait(()=>$('freshness').textContent.includes('Showing the verified bundled snapshot'));
  assert(!$('results').textContent.includes('synthetic-fragment-value'));
  assert(![...document.querySelectorAll('a')].some(a=>a.href.includes('access_token')));
  assert($('source-link').href.includes(docs['source.json'].commit));credentialSource=false;
 });
 await t.test('offline latest-source failure preserves a usable source snapshot',async()=>{
  $('reset').click();location.hash='CB-G6-001';dom.window.dispatchEvent(new dom.window.HashChangeEvent('hashchange'));
  offline=true;$('refresh').click();await wait(()=>$('freshness').textContent.includes('Showing the verified bundled snapshot'));
  assert(document.querySelectorAll('.claim').length>0);assert($('detail').textContent.includes('CB-G6-001'));
 });
 dom.window.close();
});
