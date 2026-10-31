import{mkdtempSync,mkdirSync,copyFileSync,symlinkSync,writeFileSync,rmSync}from'node:fs';import{tmpdir}from'node:os';import{join,dirname}from'node:path';
import test from 'node:test';import assert from 'node:assert/strict';import {execFileSync,spawnSync,spawn}from'node:child_process';import{fileURLToPath}from'node:url';
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
 assert.equal(ranked.results[0].subjective_reuse.later_assessments[0].source_count,110);
 assert.match(ranked.results[0].subjective_reuse.purpose,/Not mathematical acceptance/);
});

test('source refresh rejects credential fragments before persistence through the real shared validator',()=>{
 const script=fileURLToPath(new URL('../tools/test_refresh.py',import.meta.url));
 execFileSync('python3',[script],{encoding:'utf8',maxBuffer:64*1024,timeout:15000,stdio:'pipe'});
});
test('agent change lookup compares exact sources in RAM with bounded results and refuses unsupported modes',()=>{
 const sourceURL=new URL('../dist/claims.json',import.meta.url).href;
 const mock=`import {readFile} from 'node:fs/promises';const data=JSON.parse(await readFile(new URL(${JSON.stringify(sourceURL)})));const c=structuredClone(data.claims[0]);c.id='TEST-NEWLY-INDEXED';data.claims.push(c);data.claims[0].separate_downstream_or_validation_work='Synthetic changed source';globalThis.fetch=async url=>{if(String(url).endsWith('/commits/main'))return {ok:true,json:async()=>({sha:'b'.repeat(40)})};if(String(url).includes('/'+ 'b'.repeat(40)+'/docs/claims.json'))return {ok:true,json:async()=>data};throw Error('Unexpected fixture request');};`;
 const out=JSON.parse(execFileSync(process.execPath,['--import','data:text/javascript,'+encodeURIComponent(mock),cli,'--changes','--refresh','--limit','1'],{encoding:'utf8',timeout:15000,maxBuffer:2*1024*1024}));
 assert.equal(out.comparison.current.commit,'b'.repeat(40));assert.notEqual(out.comparison.baseline.commit,out.comparison.current.commit);
 assert.equal(out.comparison.added,1);assert.equal(out.comparison.changed,1);assert.equal(out.total,2);assert.equal(out.results.length,1);assert.equal(out.next_offset,1);
 assert.match(out.comparison.limitation,/not new discoveries/);
 for(const flags of [['--changes'],['--changes','--refresh','--archive'],['--changes','--refresh','--sort','subjective_reuse']]){
  const bad=spawnSync(process.execPath,[cli,...flags],{encoding:'utf8',timeout:10000});assert.notEqual(bad.status,0);assert.equal(bad.stdout,'');
 }
});

test('large paginated source JSON fully drains to a slow pipe before exit',async()=>{
 const fixture=mkdtempSync(join(tmpdir(),'commons-pipe-'));
 try {
  mkdirSync(join(fixture,'tools'));
  copyFileSync(cli,join(fixture,'tools/query.mjs'));
  symlinkSync(join(dirname(cli),'research-results.mjs'),join(fixture,'tools/research-results.mjs'));
  symlinkSync(join(dirname(cli),'../dist'),join(fixture,'dist'));
  writeFileSync(join(fixture,'result-reference-coverage.json'),JSON.stringify({records:Array.from({length:100},(_,id)=>({id,description:'synthetic public reference '.repeat(2000)}))}));
  const child=spawn(process.execPath,[join(fixture,'tools/query.mjs'),'--reference-coverage','--limit','100'],{stdio:['ignore','pipe','pipe']});
  let out='',err='';child.stdout.setEncoding('utf8');child.stderr.setEncoding('utf8');
  child.stdout.on('data',chunk=>{out+=chunk;});child.stderr.on('data',chunk=>{err+=chunk;});child.stdout.pause();
  const done=new Promise((resolve,reject)=>{child.on('error',reject);child.on('close',code=>resolve(code));});
  setTimeout(()=>child.stdout.resume(),500);
  assert.equal(await done,0,err);assert(out.length>65536,'exercise stdout backpressure');
  const parsed=JSON.parse(out);assert.equal(parsed.results.length,100);assert.equal(parsed.next_offset,null);
 } finally {rmSync(fixture,{recursive:true,force:true});}
});
