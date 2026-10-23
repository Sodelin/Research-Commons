#!/usr/bin/env node
import {readFile} from 'node:fs/promises';
import {validate, search, reusePacket, STATUS, ORIGIN} from '../dist/model.mjs';
import {searchSources,sourceExcerpt} from '../dist/source-search.mjs';
const args=process.argv.slice(2); let f={}, refresh=false,sources=false;
for(let i=0;i<args.length;i++){
  const k=args[i];
  if(k==='--refresh'){refresh=true;continue;}
  if(k==='--sources'){sources=true;continue;}
  if(!['--query','--status','--origin','--topic'].includes(k) || !args[i+1]) throw Error('Use --query TEXT --status KEY --origin KEY --topic TEXT [--refresh].');
  f[k==='--query'?'q':k.slice(2)]=args[++i];
}
if(f.status && !Object.hasOwn(STATUS,f.status)) throw Error('Unknown status filter.');
if(f.origin && !Object.hasOwn(ORIGIN,f.origin)) throw Error('Unknown origin filter.');
let data=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));
let meta=JSON.parse(await readFile(new URL('../dist/source.json',import.meta.url)));
const joins=JSON.parse(await readFile(new URL('../dist/reading-joins.json',import.meta.url))).joins;
if(refresh){
 const response=await fetch('https://api.github.com/repos/Sodelin/Research-Commons/commits/main',{signal:AbortSignal.timeout(15000)});
 if(!response.ok)throw Error(`Main lookup failed: ${response.status}`);
 const commit=(await response.json()).sha;
 const source=await fetch(`https://raw.githubusercontent.com/Sodelin/Research-Commons/${commit}/docs/claims.json`,{signal:AbortSignal.timeout(15000)});
 if(!source.ok)throw Error(`Register lookup failed: ${source.status}`);
 data=await source.json();meta={repository:'Sodelin/Research-Commons',commit,path:'docs/claims.json',source_updated_utc:data.updated_utc};
}
validate(data);
if(sources){
 const corpus=JSON.parse(await readFile(new URL('../dist/source-corpus.json',import.meta.url)));
 const allowed=new Set(search(data.claims,{...f,q:''}).map(c=>c.id));
 console.log(JSON.stringify({coverage:corpus.coverage,registry_source:corpus.registry_source,
   current_registry_source:meta,results:searchSources(corpus,f.q??'',allowed).map(({body,...d})=>({...d,excerpt:sourceExcerpt(body,f.q??'')}))},null,2));
 process.exit(0);
}
console.log(JSON.stringify({coverage:data.coverage, registry_source:meta,
 results:search(data.claims,f).map(c=>reusePacket(c,meta,joins))},null,2));
