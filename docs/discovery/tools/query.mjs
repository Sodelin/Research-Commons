#!/usr/bin/env node
import {readFile} from 'node:fs/promises';
import {validate, search, reusePacket, STATUS, ORIGIN,sortClaims,validateRanking,compareRegisters,validateAssessments} from '../dist/model.mjs';
import {searchSources,sourceExcerpt,searchArchive} from '../dist/source-search.mjs';
const args=process.argv.slice(2); let f={}, refresh=false,sources=false,archive=false,changes=false;
let limit=25,offset=0;
for(let i=0;i<args.length;i++){
  const k=args[i];
  if(k==='--limit'||k==='--offset'){const value=Number(args[++i]);if(!Number.isSafeInteger(value)||value<0||(k==='--limit'&&(value<1||value>100)))throw Error('Use --limit 1..100 and nonnegative --offset.');if(k==='--limit')limit=value;else offset=value;continue;}
  if(k==='--refresh'){refresh=true;continue;}
  if(k==='--sources'){sources=true;continue;}
  if(k==='--archive'){archive=true;continue;}
  if(k==='--changes'){changes=true;continue;}
  if(!['--query','--status','--origin','--topic','--programme','--kind','--review','--formal-status','--novelty','--sort'].includes(k) || !args[i+1]) throw Error('Use --query TEXT, combinable --topic/--programme/--kind/--status/--origin/--review/--formal-status/--novelty, --sort subjective_reuse, [--refresh | --sources | --archive].');
  f[k==='--query'?'q':k.slice(2).replaceAll('-','_')]=args[++i];
}
if(f.status && !Object.hasOwn(STATUS,f.status)) throw Error('Unknown status filter.');
if(f.origin && !Object.hasOwn(ORIGIN,f.origin)) throw Error('Unknown origin filter.');
if(changes&&(!refresh||sources||archive||f.sort))throw Error('--changes requires --refresh and compares claim snapshots; --sources, --archive and --sort belong to separate views.');
if(archive){
 if(sources||refresh||Object.keys(f).some(k=>k!=='q'))throw Error('--archive searches pinned public paths only. Use --query; claim facets, --sources and --refresh belong to the separate register/evidence view.');
 const catalog=JSON.parse(await readFile(new URL('../dist/archive-catalog.json',import.meta.url)));
 const hits=searchArchive(catalog,f.q??'');
 console.log(JSON.stringify({repository:catalog.repository,commit:catalog.commit,coverage:catalog.coverage,
   total:hits.length,offset,limit,next_offset:offset+limit<hits.length?offset+limit:null,results:hits.slice(offset,offset+limit)},null,2));process.exit(0);
}
let data=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));
let meta=JSON.parse(await readFile(new URL('../dist/source.json',import.meta.url)));
const bundled=validate(data),bundledMeta=meta;
const navigation=JSON.parse(await readFile(new URL('../dist/reading-joins.json',import.meta.url))),joins=navigation.joins;
const assessments=validateAssessments(navigation.subjective_assessments??[]);
if(refresh){
 const response=await fetch('https://api.github.com/repos/Sodelin/Research-Commons/commits/main',{signal:AbortSignal.timeout(15000)});
 if(!response.ok)throw Error(`Main lookup failed: ${response.status}`);
 const commit=(await response.json()).sha;
 if(!/^[0-9a-f]{40}$/.test(commit))throw Error('Invalid source commit.');
 const source=await fetch(`https://raw.githubusercontent.com/Sodelin/Research-Commons/${commit}/docs/claims.json`,{signal:AbortSignal.timeout(15000)});
 if(!source.ok)throw Error(`Register lookup failed: ${source.status}`);
 data=await source.json();meta={repository:'Sodelin/Research-Commons',commit,path:'docs/claims.json',source_updated_utc:data.updated_utc};
}
validate(data);
if(changes){
 const diff=compareRegisters(bundled,data),currentIDs=new Set(data.claims.map(c=>c.id));
 const candidates=[...data.claims,...bundled.claims.filter(c=>!currentIDs.has(c.id))];
 const allowed=new Set(search(candidates,f).map(c=>c.id));
 const hits=diff.records.filter(r=>allowed.has(r.claim_id));
 console.log(JSON.stringify({comparison:{baseline:bundledMeta,current:meta,added:diff.added,changed:diff.changed,removed:diff.removed,unchanged:diff.unchanged,limitation:diff.limitation},
  total:hits.length,offset,limit,next_offset:offset+limit<hits.length?offset+limit:null,results:hits.slice(offset,offset+limit)},null,2));process.exit(0);
}
const ranking=validateRanking(JSON.parse(await readFile(new URL('../dist/subjective-reuse-ranking.json',import.meta.url))));
const rankingSource=JSON.parse(await readFile(new URL('../dist/ranking-source.json',import.meta.url)));
if(sources){
 if(f.sort)throw Error('--sort orders claim cards only; source hits retain their own evidence roles, not a transferred claim rank.');
 const corpus=JSON.parse(await readFile(new URL('../dist/source-corpus.json',import.meta.url)));
 const allowed=Object.keys(f).some(k=>!['q','sort'].includes(k)&&f[k])?new Set(search(data.claims,{...f,q:''}).map(c=>c.id)):null;
 const hits=searchSources(corpus,f.q??'',allowed);
 console.log(JSON.stringify({coverage:corpus.coverage,registry_source:corpus.registry_source,
   total:hits.length,offset,limit,next_offset:offset+limit<hits.length?offset+limit:null,
   current_registry_source:meta,results:hits.slice(offset,offset+limit).map(({body,...d})=>({...d,excerpt:sourceExcerpt(body,f.q??'')}))},null,2));
 process.exit(0);
}
const hits=sortClaims(search(data.claims,f),f.sort,ranking);
console.log(JSON.stringify({coverage:data.coverage, registry_source:meta,total:hits.length,offset,limit,next_offset:offset+limit<hits.length?offset+limit:null,
 results:hits.slice(offset,offset+limit).map(c=>reusePacket(c,meta,joins,ranking,rankingSource,assessments))},null,2));
