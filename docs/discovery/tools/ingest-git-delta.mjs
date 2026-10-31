#!/usr/bin/env node
// Complete local tree delta, not a capped directory API or a status refresh.
import {execFileSync} from 'node:child_process';
import {readFile,writeFile} from 'node:fs/promises';
import {identity} from './source-cache.mjs';
import {validateCorpus} from './source-merge.mjs';
const args=process.argv.slice(2),options={};
for(let i=0;i<args.length;i+=2){if(!['--repo','--from','--to','--base','--output'].includes(args[i])||!args[i+1]||options[args[i]])throw Error('Usage: ingest-git-delta.mjs --repo PATH --from COMMIT40 --to COMMIT40 --base CORPUS --output NEW_SUPPLEMENT');options[args[i]]=args[i+1];}
for(const key of ['--repo','--from','--to','--base','--output'])if(!options[key])throw Error(`Missing ${key}`);
for(const key of ['--from','--to'])if(!/^[a-f0-9]{40}$/.test(options[key]))throw Error('Immutable full commit IDs required');
const git=(...args)=>execFileSync('git',['-C',options['--repo'],...args],{maxBuffer:8*1024*1024,timeout:15000});
const remote=git('remote','get-url','origin').toString().trim();
if(!['https://github.com/Sodelin/Research-Commons.git','https://github.com/Sodelin/Research-Commons','git@github.com:Sodelin/Research-Commons.git'].includes(remote))throw Error('Only the explicit Research-Commons source repository is supported');
for(const key of ['--from','--to'])if(git('rev-parse',`${options[key]}^{commit}`).toString().trim()!==options[key])throw Error('Commit identity mismatch');
const baseBytes=await readFile(options['--base']),base=validateCorpus(JSON.parse(baseBytes));
const parts=git('diff','--name-status','-z','--no-renames',options['--from'],options['--to'],'--','research','handoffs','communications').toString().split('\0');parts.pop();
if(parts.length%2||parts.length>4000)throw Error('Delta exceeds 2000-path bound or is malformed');
const documents=[],excluded=[],unavailable=[];let total=0;
const prior=new Set(base.documents.map(d=>d.url));
for(let i=0;i<parts.length;i+=2){
 const [status,path]=parts.slice(i,i+2);
 if(status==='D'){excluded.push({path,reason:'Deleted from later tree; historical bodies retained'});continue;}
 if(!path.endsWith('.md')||/(^|\/)(vendor|node_modules|\.lake|source-store|dist|build)(\/|$)/.test(path)){excluded.push({path,reason:'Non-Markdown or dependency/generated subtree; JSON/status/comments/Lean require separate readers'});continue;}
 if(documents.length>=100)throw Error('Delta exceeds 100-body bound; choose a smaller immutable interval');
 const url=`https://github.com/Sodelin/Research-Commons/blob/${options['--to']}/${path}`;
 if(prior.has(url)){excluded.push({path,reason:'Already indexed at this exact URL'});continue;}
 try{
  const tree=git('ls-tree','-z',options['--to'],'--',path).toString();
  const entry=tree.match(/^100(?:644|755) blob ([a-f0-9]{40})\t[^\0]+\0$/);if(!entry)throw Error('Not one regular Git blob');
  const size=Number(git('cat-file','-s',entry[1]).toString());if(!Number.isSafeInteger(size)||size>512*1024)throw Error('Body exceeds 512 KiB');
  const bytes=git('cat-file','blob',entry[1]),id=identity(bytes);if(id.git_blob!==entry[1]||id.bytes!==size)throw Error('Git body identity mismatch');
  total+=size;if(total>16*1024*1024)throw Error('Delta exceeds 16 MiB');
  const body=new TextDecoder('utf-8',{fatal:true}).decode(bytes);
  documents.push({url,title:body.match(/^#\s+(.+)$/m)?.[1]??path,body,...id,bindings:[{role:'git_tree_delta_source',label:'Source body at exact later tree; authored status/review must be read, no claim acceptance inferred'}]});
 }catch(e){unavailable.push({path,url,reason:e.message});}
}
const supplement={schema:1,date_utc:new Date().toISOString(),base_corpus_sha256:identity(baseBytes).sha256,documents,
 source_delta:{repository:'Sodelin/Research-Commons',from:options['--from'],to:options['--to'],roots:['research','handoffs','communications'],changed_paths:parts.length/2,excluded,unavailable,
  limitation:'Complete bounded local tree delta for these roots, selected Markdown bodies only. No claim-card/status edits, full history, acceptance, JSON/status/comment or Lean-body indexing.'}};
validateCorpus(supplement);
await writeFile(options['--output'],JSON.stringify(supplement)+'\n',{flag:'wx'});
console.log(JSON.stringify({indexed:documents.length,unavailable:unavailable.length,excluded:excluded.length,source_delta:supplement.source_delta}));
