#!/usr/bin/env node
// Read-only navigation joins. Scientific statuses come only from claims.json.
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';

const args=process.argv.slice(2);
let mode=null,id=null;
for(let i=0;i<args.length;i++){
  const a=args[i];
  if(a==='--programmes'||a==='--outputs'){
    if(mode)throw Error('Choose exactly one of --programmes or --outputs.');
    mode=a.slice(2);
  }else if(a==='--id'){
    if(id!==null||!args[i+1]||args[i+1].startsWith('--'))throw Error('--id requires one ID.');
    id=args[++i];
  }else throw Error('Use --programmes or --outputs, optionally --id ID.');
}
if(!mode)throw Error('Choose --programmes or --outputs.');
const sources={};
async function read(name){
  const bytes=await readFile(new URL('../../'+name,import.meta.url));
  sources['docs/'+name]={sha256:createHash('sha256').update(bytes).digest('hex')};
  return JSON.parse(bytes.toString('utf8'));
}
const registry=await read('claims.json');
const programmes=await read('programmes.json');
const pipeline=await read('dissemination.json');
if(programmes.schema_version!==1||pipeline.schema_version!==1)throw Error('Unsupported navigation schema.');
function unique(items,label){
  if(!Array.isArray(items))throw Error('Missing '+label+' array.');
  const map=new Map();
  for(const item of items){
    if(typeof item.id!=='string'||!item.id||map.has(item.id))throw Error('Invalid or duplicate '+label+' ID.');
    map.set(item.id,item);
  }
  return map;
}
const claimMap=unique(registry.claims,'claim');
const programmeMap=unique(programmes.programmes,'programme');
unique(pipeline.outputs,'output');
for(const item of [...programmes.programmes,...pipeline.outputs]){
  if(!Array.isArray(item.claim_ids)||item.claim_ids.some(id=>!claimMap.has(id)))throw Error('Unresolved canonical claim binding: '+item.id);
}
for(const item of pipeline.outputs){
  if(!Array.isArray(item.programme_ids)||item.programme_ids.some(id=>!programmeMap.has(id)))throw Error('Unresolved programme binding: '+item.id);
}
const all=mode==='programmes'?programmes.programmes:pipeline.outputs;
const selected=id===null?all:all.filter(item=>item.id===id);
if(id!==null&&!selected.length)throw Error('Unknown '+mode+' ID: '+id);
console.log(JSON.stringify({view:mode,source_scope:'Current local checkout only; not remote freshness or execution status.',sources,
  total:selected.length,results:selected.map(item=>({...item,canonical_claims:item.claim_ids.map(id=>claimMap.get(id))}))},null,2));
