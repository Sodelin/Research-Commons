import {readFile} from 'node:fs/promises';
import {resolve,dirname,basename} from 'node:path';
import {gunzipSync} from 'node:zlib';
import {createHash} from 'node:crypto';
import {searchSources,sourceExcerpt,artifactReferences,sourceQueryCandidates} from '../dist/source-search.mjs';
const sha=b=>createHash('sha256').update(b).digest('hex');
export async function queryResearchResults(manifestPath,query,{offset=0,limit=25}={}){
 const root=dirname(resolve(manifestPath)),manifest=JSON.parse(await readFile(manifestPath));
 if(manifest.schema!==1||manifest.repository!=='Sodelin/Research-Commons'||!/^[a-f0-9]{40}$/.test(manifest.commit)||!Array.isArray(manifest.shards)||!Array.isArray(manifest.inventory))throw Error('Invalid published research inventory');
 const register=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));const refs=artifactReferences(register.claims),claims=new Map();
 for(const ref of refs){const match=ref.url.match(/^https:\/\/github.com\/Sodelin\/Research-Commons\/blob\/[a-f0-9]{40}\/(.+)$/);if(!match)continue;const list=claims.get(match[1])??new Set();for(const b of ref.bindings)if(b.claim_id)list.add(b.claim_id);claims.set(match[1],list);}
 const inventory=new Map(manifest.inventory.map(r=>[r.path,r]));if(inventory.size!==manifest.inventory.length)throw Error('Duplicate inventory path');const seen=new Set();
 let total=0;const results=[];
 for(const entry of manifest.shards){
  if(entry.path!==basename(entry.path)||!/^bodies-\d{4}\.json\.gz$/.test(entry.path))throw Error('Invalid body shard path');
  const bytes=await readFile(resolve(root,entry.path));if(sha(bytes)!==entry.sha256)throw Error('Body shard hash mismatch');
  const raw=gunzipSync(bytes,{maxOutputLength:96*1024*1024}),corpus=JSON.parse(raw);if(corpus.schema!==1||corpus.documents.length!==entry.documents)throw Error('Invalid body shard');
  for(const doc of corpus.documents){const bytes=Buffer.from(doc.body);if(sha(bytes)!==doc.sha256||bytes.length!==doc.bytes||createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')!==doc.git_blob||!doc.url.startsWith(`https://github.com/Sodelin/Research-Commons/blob/${manifest.commit}/`))throw Error('Body identity mismatch');}
  for(const doc of corpus.documents)for(const path of doc.source_paths){const row=inventory.get(path);if(seen.has(path)||!row||row.coverage!=='full_text'||row.git_blob!==doc.git_blob||row.sha256!==doc.sha256||row.shard!==entry.path)throw Error('Body inventory mismatch');seen.add(path);}
  for(const doc of searchSources({documents:sourceQueryCandidates(corpus.documents,query)},query)){
   if(total>=offset&&results.length<limit)results.push({url:doc.url,title:doc.title,git_blob:doc.git_blob,sha256:doc.sha256,bytes:doc.bytes,source_paths:doc.source_paths,canonical_claim_references:[...new Set(doc.source_paths.flatMap(p=>[...(claims.get(p)??[])]))],evidence_role:'Published source; authored labels and later corrections must be read. No claim status inferred.',excerpt:sourceExcerpt(doc.body,query)});total++;
  }
 }
 if(seen.size!==manifest.coverage.full_text_paths||seen.size!==manifest.inventory.filter(r=>r.coverage==='full_text').length)throw Error('Incomplete body inventory');
 return {view:'published_research_full_text',repository:manifest.repository,commit:manifest.commit,coverage:manifest.coverage,limitation:manifest.limitation,total,offset,limit,next_offset:offset+limit<total?offset+limit:null,results};
}
