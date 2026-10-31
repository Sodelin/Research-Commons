import {readFile} from 'node:fs/promises';
import {resolve,dirname,basename} from 'node:path';
import {gunzipSync} from 'node:zlib';
import {createHash} from 'node:crypto';
import {searchSources,sourceExcerpt,artifactReferences,sourceQueryCandidates,sourceExactness} from '../dist/source-search.mjs';
import {loadReferenceBodies} from './reference-bodies.mjs';
const sha=b=>createHash('sha256').update(b).digest('hex');
export async function queryResearchResults(manifestPath,query,{offset=0,limit=25,pathPrefix=null,referenceBodies=null}={}){
 const root=dirname(resolve(manifestPath)),manifest=JSON.parse(await readFile(manifestPath));
 if(manifest.schema!==1||manifest.repository!=='Sodelin/Research-Commons'||!/^[a-f0-9]{40}$/.test(manifest.commit)||!Array.isArray(manifest.shards)||!Array.isArray(manifest.inventory))throw Error('Invalid published research inventory');
 const register=JSON.parse(await readFile(new URL('../dist/claims.json',import.meta.url)));const refs=artifactReferences(register.claims),claims=new Map();
 for(const ref of refs){const match=ref.url.match(/^https:\/\/github.com\/Sodelin\/Research-Commons\/blob\/[a-f0-9]{40}\/(.+)$/);if(!match)continue;const list=claims.get(match[1])??new Set();for(const b of ref.bindings)if(b.claim_id)list.add(b.claim_id);claims.set(match[1],list);}
 const inventory=new Map(manifest.inventory.map(r=>[r.path,r]));if(inventory.size!==manifest.inventory.length)throw Error('Duplicate inventory path');const seen=new Set();
 let total=0;const buckets=Array.from({length:6},()=>[]);
 const relevant=manifest.inventory.filter(r=>r.coverage==='full_text'&&(!pathPrefix||r.path.startsWith(pathPrefix)));const relevantShards=new Set(relevant.map(r=>r.shard));
 for(const entry of manifest.shards){
  if(!relevantShards.has(entry.path))continue;
  if(entry.path!==basename(entry.path)||!/^bodies-\d{4}\.json\.gz$/.test(entry.path))throw Error('Invalid body shard path');
  const bytes=await readFile(resolve(root,entry.path));if(sha(bytes)!==entry.sha256)throw Error('Body shard hash mismatch');
  const raw=gunzipSync(bytes,{maxOutputLength:96*1024*1024}),corpus=JSON.parse(raw);if(corpus.schema!==1||corpus.documents.length!==entry.documents)throw Error('Invalid body shard');
  for(const doc of corpus.documents){const bytes=Buffer.from(doc.body);if(sha(bytes)!==doc.sha256||bytes.length!==doc.bytes||createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')!==doc.git_blob||!(manifest.source_commits??[manifest.commit]).some(pin=>doc.url.startsWith(`https://github.com/Sodelin/Research-Commons/blob/${pin}/`)))throw Error('Body identity mismatch');}
  for(const doc of corpus.documents)for(const path of doc.source_paths){if(pathPrefix&&!path.startsWith(pathPrefix))continue;const row=inventory.get(path);if(seen.has(path)||!row||row.coverage!=='full_text'||row.git_blob!==doc.git_blob||row.sha256!==doc.sha256||row.shard!==entry.path)throw Error('Body inventory mismatch');seen.add(path);}
  for(const doc of searchSources({documents:sourceQueryCandidates(corpus.documents.filter(d=>!pathPrefix||d.source_paths.some(p=>p.startsWith(pathPrefix))),query)},query)){
   const priority=sourceExactness(doc,query);if(buckets[priority].length<offset+limit)buckets[priority].push({url:doc.url,title:doc.title,git_blob:doc.git_blob,sha256:doc.sha256,bytes:doc.bytes,source_paths:doc.source_paths,canonical_claim_references:[...new Set(doc.source_paths.flatMap(p=>[...(claims.get(p)??[])]))],evidence_role:'Published source; authored labels and later corrections must be read. No claim status inferred.',excerpt:sourceExcerpt(doc.body,query)});total++;
  }
 }
 if(seen.size!==relevant.length)throw Error('Incomplete body inventory');
 let referenceCoverage=null;
 if(referenceBodies){
  const supplement=await loadReferenceBodies(referenceBodies),exactClaims=new Map(refs.map(r=>[r.url,[...new Set(r.bindings.map(b=>b.claim_id).filter(Boolean))]]));
  // Keep a different source version even when a path or declaration is shared.
  // Skip only bodies already present at the exact immutable URL.
  const indexedUrls=new Set(manifest.inventory.filter(r=>r.coverage==='full_text').map(r=>r.document_url));
  const docs=supplement.documents.filter(d=>!indexedUrls.has(d.url)&&(!pathPrefix||d.source_paths.some(p=>p.startsWith(pathPrefix))));
  for(const doc of searchSources({documents:sourceQueryCandidates(docs,query)},query)){
   const priority=sourceExactness(doc,query);if(buckets[priority].length<offset+limit)buckets[priority].push({url:doc.url,title:doc.title,repository:doc.repository,commit:doc.commit,git_blob:doc.git_blob,sha256:doc.sha256,bytes:doc.bytes,source_paths:doc.source_paths,canonical_claim_references:[...new Set([...(exactClaims.get(doc.url)??[]),...doc.bindings.map(b=>b.claim_id).filter(id=>register.claims.some(c=>c.id===id))])],evidence_role:doc.evidence_role,license_status:doc.license_status,excerpt:sourceExcerpt(doc.body,query)});total++;
  }
  referenceCoverage={documents:supplement.documents.length,additional_documents:docs.length,unavailable:supplement.unavailable,limitation:supplement.limitation};
 }
 const results=buckets.reverse().flat().slice(offset,offset+limit);
 return {view:'published_research_full_text',path_prefix:pathPrefix,repository:manifest.repository,commit:manifest.commit,coverage:manifest.coverage,reference_bodies:referenceCoverage,limitation:manifest.limitation,total,offset,limit,next_offset:offset+limit<total?offset+limit:null,results};
}
