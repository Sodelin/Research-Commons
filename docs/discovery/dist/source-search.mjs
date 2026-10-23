import MiniSearch from './vendor/minisearch.mjs';
import {safeLink} from './model.mjs';
// Evidence retrieval is a projection, never a scientific status register.
export function artifactReferences(claims){
  const refs=new Map();
  for(const c of claims)for(const a of c.accepted_artifacts){
    const url=safeLink(a.url);
    if(!url||!/^https:\/\/github\.com\/Sodelin\/[^/]+\/blob\/[a-f0-9]{40}\/.+\.md$/i.test(url))continue;
    if(!refs.has(url))refs.set(url,{url,bindings:[]});
    refs.get(url).bindings.push({claim_id:c.id,role:a.role,label:a.label});
  }
  return [...refs.values()].sort((a,b)=>a.url.localeCompare(b.url));
}
export function readingReferences(joins,claims){
  const ids=new Set(claims.map(c=>c.id)),refs=new Map();
  for(const join of joins){
    if(!Array.isArray(join.claim_ids)||join.claim_ids.some(id=>!ids.has(id)))throw Error('Unknown reading-join claim identity');
    for(const link of join.links){
      const url=safeLink(link.url);if(!url)throw Error('Unsafe reading-join source link');
      if(!/^https:\/\/github\.com\/Sodelin\/[^/]+\/blob\/[a-f0-9]{40}\/.+\.md$/i.test(url))continue;
      if(!refs.has(url))refs.set(url,{url,bindings:[]});
      refs.get(url).bindings.push(...join.claim_ids.map(claim_id=>({claim_id,role:'owned_reading_join_source',label:link.label,source_join_kind:join.kind})));
    }
  }
  return [...refs.values()].sort((a,b)=>a.url.localeCompare(b.url));
}
const indexes=new WeakMap();
export function recoveredReferences(catalogue,manifest,baseURL){
  if(!safeLink(baseURL)||!/^https:\/\/github\.com\/Sodelin\/[^/]+\/blob\/[a-f0-9]{40}\/.+\/$/.test(baseURL))throw Error('Recovery catalogue needs an immutable public source root');
  if(!Array.isArray(catalogue.entries)||!Array.isArray(manifest.files))throw Error('Unsupported recovery source contract');
  return manifest.files.filter(f=>f.kind==='authored_mathematical_note').map(f=>{
    if(!/^[A-Za-z0-9_.-]+\.md$/.test(f.name)||f.name.startsWith('.'))throw Error('Unsafe recovered source name');
    if(!/^[a-f0-9]{64}$/.test(f.public_sha256)||!/^[a-f0-9]{40}$/.test(f.public_git_blob_sha)||!Number.isSafeInteger(f.public_bytes))throw Error('Missing public source identity');
    const records=catalogue.entries.filter(e=>e.file===f.name||(e.companions??[]).includes(f.name));
    return {url:baseURL+f.name,expected_sha256:f.public_sha256,expected_git_blob:f.public_git_blob_sha,expected_bytes:f.public_bytes,
      bindings:records.length?records.map(record=>({catalogue_key:record.key,role:'recovered_component_source',label:record.title,catalogue_record:record})):
        [{role:'recovered_manifest_note',label:f.title,catalogue_key:null}]};
  });
}
export function searchSources(corpus,query,claimIds=null){
  if(!indexes.has(corpus)){
    const index=new MiniSearch({idField:'url',fields:['title','body','claims']});
    index.addAll(corpus.documents.map(d=>({...d,claims:d.bindings.map(b=>[b.claim_id,b.catalogue_key,b.label,b.catalogue_record?.scope].filter(Boolean).join(' ')).join(' ')})));
    indexes.set(corpus,index);
  }
  const byURL=new Map(corpus.documents.map(d=>[d.url,d]));
  let hits=String(query).trim()?indexes.get(corpus).search(query,{combineWith:'AND',prefix:true,boost:{title:4,claims:3}}).map(h=>byURL.get(h.id)):corpus.documents;
  const exact=corpus.documents.filter(d=>d.bindings.some(b=>b.catalogue_key===String(query).trim()));
  if(exact.length){const urls=new Set(exact.map(d=>d.url));hits=[...exact,...hits.filter(d=>!urls.has(d.url))];}
  return hits.filter(d=>!claimIds||d.bindings.some(b=>claimIds.has(b.claim_id)));
}
export function sourceExcerpt(body,query,max=320){
  const term=String(query).trim().split(/\s+/).find(t=>body.toLowerCase().includes(t.toLowerCase()));
  const pos=term?body.toLowerCase().indexOf(term.toLowerCase()):0,start=Math.max(0,pos-90);
  return (start?'…':'')+body.slice(start,start+max)+(body.length>start+max?'…':'');
}
const archiveIndexes=new WeakMap();
export function searchArchive(catalog,query){
  if(!archiveIndexes.has(catalog)){
    const index=new MiniSearch({idField:'path',fields:['title','path','group']});
    index.addAll(catalog.documents);archiveIndexes.set(catalog,index);
  }
  if(!String(query).trim())return catalog.documents;
  const byPath=new Map(catalog.documents.map(d=>[d.path,d]));
  return archiveIndexes.get(catalog).search(query,{combineWith:'AND',prefix:true,boost:{title:2,path:1}}).map(h=>byPath.get(h.id));
}
