import MiniSearch from './vendor/minisearch.mjs';
import {safeLink} from './model.mjs';
// Evidence retrieval is a projection, never a scientific status register.
export function artifactReferences(claims){
  const refs=new Map();
  for(const c of claims)for(const a of c.accepted_artifacts){
    if(!safeLink(a.url)||!/^https:\/\/github\.com\/Sodelin\/[^/]+\/blob\/[a-f0-9]{40}\/.+\.md$/i.test(a.url))continue;
    if(!refs.has(a.url))refs.set(a.url,{url:a.url,bindings:[]});
    refs.get(a.url).bindings.push({claim_id:c.id,role:a.role,label:a.label});
  }
  return [...refs.values()].sort((a,b)=>a.url.localeCompare(b.url));
}
const indexes=new WeakMap();
export function searchSources(corpus,query,claimIds=null){
  if(!indexes.has(corpus)){
    const index=new MiniSearch({idField:'url',fields:['title','body','claims']});
    index.addAll(corpus.documents.map(d=>({...d,claims:d.bindings.map(b=>b.claim_id+' '+b.label).join(' ')})));
    indexes.set(corpus,index);
  }
  const byURL=new Map(corpus.documents.map(d=>[d.url,d]));
  const hits=String(query).trim()?indexes.get(corpus).search(query,{combineWith:'AND',prefix:true,boost:{title:4,claims:3}}).map(h=>byURL.get(h.id)):corpus.documents;
  return hits.filter(d=>!claimIds||d.bindings.some(b=>claimIds.has(b.claim_id)));
}
export function sourceExcerpt(body,query,max=320){
  const term=String(query).trim().split(/\s+/).find(t=>body.toLowerCase().includes(t.toLowerCase()));
  const pos=term?body.toLowerCase().indexOf(term.toLowerCase()):0,start=Math.max(0,pos-90);
  return (start?'…':'')+body.slice(start,start+max)+(body.length>start+max?'…':'');
}
