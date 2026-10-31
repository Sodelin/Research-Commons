// Offline immutable-source ingestion. Authorship/bindings remain producer data.
import {cachedBody,identity} from './source-cache.mjs';
import {safeLink} from '../dist/model.mjs';
export function validateCorpus(corpus){
 if(corpus.schema!==1||!Array.isArray(corpus.documents))throw Error('Unsupported source corpus');
 let total=0;const seen=new Set();
 for(const d of corpus.documents){
  if(!safeLink(d.url)||!/^https:\/\/github\.com\/Sodelin\/[^/]+\/blob\/[0-9a-f]{40}\/.+\.md$/.test(d.url))throw Error('Source needs immutable public Markdown URL');
  const bytes=cachedBody(d);if(!bytes)throw Error('Source body identity mismatch');
  if(seen.has(d.url))throw Error('Duplicate source URL');seen.add(d.url);total+=bytes.length;
  if(!Array.isArray(d.bindings))throw Error('Missing source bindings');
 }
 if(total>16*1024*1024)throw Error('Source corpus exceeds 16 MiB');
 return corpus;
}
export function mergeSources(baseBytes,supplement){
 if(supplement.schema!==1||identity(baseBytes).sha256!==supplement.base_corpus_sha256)throw Error('Wrong supplement base');
 const base=validateCorpus(JSON.parse(baseBytes));validateCorpus(supplement);
 const merged={...base,documents:[...base.documents,...supplement.documents]};validateCorpus(merged);
 merged.coverage={...base.coverage,indexed:merged.documents.length,selected_references:merged.documents.length,
  supplements:[...(base.coverage.supplements??[]),{date_utc:supplement.date_utc,base_corpus_sha256:supplement.base_corpus_sha256,source_delta:supplement.source_delta,documents:supplement.documents.map(({body,...d})=>d)}],
  limitation:base.coverage.limitation+' Explicit offline navigation supplement; original registry/archive pins and all authored evidence roles retained. No deployment, proof acceptance or complete archive coverage.'};
 return merged;
}
