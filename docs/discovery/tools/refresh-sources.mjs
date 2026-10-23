// Only deliberately public, immutable first-party Markdown evidence is projected.
// Network responses stay in RAM until the complete bounded snapshot is assembled.
import {readFile,writeFile,rename} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {artifactReferences,recoveredReferences} from '../dist/source-search.mjs';
import {validate} from '../dist/model.mjs';
const root=new URL('../dist/',import.meta.url);
const data=validate(JSON.parse(await readFile(new URL('claims.json',root))));
const registry=JSON.parse(await readFile(new URL('source.json',root)));
const refs=artifactReferences(data.claims),documents=[],unavailable=[],catalogues=[];
const canonicalReferenceCount=refs.length;
async function publicBytes(url){
 const raw=url.replace('https://github.com/','https://raw.githubusercontent.com/').replace('/blob/','/');
 const r=await fetch(raw,{redirect:'error',signal:AbortSignal.timeout(20000)});
 if(!r.ok)throw Error('HTTP '+r.status);
 const chunks=[];let size=0;
 for await(const chunk of r.body){size+=chunk.length;if(size>512*1024)throw Error('Artifact exceeds 512 KiB bound');chunks.push(chunk);}
 return Buffer.concat(chunks);
}
function identity(bytes){return {bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex'),git_blob:createHash('sha1').update(Buffer.from('blob '+bytes.length+'\0')).update(bytes).digest('hex')};}
for(const reference of data.recovered_source_catalogues??[]){
 // Existing G3 owner's published contract, not a guessed schema for other producers.
 if(reference.programme!=='original.G3'||reference.path!=='research/2026-10-23-g3-proof-recovery/RESULT-CATALOGUE.json')throw Error('Unsupported recovery catalogue: add its owned contract before importing');
 const base='https://github.com/'+registry.repository+'/blob/'+registry.commit+'/'+reference.path.slice(0,reference.path.lastIndexOf('/')+1);
 const url=base+'RESULT-CATALOGUE.json',manifestURL=base+'SOURCE-MANIFEST.json';
 const [bytes,manifestBytes]=await Promise.all([publicBytes(url),publicBytes(manifestURL)]);
 const catalogue=JSON.parse(bytes),manifest=JSON.parse(manifestBytes);
 const recovered=recoveredReferences(catalogue,manifest,base);
 if(recovered.length!==reference.mathematical_notes)throw Error('Recovery manifest count does not match canonical declaration');
 catalogues.push({url,...identity(bytes),catalogue,manifest:{url:manifestURL,...identity(manifestBytes)},mathematical_notes:recovered.length,programme:reference.programme});
 for(const ref of recovered){const existing=refs.find(r=>r.url===ref.url);if(existing)existing.bindings.push(...ref.bindings);else refs.push(ref);}
 if(reference.readme!==reference.path.replace('RESULT-CATALOGUE.json','README.md'))throw Error('Unsupported catalogue context path');
 refs.push({url:base+'README.md',bindings:[{role:'recovered_catalogue_context',catalogue_key:null,label:reference.programme+' source recovery, disposition and later corrections'}]});
}
let cursor=0,total=0;
await Promise.all(Array.from({length:4},async()=>{
  while(cursor<refs.length){
    const ref=refs[cursor++];
    try{
      const bytes=await publicBytes(ref.url),id=identity(bytes);
      total+=id.bytes;if(total>16*1024*1024)throw Error('Corpus exceeds 16 MiB bound');
      if(ref.expected_sha256&&(id.sha256!==ref.expected_sha256||id.git_blob!==ref.expected_git_blob||id.bytes!==ref.expected_bytes))throw Error('Public recovered-source identity mismatch');
      const body=new TextDecoder('utf-8',{fatal:true}).decode(bytes);
      documents.push({...ref,title:body.match(/^#\s+(.+)$/m)?.[1]??decodeURIComponent(ref.url.split('/').at(-1)),body,...id});
    }catch(e){unavailable.push({url:ref.url,reason:e.message});}
  }
}));
documents.sort((a,b)=>a.url.localeCompare(b.url));unavailable.sort((a,b)=>a.url.localeCompare(b.url));
if(total>16*1024*1024)throw Error('Corpus bound exceeded; previous snapshot preserved');
const corpus={schema:1,registry_source:registry,catalogues,coverage:{selected_references:refs.length,canonical_artifact_references:canonicalReferenceCount,recovered_mathematical_notes:catalogues.reduce((n,c)=>n+c.mathematical_notes,0),indexed:documents.length,unavailable,
  limitation:'Only immutable first-party Markdown evidence linked by this registry snapshot. Not the full archive. Source hits do not establish acceptance or current status.'},documents};
const target=new URL('source-corpus.json',root),pending=new URL('source-corpus.json.pending',root);
await writeFile(pending,JSON.stringify(corpus));await rename(pending,target);
console.log(JSON.stringify({indexed:documents.length,unavailable:unavailable.length,bytes:total}));
