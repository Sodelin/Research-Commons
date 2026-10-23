// Only deliberately public, immutable first-party Markdown evidence is projected.
// Network responses stay in RAM until the complete bounded snapshot is assembled.
import {readFile,writeFile,rename} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {artifactReferences} from '../dist/source-search.mjs';
import {validate} from '../dist/model.mjs';
const root=new URL('../dist/',import.meta.url);
const data=validate(JSON.parse(await readFile(new URL('claims.json',root))));
const registry=JSON.parse(await readFile(new URL('source.json',root)));
const refs=artifactReferences(data.claims),documents=[],unavailable=[];
let cursor=0,total=0;
await Promise.all(Array.from({length:4},async()=>{
  while(cursor<refs.length){
    const ref=refs[cursor++];
    try{
      const raw=ref.url.replace('https://github.com/','https://raw.githubusercontent.com/').replace('/blob/','/');
      const r=await fetch(raw,{redirect:'error',signal:AbortSignal.timeout(20000)});
      if(!r.ok)throw Error('HTTP '+r.status);
      const chunks=[];let size=0;
      for await(const chunk of r.body){size+=chunk.length;if(size>512*1024)throw Error('Artifact exceeds 512 KiB bound');chunks.push(chunk);}
      total+=size;if(total>16*1024*1024)throw Error('Corpus exceeds 16 MiB bound');
      const bytes=Buffer.concat(chunks),body=new TextDecoder('utf-8',{fatal:true}).decode(bytes);
      documents.push({...ref,title:body.match(/^#\s+(.+)$/m)?.[1]??decodeURIComponent(ref.url.split('/').at(-1)),body,
        bytes:size,sha256:createHash('sha256').update(bytes).digest('hex'),
        git_blob:createHash('sha1').update(Buffer.from('blob '+size+'\0')).update(bytes).digest('hex')});
    }catch(e){unavailable.push({url:ref.url,reason:e.message});}
  }
}));
documents.sort((a,b)=>a.url.localeCompare(b.url));unavailable.sort((a,b)=>a.url.localeCompare(b.url));
if(total>16*1024*1024)throw Error('Corpus bound exceeded; previous snapshot preserved');
const corpus={schema:1,registry_source:registry,coverage:{selected_references:refs.length,indexed:documents.length,unavailable,
  limitation:'Only immutable first-party Markdown evidence linked by this registry snapshot. Not the full archive. Source hits do not establish acceptance or current status.'},documents};
const target=new URL('source-corpus.json',root),pending=new URL('source-corpus.json.pending',root);
await writeFile(pending,JSON.stringify(corpus));await rename(pending,target);
console.log(JSON.stringify({indexed:documents.length,unavailable:unavailable.length,bytes:total}));
