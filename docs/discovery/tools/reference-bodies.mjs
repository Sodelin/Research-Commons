import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';

// Exact public first-party input pins reviewed for the canonical reference gap.
// This is a source intake boundary, not a list of accepted scientific results.
export const REFERENCED_PUBLIC_INPUTS = new Map([
 ['Sodelin/Work-on-Samuel-Alexander-Research-','e2502c82ab9a77c00543932f775a71e5374221f7'],
 ['Sodelin/Formalizing-Soft-Sciences','8e665d2a9f6168e6448b2ca49fccbec87d57d3ad'],
 ['Sodelin/Cross-Scale-Causal-Formalization','28bdb75b8d057332e1bb32020d02e5eaea4c0517'],
 ['Sodelin/Collatz-Conjecture-Work','026aa4ad4be6453a005ab950b160a9f2204c5271'],
]);
export async function loadReferenceBodies(path){
 const corpus=JSON.parse(await readFile(path));
 if(corpus.schema!==1||corpus.view!=='exact_canonical_reference_bodies'||!Array.isArray(corpus.documents)||!Array.isArray(corpus.unavailable))throw Error('Invalid reference body supplement');
 const seen=new Set();
 for(const doc of corpus.documents){
  if(!/^[a-f0-9]{40}$/.test(doc.commit)||!Array.isArray(doc.source_paths)||doc.source_paths.length!==1||typeof doc.body!=='string')throw Error('Invalid reference body identity');
  const p=doc.source_paths[0];
  if(p.startsWith('/')||p.split('/').some(x=>!x||x==='.'||x==='..')||p.includes('\\'))throw Error('Invalid reference source path');
  if(doc.repository!=='Sodelin/Research-Commons'&&REFERENCED_PUBLIC_INPUTS.get(doc.repository)!==doc.commit)throw Error('Unreviewed public repository/pin; retain link-only');
  const expected=`https://github.com/${doc.repository}/blob/${doc.commit}/${p}`;
  if(doc.url!==expected||seen.has(doc.url))throw Error('Duplicate or inconsistent reference URL');seen.add(doc.url);
  const b=Buffer.from(doc.body);
  if(b.length>16*1024*1024||b.includes(0)||b.length!==doc.bytes||createHash('sha256').update(b).digest('hex')!==doc.sha256||createHash('sha1').update(`blob ${b.length}\0`).update(b).digest('hex')!==doc.git_blob)throw Error('Reference body hash/size mismatch');
  if(!Array.isArray(doc.bindings)||doc.bindings.some(b=>b.role!=='canonical_reference_only'||typeof b.claim_id!=='string'))throw Error('Invalid reference-only bindings');
  if(typeof doc.license_status!=='string'||!doc.license_status||doc.evidence_role!=='Source body only; no scientific status, review, execution or license acceptance inferred.')throw Error('Reference body scope/ license label required');
 }
 return corpus;
}
