#!/usr/bin/env node
import {readFile,writeFile} from 'node:fs/promises';
import {mergeSources} from './source-merge.mjs';
const [base,supplement,output,...extra]=process.argv.slice(2);
if(!base||!supplement||!output||extra.length)throw Error('Usage: merge-sources.mjs BASE SUPPLEMENT NEW_OUTPUT');
const result=mergeSources(await readFile(base),JSON.parse(await readFile(supplement)));
await writeFile(output,JSON.stringify(result)+'\n',{flag:'wx'});
console.log(JSON.stringify({indexed:result.documents.length,output,scope:'Offline navigation only; no canonical status or deployment change.'}));
