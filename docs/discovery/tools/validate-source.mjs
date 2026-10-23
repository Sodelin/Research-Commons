#!/usr/bin/env node
// Source-only stdin validator. No temporary files, network, or runtime record writes.
import {validate,validateRanking} from '../dist/model.mjs';
try{
 const chunks=[];let size=0;
 for await(const chunk of process.stdin){size+=chunk.length;if(size>8*1024*1024)throw Error('Source exceeds the selected 8MiB import bound.');chunks.push(chunk);}
 const data=JSON.parse(Buffer.concat(chunks).toString('utf8'));
 if(process.argv[2]==='--ranking'){
  const ranking=validateRanking(data);console.log(JSON.stringify({valid:true,entries:ranking.entries.length,subjective:true}));
 }else{
  if(process.argv.length>2)throw Error('Unsupported validation mode.');
  const source=validate(data);console.log(JSON.stringify({valid:true,claims:source.claims.length,schema:source.schema_version}));
 }
}catch{console.error('Canonical source validation refused; no source snapshot was persisted.');process.exitCode=2;}
