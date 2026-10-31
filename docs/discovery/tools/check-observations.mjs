import {readFile} from 'node:fs/promises';
import {identity} from './source-cache.mjs';
export async function readObservations(paths,pkg){
 if(paths.length>20)throw Error('At most 20 explicit observations');
 const records=[];
 for(const path of paths){
  const bytes=await readFile(path);if(bytes.length>5*1024*1024)throw Error('Observation exceeds 5 MiB');
  const r=JSON.parse(bytes);
  if(r.schema!==1||r.record_kind!=='bounded_declaration_check_observation'||!pkg.cards.has(r.claim_id)||!['UNKNOWN','NOT_EXECUTED','CHECKED_SCOPED_DECLARATIONS'].includes(r.outcome))throw Error('Unsupported observation');
  const current=JSON.stringify(r.package_source?.files)===JSON.stringify(pkg.identity.files);
  records.push({claim_id:r.claim_id,outcome:r.outcome,executed:r.executed,blockers:r.blockers??[],scope:r.scope,observed_utc:r.observed_utc,
   current_package_metadata_files_match:current,
   identity_match_scope:'Only the package metadata files explicitly listed in package_source.files are compared. This does not establish correspondence of checker/runtime/Cargo/toolchain bytes or the complete execution environment.',
   source:{path,...identity(bytes)},
   trust:'Explicit local observation bytes, not authenticated proof acceptance. Read the actual checker/owned evidence before reuse.'});
 }
 return records;
}
