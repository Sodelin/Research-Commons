import MiniSearch from './vendor/minisearch.mjs';
// Projection of the existing claim register. Stored scientific statuses stay unchanged.
export const STATUS = {
  established: 'Established at stated scope', counterexample: 'Counterexamples & limits',
  open: 'Open mathematics', formal: 'Formal or implementation gaps',
  proposal: 'Proposals & conditional results', applied: 'Software & empirical results', other:'Unmapped source disposition'
};
export const ORIGIN = { published_open_problem: 'Published questions', project_posed: 'Project questions', classical_prior: 'Classical suppliers' };
export const RELATION = {proved_adapter:'Proved adapter at stated scope', reused_theorem:'Reuses this theorem', same_principle:'Related principle — no theorem implication', candidate_connection:'Candidate connection — not established'};
export function bucket(c) {
  const s=c.mathematical_status;
  if (/counterexample|refut|nonseparation/.test(s)) return 'counterexample';
  if (s==='open') return 'open';
  if (/open_formal/.test(s)) return 'formal';
  if (/proposal|conditional/.test(s)) return 'proposal';
  if (/software|empirical|computational/.test(s)) return 'applied';
  if (s==='proved_at_stated_scope') return 'established';
  return 'other';
}
export const topic = c => c.programme.split(' · ')[0];
export const words = text => String(text ?? '').normalize('NFKD').replace(/[\u0300-\u036f]/g,'').toLocaleLowerCase();
export function validate(data) {
  if (!data || !Array.isArray(data.claims) || !data.claims.length) throw Error('The canonical register contains no claim cards.');
  const ids=new Set();
  for(const c of data.claims) {
    if (!c.id || ids.has(c.id)) throw Error('Missing or duplicate claim identity.');
    ids.add(c.id);
    if (!c.plain_language || !c.evidence || !c.origin || !Array.isArray(c.dependencies) || !Array.isArray(c.accepted_artifacts)) throw Error(`Incomplete canonical card ${c.id}.`);
    if(c.origin.source_url&&!safeLink(c.origin.source_url))throw Error(`Unsafe origin source on ${c.id}.`);
    if(c.accepted_artifacts.some(a=>!safeLink(a.url)))throw Error(`Unsafe evidence source on ${c.id}.`);
    for(const k of ['question','what_we_learned','what_it_lets_someone_do','what_cannot_conclude'])
      if(typeof c.plain_language[k]!=='string') throw Error(`Missing ${k} on ${c.id}.`);
  }
  for(const c of data.claims) for(const r of c.dependencies)
    if(!ids.has(r.claim_id) || !RELATION[r.relation_type]) throw Error(`Unresolved relationship on ${c.id}.`);
  return data;
}
const indexes=new WeakMap();
const STOP=new Set(['a','an','the','is','are','was','were','can','could','do','does','did','we','our','what','which','how','of','for','to','and','in','on','with','this','that','it']);
function indexFor(claims) {
  if(indexes.has(claims)) return indexes.get(claims);
  const index=new MiniSearch({idField:'id', fields:['id','title','question','answer','scope','context','downstream'],
    processTerm:t=>{const w=words(t);return STOP.has(w)?null:w;}});
  index.addAll(claims.map(c=>({id:c.id,title:c.title,question:c.plain_language.question,
    answer:c.plain_language.what_we_learned,scope:c.exact_statement_and_scope,
    downstream:c.separate_downstream_or_validation_work??'',
    context:[c.programme,c.plain_language.what_it_lets_someone_do,c.plain_language.what_cannot_conclude,
      c.prior_work,c.our_contribution,c.remaining_obligation,c.completion?.display??'',JSON.stringify(c.aliases),
      literatureSources(c).map(a=>a.label+' '+a.url).join(' ')].join(' ')})));
  indexes.set(claims,index); return index;
}
export function search(claims, f={}) {
  const query=String(f.q??'').trim();
  let ordered=claims;
  if(query){
    const exact=claims.find(c=>words(c.id)===words(query)||words(c.canonical_key)===words(query));
    const hits=indexFor(claims).search(query,{combineWith:'AND',prefix:true,
      fuzzy:t=>t.length>4?0.2:false,boost:{id:12,title:7,question:7,answer:3,scope:2}});
    const byId=new Map(claims.map(c=>[c.id,c]));
    ordered=hits.map(hit=>byId.get(hit.id)).filter(Boolean);
    if(exact) ordered=[exact,...ordered.filter(c=>c.id!==exact.id)];
  }
  return ordered.filter(c=> {
    if (f.topic && topic(c)!==f.topic) return false;
    if (f.status && bucket(c)!==f.status) return false;
    if (f.origin && c.origin.category!==f.origin) return false;
    if (f.programme && c.programme!==f.programme) return false;
    if (f.kind && c.claim_kind!==f.kind) return false;
    if (f.review && (c.completion?.independent_review??'not_recorded')!==f.review) return false;
    if (f.formal_status && c.evidence.formal.status!==f.formal_status) return false;
    if (f.novelty && c.novelty_status!==f.novelty) return false;
    if (f.formal==='checked' && !/^kernel_checked|^accepted_selected_formal_chain/.test(c.evidence.formal.status)) return false;
    return true;
  });
}
export function sortClaims(claims,sort,ranking){
  if(!sort||sort==='relevance')return claims;
  if(sort!=='subjective_reuse')throw Error('Unknown claim ordering');
  const ranks=new Map((ranking?.entries??[]).map(e=>[e.claim_id,e.rank]));
  return [...claims].sort((a,b)=>(ranks.get(a.id)??Infinity)-(ranks.get(b.id)??Infinity));
}
export function neighbors(claims, id) {
  const c=claims.find(x=>x.id===id);
  if (!c) return {outgoing:[],incoming:[]};
  return {outgoing:c.dependencies.map(r=>({...r,claim:claims.find(x=>x.id===r.claim_id)})),
    incoming:claims.flatMap(other=>other.dependencies.filter(r=>r.claim_id===id).map(r=>({...r,claim:other})))};
}
function stableSource(value){
  if(Array.isArray(value))return value.map(stableSource);
  if(value&&typeof value==='object')return Object.fromEntries(Object.keys(value).sort().map(k=>[k,stableSource(value[k])]));
  return value;
}
export function compareRegisters(previous,current){
  validate(previous);validate(current);
  const old=new Map(previous.claims.map(c=>[c.id,c])),now=new Map(current.claims.map(c=>[c.id,c]));
  const summary=c=>c?{question:c.plain_language.question,exact_scope:c.exact_statement_and_scope,
    mathematical_status:c.mathematical_status,completion:c.completion??null,formal_status:c.evidence.formal.status}:null;
  const records=[];
  for(const c of current.claims){
    const before=old.get(c.id);
    const fields=before?[...new Set([...Object.keys(before),...Object.keys(c)])].sort().filter(k=>JSON.stringify(stableSource(before[k]))!==JSON.stringify(stableSource(c[k]))):[];
    if(!before||fields.length)records.push({claim_id:c.id,change_type:before?'changed':'added',changed_fields:fields,previous:summary(before),current:summary(c)});
  }
  for(const c of previous.claims)if(!now.has(c.id))records.push({claim_id:c.id,change_type:'removed',changed_fields:[],previous:summary(c),current:null});
  return {added:records.filter(r=>r.change_type==='added').length,changed:records.filter(r=>r.change_type==='changed').length,
    removed:records.filter(r=>r.change_type==='removed').length,unchanged:current.claims.length-records.filter(r=>r.current).length,
    limitation:'Indexed-card changes between two exact snapshots, not new discoveries, proof acceptance, deletion of historical evidence or complete intervening history.',records};
}
export function literatureSources(c) {
  const candidates=[];
  const originURL=safeLink(c.origin?.source_url);
  if(originURL)candidates.push({label:'Original published question',url:originURL,role:'origin_source'});
  for(const a of c.accepted_artifacts??[]){const url=safeLink(a.url);if(['prior_work','historical_problem_statement'].includes(a.role)&&url)candidates.push({...a,url});}
  const seen=new Set();return candidates.filter(a=>{if(seen.has(a.url))return false;seen.add(a.url);return true;});
}
export function reusePacket(c, meta, joins=[],ranking=null,rankingSource=null,assessments=[]) {
  return {claim_id:c.id, question:c.plain_language.question, mathematical_status:c.mathematical_status,
    exact_scope:c.exact_statement_and_scope, completion_evidence:c.accepted_artifacts,
    formal_status:c.evidence.formal, execution_status:c.evidence.execution,
    completion:c.completion??null, genuine_remaining_obligation:c.remaining_obligation,
    separate_downstream_or_validation_work:c.separate_downstream_or_validation_work??null, dependencies:c.dependencies,
    provenance:{origin:c.origin,prior_work:c.prior_work,literature_sources:literatureSources(c),contribution:c.our_contribution,novelty:c.novelty_status},
    registry_source:meta, reader_evidence_joins:joins.filter(j=>j.claim_ids.includes(c.id)),
    subjective_reuse:ranking?{entry:ranking.entries.find(e=>e.claim_id===c.id)??null,author:ranking.author,dated_utc:ranking.dated_utc,
      purpose:ranking.purpose,source:rankingSource,later_assessments:validateAssessments(assessments),unranked_means:'No rank supplied in this dated overlay, not low importance or incomplete mathematics.'}:null,
    before_new_work:['Read the actual accepted sources and later corrections, not only this summary.',
      'Match the proposed statement, quantifiers, observations and assumptions to this exact scope.',
      'Reuse completed mathematics. Missing formalization does not reopen a hand proof.',
      'Name the new unresolved implication or added value: independent check, sharper scope, new adapter or failed-route exclusion.',
      'Preserve existing owners and holds. Discovery is not permission to run a job.']};
}
const CREDENTIAL_KEY=/^(?:token|access_token|auth|authorization|api_key|apikey|secret|password|signature|sig|credential|session|x-amz-signature|x-amz-credential|x-amz-security-token|x-goog-signature|x-goog-credential|googleaccessid)$/i;
function credentialParameters(text){
  return [...new URLSearchParams(text).keys()].some(key=>CREDENTIAL_KEY.test(key));
}
function credentialFragment(hash){
  const raw=hash.slice(1),forms=[raw];
  try{const decoded=decodeURIComponent(raw);if(decoded!==raw)forms.push(decoded);}catch{/* Ordinary malformed anchors retain their existing URL behavior. */}
  for(const form of forms){
    // OAuth parameter fragments and hash-router query strings are both links.
    // A plain scientific anchor such as #token is not a parameter assignment.
    if(!/[=?&]/.test(form))continue;
    const parts=[form.replace(/^[!/?]+/,''),...form.split('?').slice(1)];
    if(parts.some(credentialParameters))return true;
  }
  return false;
}
export function validateRanking(ranking){
  if(ranking?.subjective!==true||!Array.isArray(ranking.entries))throw Error('Unsupported subjective source overlay.');
  if(ranking.entries.some(entry=>entry.source_url&&!safeLink(entry.source_url)))throw Error('Unsafe subjective source link.');
  return ranking;
}
export function validateAssessments(notes){
  if(!Array.isArray(notes))throw Error('Unsupported authored assessment sources.');
  for(const n of notes){
    if(n.subjective!==true||!Number.isSafeInteger(n.source_count)||n.source_count<1||!Number.isFinite(Date.parse(n.dated_utc))||
      !['title','author','scope'].every(k=>typeof n[k]==='string'&&n[k])||!safeLink(n.source_url)||
      !/^https:\/\/github\.com\/Sodelin\/[^/]+\/blob\/[a-f0-9]{40}\/.+\.md$/.test(safeLink(n.source_url)))throw Error('Invalid dated subjective assessment source.');
  }
  return notes;
}
export function safeLink(url) {
  try {
    if(typeof url!=='string'||/[\u0000-\u0020]/.test(url))return null;
    const u=new URL(url);
    // Adapted from the recovered Atlas reading-core link boundary: source
    // links never carry credentials. Keep scientific domains extensible.
    if(u.protocol!=='https:'||u.username||u.password||u.port)return null;
    if(credentialParameters(u.search)||credentialFragment(u.hash))return null;
    return u.href;
  }catch{return null;}
}
