import {validate,search,topic,bucket,STATUS,ORIGIN,RELATION,neighbors,reusePacket,safeLink,literatureSources,sortClaims} from './model.mjs';
import {searchSources,sourceExcerpt,searchArchive} from './source-search.mjs';
const $=id=>document.getElementById(id);
const state={data:null,meta:null,limit:9,selected:decodeURIComponent(location.hash.slice(1)),mode:'all',joins:[]};
const initial=new URLSearchParams(location.search);
const facetKeys=['topic','status','origin','programme','kind','review','formal_status','novelty'];
const controlKeys=[...facetKeys,'sort'];
state.ranking=null;state.rankingSource=null;
function el(tag,text,cls){const x=document.createElement(tag);if(text!==undefined)x.textContent=text;if(cls)x.className=cls;return x;}
function add(parent,...children){parent.append(...children);return parent;}
function link(label,url){const a=el('a',label);const safe=safeLink(url);if(!safe){a.removeAttribute('href');return a;}a.href=safe;a.target='_blank';a.rel='noopener';return a;}
const pretty=s=>String(s??'').replaceAll('_',' ');
function badge(c){const label=c.completion?.display??STATUS[bucket(c)];return el('span',bucket(c)==='counterexample'&&!/counterexample/i.test(label)?'Counterexample · '+label:label,'badge '+bucket(c));}
function filters(){return Object.fromEntries([['q',$('search').value],...controlKeys.map(k=>[k,$(k).value])]);}
function writeRoute(){const u=new URL(location.href);u.search='';for(const[k,v]of Object.entries(filters()))if(v)u.searchParams.set(k,v);if(state.mode==='reuse'||state.mode==='connections')u.searchParams.set('mode',state.mode);u.hash=state.selected;history.replaceState(null,'',u);}
function toast(message){const target=$('toast');if(!target)return;target.textContent=message;target.style.display='block';setTimeout(()=>target.style.display='none',3000);}
async function copy(text){try{await navigator.clipboard.writeText(text);toast('Copied.');}catch{toast('Clipboard unavailable. Select the text or copy the page address.');}}
function option(select,value,label){const o=el('option',label);o.value=value;select.append(o);}
function initialize(data,meta){
  validate(data);state.data=data;state.meta=meta;
  const old=filters();$('topic').replaceChildren();option($('topic'),'','All topics');
  for(const t of [...new Set(data.claims.map(topic))])option($('topic'),t,t);
  $('topic').value=old.topic;
  for(const[key,value]of Object.entries({programme:c=>c.programme,kind:c=>c.claim_kind,review:c=>c.completion?.independent_review??'not_recorded',formal_status:c=>c.evidence.formal.status,novelty:c=>c.novelty_status})){
    const select=$(key),label=select.options[0].textContent;select.replaceChildren();option(select,'',label);
    for(const v of [...new Set(data.claims.map(value))].sort())option(select,v,pretty(v));select.value=old[key]??'';
  }
  $('credit').textContent=data.contributor;
  $('source-link').href=`https://github.com/Sodelin/Research-Commons/blob/${meta.commit}/docs/claims.json`;
  const cov=$('coverage-body');cov.replaceChildren();
  add(cov,el('p',`${data.claims.length} selected claim cards. ${pretty(data.coverage.status)}.`));
  for(const [key,title]of [['included','Included'],['gaps','Still to be mapped'],['not_claimed','Not claimed']]){
    if(!data.coverage[key]?.length)continue;cov.append(el('strong',title));const list=el('ul');for(const s of data.coverage[key])list.append(el('li',s));cov.append(list);
  }
  $('freshness').textContent=`Canonical register updated ${data.updated_utc}. Source ${meta.commit.slice(0,8)}. Search runs locally in your browser.`;
  render();
}
function showMode(mode){
  state.mode=mode;
  if(mode==='connections'&&!state.selected)state.selected='CB-G7-001';
  document.querySelectorAll('nav button').forEach(b=>b.classList.toggle('active',b.dataset.mode===mode));
  $('reuse-guide').hidden=mode!=='reuse';
}
function render(){
  if(!state.data)return;
  const f=filters(),matches=sortClaims(search(state.data.claims,f),f.sort,state.ranking),results=$('results');results.replaceChildren();
  $('count').textContent=`${matches.length} of ${state.data.claims.length} indexed claims${state.mode==='connections'?' · select a card to follow its typed connections':''}`;
  $('ranking-note').textContent=f.sort==='subjective_reuse'?
    `Subjective reuse judgment by ${state.ranking?.author??'unavailable author'}, dated ${state.ranking?.dated_utc??'unknown'}. It covers ${state.ranking?.source_count??0} source cards; newer/unranked entries follow without a score. This is not an importance, novelty, correctness or review metric.`:
    'Reuse judgments, historical novelty, proof completion and review are separate.';
  if(!matches.length){results.append(el('p','No indexed claim matches these filters. Try fewer terms or reset the filters. This is not evidence that no result exists in the archive.','empty'));results.append(link('Search the wider public source archive ↗','https://github.com/search?type=code&q='+encodeURIComponent('repo:Sodelin/Research-Commons '+f.q)));}
  for(const c of matches.slice(0,state.limit)){
    const article=el('article',undefined,'claim'+(c.id===state.selected?' selected':''));
    article.append(el('p',c.programme,'topic'));
    const h=el('h2');const button=el('button',c.plain_language.question);button.addEventListener('click',()=>select(c.id,true));h.append(button);article.append(h);
    article.append(el('p',c.plain_language.what_we_learned,'answer'),badge(c));
    if(f.sort==='subjective_reuse'){const rank=state.ranking?.entries.find(e=>e.claim_id===c.id);article.append(el('p',rank?`Dot's subjective reuse rank ${rank.rank}: ${rank.reason}`:'Not ranked in this dated subjective overlay.','topic'));}
    const n=neighbors(state.data.claims,c.id);const bottom=el('div',undefined,'claim-bottom');
    add(bottom,el('span',c.id),el('span',`${n.outgoing.length+n.incoming.length} connections`));article.append(bottom);results.append(article);
  }
  if(matches.length>state.limit){const more=el('button',`Show ${Math.min(12,matches.length-state.limit)} more`,'loadmore');more.addEventListener('click',()=>{state.limit+=12;render();});results.append(more);}
  renderSources(results,f);
  renderArchive(results,f.q);
  if(state.selected)renderDetail();writeRoute();
}
let archiveCatalog=null,archiveLoading=false,archiveError=false;
function renderArchive(results,query){
  const panel=el('section',undefined,'archive-results');results.append(panel);panel.append(el('h2','Find older public source documents'));
  if(!archiveCatalog){
    panel.append(el('p','Search document paths across the wider public research tree, including material not yet mapped to claim cards. This lookup uses your search words; mathematical-status, origin and topic filters apply only to the register and its linked evidence.'));
    if(archiveError)panel.append(el('p','The public archive inventory could not load. Use the GitHub archive guide while it is unavailable.','limit'));
    const load=el('button',archiveLoading?'Loading archive inventory…':'Load wider archive search');load.disabled=archiveLoading;
    load.addEventListener('click',async()=>{
      archiveLoading=true;archiveError=false;render();
      try{const r=await fetch('./archive-catalog.json');if(!r.ok)throw Error('Archive unavailable');const catalog=await r.json();if(catalog.schema!==1||!Array.isArray(catalog.documents))throw Error('Unsupported archive');archiveCatalog=catalog;}
      catch{archiveError=true;}finally{archiveLoading=false;render();}
    });panel.append(load,link('Browse the GitHub archive guide ↗','https://github.com/Sodelin/Research-Commons/blob/main/docs/ARCHIVE-SOURCES.md'));return;
  }
  const hits=searchArchive(archiveCatalog,query);
  panel.append(el('p',`${hits.length} matching paths of ${archiveCatalog.documents.length}. Public source ${archiveCatalog.commit.slice(0,8)}. Query words only; claim facets do not filter unmapped archive paths. ${archiveCatalog.coverage.limitations}`));
  if(!hits.length)panel.append(el('p','No matching path in the selected public snapshot. A term may still occur inside an unindexed body or historical source.','limit'));
  for(const d of hits.slice(0,state.limit)){
    const article=el('article',undefined,'archive-hit');article.append(link(d.path+' ↗',d.url),el('p',`Source group: ${d.group}`),el('small',`Git blob ${d.git_blob} · ${d.bytes??'unknown'} bytes · status unverified by this inventory`));panel.append(article);
  }
  if(hits.length>state.limit){const more=el('button','Show more archive paths','loadmore');more.addEventListener('click',()=>{state.limit+=12;render();});panel.append(more);}
}
let sourceCorpus=null,sourceLoading=false,sourceError=false;
function renderSources(results,f){
  const panel=el('section',undefined,'source-results');results.append(panel);
  panel.append(el('h2','Search the linked evidence bodies'));
  if(!sourceCorpus){
    panel.append(el('p','Load the bundled public evidence corpus to search inside source documents. This is separate from the claim summaries.'));
    if(sourceError)panel.append(el('p','Evidence search could not load. Claim search and original source links remain available.'));
    const load=el('button',sourceLoading?'Loading evidence…':'Load evidence search (selected public bodies)');load.disabled=sourceLoading;
    load.addEventListener('click',async()=>{
      sourceLoading=true;sourceError=false;render();
      try{const r=await fetch('./source-corpus.json');if(!r.ok)throw Error('Source corpus unavailable');const corpus=await r.json();if(corpus.schema!==1||!Array.isArray(corpus.documents))throw Error('Unsupported corpus');sourceCorpus=corpus;}
      catch{sourceError=true;}finally{sourceLoading=false;render();}
    });panel.append(load);return;
  }
  const allowed=facetKeys.some(k=>f[k])?new Set(search(state.data.claims,{...f,q:''}).map(c=>c.id)):null;
  const hits=searchSources(sourceCorpus,f.q,allowed);
  panel.append(el('p',`${hits.length} matching documents of ${sourceCorpus.coverage.indexed} indexed; ${sourceCorpus.coverage.unavailable.length} unavailable. Evidence snapshot ${sourceCorpus.registry_source.commit.slice(0,8)}. ${sourceCorpus.coverage.limitation}`));
  if(sourceCorpus.catalogues?.length)panel.append(el('p','Recovered component records retain their own literal scope, authorship, review, formal status and gap. They are not proofs of the unresolved master claim. Clear claim facets to include catalogue-only sources.'));
  for(const c of sourceCorpus.catalogues??[])if(c.catalogue?.unpromoted_sources)panel.append(el('p',c.catalogue.unpromoted_sources,'limit'));
  if(sourceCorpus.registry_source.commit!==state.meta.commit)panel.append(el('p','The claim register has a different revision. Evidence bodies remain pinned to their bundled source snapshot.','limit'));
  if(!hits.length)panel.append(el('p','No match in this selected corpus. This does not establish absence from the wider archive.'));
  for(const d of hits.slice(0,state.limit)){
    const article=el('article',undefined,'source-hit');article.append(link(d.title+' ↗',d.url),el('p',sourceExcerpt(d.body,f.q)));
    for(const binding of d.bindings){
      if(binding.claim_id){const b=el('button',`${binding.claim_id} · ${pretty(binding.role)}`,'quiet');b.addEventListener('click',()=>select(binding.claim_id,true));article.append(b);}
      else{
        article.append(el('p',`${binding.catalogue_key??'Manifest note'} · ${pretty(binding.role)} · ${binding.label}`));
        if(binding.catalogue_record){const record=el('details');record.append(el('summary','Owned component scope and evidence distinctions'));
          for(const key of ['scope','mathematical_status','proof_authorship','independent_review','formal_status','gap'])record.append(el('strong',pretty(key)),el('p',binding.catalogue_record[key]??'Not supplied'));
          article.append(record);
        }
      }
    }
    article.append(el('small',`Source SHA256 ${d.sha256}`));panel.append(article);
  }
  if(hits.length>state.limit){const more=el('button','Show more evidence results','loadmore');more.addEventListener('click',()=>{state.limit+=12;render();});panel.append(more);}
}
function section(parent,title,text,cls){parent.append(el('h3',title),el('p',text,cls));}
function select(id,focus=false){state.selected=id;render();if(focus){$('detail').focus({preventScroll:true});if(innerWidth<=1050)$('detail').scrollIntoView({behavior:matchMedia('(prefers-reduced-motion: reduce)').matches?'auto':'smooth',block:'start'});}}
function renderDetail(){
  const c=state.data.claims.find(x=>x.id===state.selected),p=$('detail');p.replaceChildren();
  if(!c){p.append(el('h2','This claim is not in the loaded register.'),el('p','Try the latest register or the canonical board. A missing card is an indexing gap, not a disproof.'));return;}
  p.append(el('p',`${c.id} · ${c.programme}`,'eyebrow'),badge(c),el('h2',c.plain_language.question));
  p.append(el('p',c.plain_language.what_we_learned,'answer-block'));
  section(p,'What this lets you do',c.plain_language.what_it_lets_someone_do);
  section(p,'Where the result stops',c.plain_language.what_cannot_conclude,'limit');
  const exact=el('details');exact.append(el('summary','Exact statement and assumptions'),el('p',c.exact_statement_and_scope));p.append(exact);
  section(p,'Question origin',`${ORIGIN[c.origin.category]??pretty(c.origin.category)}. ${c.origin.detail}`);
  const literature=literatureSources(c);
  if(literature.length){const refs=el('ul');for(const ref of literature){const li=el('li');li.append(link(ref.label+' ↗',ref.url),el('small',' · '+pretty(ref.role)));refs.append(li);}p.append(refs);}
  else if(c.origin.category==='published_open_problem')p.append(el('p','No literature URL is indexed in the origin or prior-work references on this card; consult its source references.','limit'));
  section(p,'Prior work',c.prior_work);section(p,'The contribution here',c.our_contribution);
  section(p,'Novelty / historical priority',c.novelty_status);
  p.append(el('h3','Evidence, kept separate'));
  const ev=el('div',undefined,'evidence');
  for(const[k,title]of [['hand','Mathematics / hand review'],['formal','Formal verification'],['execution','Execution'],['empirical','Empirical admission']]){
    const value=c.evidence[k];const box=el('section');box.append(el('strong',title),el('p',pretty(value?.status)));
    if(value?.detail){const more=el('details');more.append(el('summary','Scope'),el('p',value.detail));box.append(more);}ev.append(box);
  }p.append(ev);
  p.append(el('h3','Read the proof, review or result'));
  const sources=el('ul');for(const s of c.accepted_artifacts.filter(a=>!['prior_work','historical_problem_statement'].includes(a.role))){const li=el('li');li.append(link(s.label+' ↗',s.url),el('small',' · '+pretty(s.role)));sources.append(li);}p.append(sources);
  if(c.completion?.mathematical_claim_complete===true){
    section(p,'Mathematical claim complete',c.remaining_obligation);
    if(c.separate_downstream_or_validation_work)section(p,'Separate downstream or validation work',c.separate_downstream_or_validation_work);
  }else{
    section(p,c.completion?.proof_derivation_required===true?'Remaining mathematical implication':'What remains at this scope',c.remaining_obligation);
    if(c.separate_downstream_or_validation_work)section(p,'Separate downstream or validation work',c.separate_downstream_or_validation_work);
  }
  for(const j of state.joins.filter(j=>j.claim_ids.includes(c.id))){
    p.append(el('h3',j.title),el('p',j.explanation));const list=el('ul');
    for(const s of j.links){const li=el('li');li.append(link(s.label+' ↗',s.url));list.append(li);}p.append(list);
  }
  const graph=neighbors(state.data.claims,c.id);p.append(el('h3','Connections named by the registry'));
  if(!graph.outgoing.length&&!graph.incoming.length)p.append(el('p','No typed connection is indexed for this card yet. Similar wording alone does not establish a theorem dependency.'));
  for(const[direction,items]of [['This card points to',graph.outgoing],['Other cards point here',graph.incoming]]){
    if(!items.length)continue;const edges=el('div',undefined,'connections');
    for(const r of items){const item=el('div',undefined,'connection');item.append(el('small',`${direction} · ${RELATION[r.relation_type]}`));const b=el('button',`${r.claim.id}: ${r.claim.title}`);b.addEventListener('click',()=>select(r.claim.id,true));item.append(b,el('p',r.detail??''));edges.append(item);}p.append(edges);
  }
  const tools=el('div',undefined,'tools');
  const share=el('button','Copy claim link','quiet');share.addEventListener('click',()=>{const u=new URL(location.href);u.hash=c.id;copy(u.href);});
  const reuse=el('button','Copy agent reuse record','quiet');reuse.addEventListener('click',()=>copy(JSON.stringify(reusePacket(c,state.meta,state.joins,state.ranking,state.rankingSource),null,2)));
  tools.append(share,reuse);p.append(tools);
}
async function refresh(automatic=false){
  const b=$('refresh');b.disabled=true;
  try{
    const response=await fetch('https://api.github.com/repos/Sodelin/Research-Commons/commits/main',{signal:AbortSignal.timeout(12000)});
    if(!response.ok)throw Error(`GitHub status ${response.status}`);
    const head=(await response.json()).sha;
    if(!/^[0-9a-f]{40}$/.test(head))throw Error('Invalid source commit');
    if(head===state.meta.commit){$('freshness').textContent=`Latest register checked. ${state.data.updated_utc} · source ${head.slice(0,8)}. Queries stay in this browser.`;return;}
    const raw=await fetch(`https://raw.githubusercontent.com/Sodelin/Research-Commons/${head}/docs/claims.json`,{signal:AbortSignal.timeout(12000)});
    if(!raw.ok)throw Error(`Register status ${raw.status}`);
    const data=validate(await raw.json());initialize(data,{repository:'Sodelin/Research-Commons',commit:head,path:'docs/claims.json',source_updated_utc:data.updated_utc});
    $('freshness').textContent=`Latest canonical register loaded: ${data.updated_utc} · source ${head.slice(0,8)}. Queries stay in this browser.`;
    if(!automatic)toast('Latest canonical register loaded.');
  }catch{
    $('freshness').textContent=`Latest-source check unavailable. Showing the verified bundled snapshot (${state.data.updated_utc}, ${state.meta.commit.slice(0,8)}). Search still works; check the canonical board for later results.`;
    if(!automatic)toast('Kept the bundled source. Latest-source check unavailable.');
  }finally{b.disabled=false;}
}
async function start(){
  const [dataResponse,metaResponse,joinResponse]=await Promise.all([fetch('./claims.json'),fetch('./source.json'),fetch('./reading-joins.json')]);
  if(!dataResponse.ok||!metaResponse.ok)throw Error('Could not load the bundled register.');
  const [data,meta]=await Promise.all([dataResponse.json(),metaResponse.json()]);
  if(joinResponse.ok)state.joins=(await joinResponse.json()).joins??[];
  for(const[k,v]of Object.entries(STATUS))option($('status'),k,v);
  for(const[k,v]of Object.entries(ORIGIN))option($('origin'),k,v);
  try{const [r,m]=await Promise.all([fetch('./subjective-reuse-ranking.json'),fetch('./ranking-source.json')]);if(r.ok&&m.ok){state.ranking=await r.json();state.rankingSource=await m.json();}}catch{/* Optional dated overlay never blocks claim lookup. */}
  initialize(data,meta);$('search').value=initial.get('q')??'';
  for(const k of controlKeys)$(k).value=initial.get(k)??'';
  const mode=initial.get('mode')??'all';showMode(mode);render();
  let timer; $('search').addEventListener('input',()=>{clearTimeout(timer);timer=setTimeout(()=>{state.limit=9;render();},100);});
  for(const k of controlKeys)$(k).addEventListener('change',()=>{state.limit=9;render();});
  $('reset').addEventListener('click',()=>{for(const k of ['search',...controlKeys])$(k).value='';state.selected='';state.limit=9;showMode('all');$('detail').replaceChildren(el('h2','Select a question to see its result.'));render();});
  document.querySelectorAll('nav button').forEach(b=>b.addEventListener('click',()=>{showMode(b.dataset.mode);$('status').value=['established','counterexample','open'].includes(state.mode)?state.mode:'';state.limit=9;render();}));
  document.querySelectorAll('.suggestions button').forEach(b=>b.addEventListener('click',()=>{for(const k of controlKeys)$(k).value='';$('search').value=b.dataset.query??'';if(b.dataset.topic)$('topic').value=b.dataset.topic;if(b.dataset.origin)$('origin').value=b.dataset.origin;state.limit=9;render();}));
  $('share').addEventListener('click',()=>copy(location.href));$('refresh').addEventListener('click',()=>refresh());
  addEventListener('hashchange',()=>{state.selected=decodeURIComponent(location.hash.slice(1));render();});
  addEventListener('keydown',e=>{if(e.key==='/'&&!['INPUT','TEXTAREA','SELECT'].includes(document.activeElement?.tagName)){e.preventDefault();$('search').focus();}});
  refresh(true);
}
start().catch(error=>{$('count').textContent='The reader could not load its source.';const p=el('p','Open the canonical claim board above while this source issue is repaired.','error');$('results').replaceChildren(p);console.error(error.message);});
