import {validate,search,topic,bucket,STATUS,ORIGIN,RELATION,neighbors,reusePacket,safeLink} from './model.mjs';
const $=id=>document.getElementById(id);
const state={data:null,meta:null,limit:9,selected:decodeURIComponent(location.hash.slice(1)),mode:'all',joins:[]};
const initial=new URLSearchParams(location.search);
function el(tag,text,cls){const x=document.createElement(tag);if(text!==undefined)x.textContent=text;if(cls)x.className=cls;return x;}
function add(parent,...children){parent.append(...children);return parent;}
function link(label,url){const a=el('a',label);const safe=safeLink(url);if(!safe){a.removeAttribute('href');return a;}a.href=safe;a.target='_blank';a.rel='noopener';return a;}
const pretty=s=>String(s??'').replaceAll('_',' ');
function badge(c){return el('span',STATUS[bucket(c)],'badge '+bucket(c));}
function filters(){return {q:$('search').value,topic:$('topic').value,status:$('status').value,origin:$('origin').value};}
function writeRoute(){const u=new URL(location.href);u.search='';for(const[k,v]of Object.entries(filters()))if(v)u.searchParams.set(k,v);if(state.mode==='reuse'||state.mode==='connections')u.searchParams.set('mode',state.mode);u.hash=state.selected;history.replaceState(null,'',u);}
function toast(message){const target=$('toast');if(!target)return;target.textContent=message;target.style.display='block';setTimeout(()=>target.style.display='none',3000);}
async function copy(text){try{await navigator.clipboard.writeText(text);toast('Copied.');}catch{toast('Clipboard unavailable. Select the text or copy the page address.');}}
function option(select,value,label){const o=el('option',label);o.value=value;select.append(o);}
function initialize(data,meta){
  validate(data);state.data=data;state.meta=meta;
  const old=filters();$('topic').replaceChildren();option($('topic'),'','All topics');
  for(const t of [...new Set(data.claims.map(topic))])option($('topic'),t,t);
  $('topic').value=old.topic;
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
  const f=filters(),matches=search(state.data.claims,f),results=$('results');results.replaceChildren();
  $('count').textContent=`${matches.length} of ${state.data.claims.length} indexed claims${state.mode==='connections'?' · select a card to follow its typed connections':''}`;
  if(!matches.length){results.append(el('p','No indexed claim matches these filters. Try fewer terms or reset the filters. This is not evidence that no result exists in the archive.','empty'));results.append(link('Search the wider public source archive ↗','https://github.com/search?type=code&q='+encodeURIComponent('repo:Sodelin/Research-Commons '+f.q)));}
  for(const c of matches.slice(0,state.limit)){
    const article=el('article',undefined,'claim'+(c.id===state.selected?' selected':''));
    article.append(el('p',c.programme,'topic'));
    const h=el('h2');const button=el('button',c.plain_language.question);button.addEventListener('click',()=>select(c.id,true));h.append(button);article.append(h);
    article.append(el('p',c.plain_language.what_we_learned,'answer'),badge(c));
    const n=neighbors(state.data.claims,c.id);const bottom=el('div',undefined,'claim-bottom');
    add(bottom,el('span',c.id),el('span',`${n.outgoing.length+n.incoming.length} connections`));article.append(bottom);results.append(article);
  }
  if(matches.length>state.limit){const more=el('button',`Show ${Math.min(12,matches.length-state.limit)} more`,'loadmore');more.addEventListener('click',()=>{state.limit+=12;render();});results.append(more);}
  if(state.selected)renderDetail();writeRoute();
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
  if(c.origin.source_url)p.append(link('Original published question ↗',c.origin.source_url));
  section(p,'Prior work',c.prior_work);section(p,'The contribution here',c.our_contribution);
  section(p,'Novelty / historical priority',c.novelty_status);
  p.append(el('h3','Evidence, kept separate'));
  const ev=el('div',undefined,'evidence');
  for(const[k,title]of [['hand','Mathematics / hand review'],['formal','Formal verification'],['execution','Execution'],['empirical','Empirical admission']]){
    const value=c.evidence[k];const box=el('section');box.append(el('strong',title),el('p',pretty(value?.status)));
    if(value?.detail){const more=el('details');more.append(el('summary','Scope'),el('p',value.detail));box.append(more);}ev.append(box);
  }p.append(ev);
  p.append(el('h3','Read the proof, review or result'));
  const sources=el('ul');for(const s of c.accepted_artifacts){const li=el('li');li.append(link(s.label+' ↗',s.url));sources.append(li);}p.append(sources);
  section(p,'What remains',c.remaining_obligation);
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
  const reuse=el('button','Copy agent reuse record','quiet');reuse.addEventListener('click',()=>copy(JSON.stringify(reusePacket(c,state.meta,state.joins),null,2)));
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
  initialize(data,meta);$('search').value=initial.get('q')??'';
  for(const k of ['topic','status','origin'])$(k).value=initial.get(k)??'';
  const mode=initial.get('mode')??'all';showMode(mode);render();
  let timer; $('search').addEventListener('input',()=>{clearTimeout(timer);timer=setTimeout(()=>{state.limit=9;render();},100);});
  for(const k of ['topic','status','origin'])$(k).addEventListener('change',()=>{state.limit=9;render();});
  $('reset').addEventListener('click',()=>{for(const k of ['search','topic','status','origin'])$(k).value='';state.selected='';state.limit=9;showMode('all');$('detail').replaceChildren(el('h2','Select a question to see its result.'));render();});
  document.querySelectorAll('nav button').forEach(b=>b.addEventListener('click',()=>{showMode(b.dataset.mode);$('status').value=['established','counterexample','open'].includes(state.mode)?state.mode:'';state.limit=9;render();}));
  document.querySelectorAll('.suggestions button').forEach(b=>b.addEventListener('click',()=>{for(const k of ['topic','status','origin'])$(k).value='';$('search').value=b.dataset.query??'';if(b.dataset.topic)$('topic').value=b.dataset.topic;if(b.dataset.origin)$('origin').value=b.dataset.origin;state.limit=9;render();}));
  $('share').addEventListener('click',()=>copy(location.href));$('refresh').addEventListener('click',()=>refresh());
  addEventListener('hashchange',()=>{state.selected=decodeURIComponent(location.hash.slice(1));render();});
  addEventListener('keydown',e=>{if(e.key==='/'&&!['INPUT','TEXTAREA','SELECT'].includes(document.activeElement?.tagName)){e.preventDefault();$('search').focus();}});
  refresh(true);
}
start().catch(error=>{$('count').textContent='The reader could not load its source.';const p=el('p','Open the canonical claim board above while this source issue is repaired.','error');$('results').replaceChildren(p);console.error(error.message);});
