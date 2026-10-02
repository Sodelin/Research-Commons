#!/usr/bin/env python3
"""Official DOI-exact OpenAlex neighborhood; public read-only audit.
Adapts the successful E-lane route with attribution; no credentials/auth.
Author: GPT-6.1 Sol / continue_g_research, 2026-10-02.
"""
from pathlib import Path
import urllib.request,urllib.parse,json,time,concurrent.futures,itertools,collections,hashlib
ROOT=Path(__file__).parent;LOG=[];STAMP='2026-10-02T06:07:00Z'
FIELDS='id,doi,title,publication_year,publication_date,type,referenced_works,primary_location'
def fetch(url):
 request=urllib.request.Request(url,headers={'User-Agent':'Research evidence audit (read-only)'})
 with urllib.request.urlopen(request,timeout=40) as r:data=json.load(r)
 LOG.append({'context_utc':STAMP,'url':url,'status':'OK','count':data.get('meta',{}).get('count')});return data

def save(name,data): (ROOT/name).write_text(json.dumps(data,indent=2)+'\n')
seed=fetch('https://api.openalex.org/works/https://doi.org/10.1080/00029890.2021.1926187');save('seed.json',seed)
sid=seed['id'].split('/')[-1];cursor='*';pages=[];citers=[]
while cursor:
 params={'filter':f'cites:{sid},to_publication_date:2026-10-02','per-page':'200','sort':'publication_date:desc','cursor':cursor,'select':FIELDS}
 page=fetch('https://api.openalex.org/works?'+urllib.parse.urlencode(params));pages.append(page);citers+=page['results'];cursor=page['meta'].get('next_cursor')
 if len(pages)>=10 and cursor:raise RuntimeError('unexpected >2000 seed citations; preserve bounded partial before review')
assert all(seed['id'] in w['referenced_works'] for w in citers)
save('direct-citers.json',{'pages':pages,'seed_id':seed['id'],'cursor_exhausted':not cursor})
print('SEED',seed['title'],'index refs',len(seed['referenced_works']),'citing edges',len(citers),'pages',len(pages),'exhausted',not cursor,flush=True)
for w in citers:print('CITER',w['publication_date'],w['title'],w.get('doi'),flush=True)
# Metadata for all direct references and all repeatedly co-cited works. IDs are graph evidence.
refset=set(seed['referenced_works']);allref=collections.Counter(r for w in citers for r in set(w.get('referenced_works',[])) if r!=seed['id'])
metaids=sorted(refset|{r for r,n in allref.items() if n>=2})
metadata={}
for i in range(0,len(metaids),70):
 ids='|'.join(v.rsplit('/',1)[-1] for v in metaids[i:i+70])
 params={'filter':'openalex_id:'+ids,'per-page':'200','select':FIELDS}
 d=fetch('https://api.openalex.org/works?'+urllib.parse.urlencode(params))
 metadata.update({w['id']:w for w in d['results']})
save('reference-and-cocitation-metadata.json',metadata)
# Adjacent topical works are separate from actual citation edges.
queries=['On a question of Vera T. Sós about size forcing of graphons','On series expansions of zeros of the deformed exponential function','Forcing Quasirandomness via Rooted F-Densities','Finitely forcible graphons','Note on forcing pairs','Zeros of the deformed exponential function','General solution for the second-order nonlocal linear differential equation','Numerical investigation of the pantograph equation','Transformation of Stochastic Recursions and Critical Phenomena in the Analysis of a Class of Mean Flow Equations','Nonlocal Integrable Equations in Soliton Theory']
def search(q):
 params={'search':q,'per-page':'5','select':FIELDS}
 try:return {'query':q,'response':fetch('https://api.openalex.org/works?'+urllib.parse.urlencode(params))}
 except Exception as e:return {'query':q,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:adj=list(pool.map(search,queries))
save('adjacent-title-resolution.json',adj)
focus={seed['id']:seed,**{w['id']:w for w in citers}}
# Accept exact title equality for adjacent candidates; nonexact hits remain unscreened.
def norm(t):return ''.join(x.lower() for x in t if x.isalnum())
for a in adj:
 for w in a.get('response',{}).get('results',[]):
  if norm(w['title'])==norm(a['query']):focus[w['id']]=w
coupling=[]
for aid,bid in itertools.combinations(focus,2):
 aa=set(focus[aid].get('referenced_works',[]));bb=set(focus[bid].get('referenced_works',[]));shared=sorted(aa&bb)
 if shared:coupling.append({'a':aid,'a_title':focus[aid]['title'],'b':bid,'b_title':focus[bid]['title'],'shared_count':len(shared),'jaccard':len(shared)/len(aa|bb),'shared_ids':shared,'shared_titles':[metadata.get(i,{}).get('title') for i in shared]})
co=[{'id':i,'title':metadata.get(i,{}).get('title'),'doi':metadata.get(i,{}).get('doi'),'cociting_works':n,'citer_ids':[w['id'] for w in citers if i in set(w.get('referenced_works',[]))]} for i,n in allref.items()]
co.sort(key=lambda w:(-w['cociting_works'],w['id']))
report={'context_utc':STAMP,'seed_id':seed['id'],'seed_doi':seed['doi'],'primary_bibliography_count':24,'index_reference_count':len(refset),
 'direct_citing_count_index':pages[0]['meta']['count'],'direct_citers_retrieved':len(citers),'all_direct_citing_edges_verified_in_index':True,'seed_cursor_exhausted':not cursor,
 'metadata_direct_references_retrieved':len(refset&metadata.keys()),'focus_records':list(focus.values()),'coupling':sorted(coupling,key=lambda v:(-v['shared_count'],-v['jaccard'])),
 'seed_cocitations':co,'scope':'Complete dated first-hop within this OpenAlex seed record; index metadata are not primary theorem validation. Coupling/co-citation census restricted to retrieved records, not global literature completeness. Primary bibliography has 24 references; index contains 21.'}
save('coupling-and-cocitation.json',report);save('QUERY-LOG.json',LOG)
print('FOCUS',len(focus),'coupled pairs',len(coupling),'co-cited other works',len(co),flush=True)
for v in report['coupling'][:15]:print('COUPLING',v['shared_count'],v['a_title'],'//',v['b_title'],flush=True)
print('COMPLETE source hash',hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),flush=True)
