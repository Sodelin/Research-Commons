from fetch_helpers import ROOT,fetch,save,FIELDS
import json,urllib.parse
r=json.load(open(ROOT/'coupling-and-cocitation.json'));ids=sorted({v for w in r['focus_records'] for v in w.get('referenced_works',[])})
meta=json.load(open(ROOT/'reference-and-cocitation-metadata.json'))
for i in range(0,len(ids),70):
 q={'filter':'openalex_id:'+'|'.join(x.rsplit('/',1)[-1] for x in ids[i:i+70]),'per-page':'200','select':FIELDS}
 meta.update({w['id']:w for w in fetch('https://api.openalex.org/works?'+urllib.parse.urlencode(q))['results']})
save('all-focus-reference-metadata.json',meta)
for doi,key in [('10.1007/s10474-022-01265-8','size-forcing'),('10.48550/arxiv.2412.02462','zero-expansions')]:
 seed=fetch('https://api.openalex.org/works/https://doi.org/'+doi);save(key+'-seed.json',seed);sid=seed['id'].rsplit('/',1)[-1];cursor='*';pages=[]
 while cursor:
  q={'filter':f'cites:{sid},to_publication_date:2026-10-02','per-page':'200','sort':'publication_date:desc','cursor':cursor,'select':FIELDS}
  d=fetch('https://api.openalex.org/works?'+urllib.parse.urlencode(q));pages.append(d);cursor=d['meta'].get('next_cursor')
  if len(pages)>4 and cursor:raise RuntimeError('Second-hop cap reached')
 save(key+'-citers.json',{'seed_id':seed['id'],'pages':pages,'cursor_exhausted':not cursor})
 print('SECOND-HOP',key,pages[0]['meta']['count'],'exhausted',not cursor)
 for page in pages:
  for w in page['results']:print(' ',w['publication_date'],w['title'],w.get('doi'))
