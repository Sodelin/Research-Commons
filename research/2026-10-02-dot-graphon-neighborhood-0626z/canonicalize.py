from pathlib import Path
import json,collections,itertools,unicodedata
P=Path(__file__).parent;r=json.load(open(P/'coupling-and-cocitation.json'));meta=json.load(open(P/'all-focus-reference-metadata.json'));seed=json.load(open(P/'seed.json'));zero=json.load(open(P/'zero-expansions-seed.json'))
focus={v['id']:v for v in r['focus_records']};focus[zero['id']]=zero
# Explicit report families: journal preferred; no automatic same-title merge across unrelated works.
alias=[['https://openalex.org/W4309879554','https://openalex.org/W3139238831','https://openalex.org/W4287268256'],['https://openalex.org/W1970138544','https://openalex.org/W2949893036'],['https://openalex.org/W2964056543','https://openalex.org/W2754699279'],['https://openalex.org/W1983614667','https://openalex.org/W4255284598']]
canon={x:g[0] for g in alias for x in g}
C=lambda i:canon.get(i,i)
works={}
for i,v in focus.items():
 k=C(i)
 if k not in works:works[k]=dict(v,report_ids=[],reference_ids=set())
 works[k]['report_ids'].append(i);works[k]['reference_ids']|={C(x) for x in v.get('referenced_works',[])}
rows=[]
for a,b in itertools.combinations(works,2):
 sa,sb=works[a]['reference_ids'],works[b]['reference_ids'];shared=sorted(sa&sb)
 if shared:rows.append({'a':a,'a_title':works[a]['title'],'b':b,'b_title':works[b]['title'],'shared_count':len(shared),'jaccard':len(shared)/len(sa|sb),'shared_ids':shared,'shared_titles':[meta.get(x,{}).get('title') for x in shared]})
rows.sort(key=lambda x:(-x['shared_count'],-x['jaccard']))
for w in works.values():w['reference_ids']=sorted(w['reference_ids'])
report={'scope':'One DOI-exact dated index first-hop, primary-backward bibliography, explicit journal/preprint/conference alias families and selected second-hop topical records; no global exhaustive-literature claim.',
 'distinct_focus_families':len(works),'report_records_before_alias_merge':len(focus),'explicit_alias_families':alias,'works':list(works.values()),'coupling_pairs':rows,
 'indexed_seed_reference_ids':len(seed['referenced_works']),'resolved_distinct_seed_references':len({C(x) for x in seed['referenced_works'] if x in meta}),'unresolved_seed_ids':[x for x in seed['referenced_works'] if x not in meta],
 'primary_bibliography_references':24,'direct_seed_citers_indexed_exhausted':6,'primary_additional_direct_citer':{'title':'Adjunctions, Box Products, and Forcing Families','arxiv':'2412.12904v2','version_date':'2026-09-21','primary_reference_number':29,'index_absence_note':'not present in the DOI-exact six-citer seed graph'},
 'source_coverage_note':'Raw index contains a duplicate Kurtz record and one unresolved ID; 21 IDs are not 21 distinct verified primary references.'}
(P/'canonical-neighborhood.json').write_text(json.dumps(report,indent=2)+'\n')
print('CANONICAL families',len(works),'coupling pairs',len(rows),'primary-backrefs24, index raw21, resolveddistinct',report['resolved_distinct_seed_references'])
for v in rows:
 if seed['id'] in (v['a'],v['b']):print('SEED COUPLING',v['shared_count'],v['a_title'],'//',v['b_title'],v['shared_titles'])
