#!/usr/bin/env python3
"""Offline evidence/count replay; not primary theorem verification.
GPT-6.1 Sol / continue_g_research, 2026-10-02.
"""
from pathlib import Path
import json,hashlib,time
P=Path(__file__).parent;t=time.perf_counter()
read=lambda n:json.loads((P/n).read_text())
s=read('seed.json');d=read('direct-citers.json');r=read('coupling-and-cocitation.json');c=read('canonical-neighborhood.json');l=read('PRIMARY-EDGE-LEDGER.json');b=read('BACKWARD-REFERENCES.json')
ws=[w for p in d['pages'] for w in p['results']]
assert len(ws)==6 and d['cursor_exhausted'] and d['pages'][-1]['meta']['next_cursor'] is None
assert len({w['id'] for w in ws})==6 and all(s['id'] in w['referenced_works'] for w in ws)
assert len(b['entries'])==24 and [e['number'] for e in b['entries']]==list(range(1,25))
assert len(r['seed_cocitations'])==131 and len({e['id'] for e in r['seed_cocitations']})==131
assert len(c['works'])==c['distinct_focus_families']==13 and len(c['coupling_pairs'])==26
alias={i:g[0] for g in c['explicit_alias_families'] for i in g};C=lambda i:alias.get(i,i)
w={e['id']:e for e in c['works']}
for q in c['coupling_pairs']:
 a=set(w[q['a']]['reference_ids']);bb=set(w[q['b']]['reference_ids'])
 assert sorted(a&bb)==q['shared_ids'] and len(a&bb)==q['shared_count']
 assert q['jaccard']==len(a&bb)/len(a|bb)
assert len(s['referenced_works'])==21 and c['resolved_distinct_seed_references']==19
seedpairs=[q for q in c['coupling_pairs'] if s['id'] in (q['a'],q['b'])]
assert max(q['shared_count'] for q in seedpairs)==6
assert l['distinct_substantiated_direct_citing_works']==7
assert len([e for e in l['forward_edges'] if e.get('primary_reference_number')])==6
assert l['manual_primary_coupling']['shared_count']==4
assert c['unresolved_seed_ids']==['https://openalex.org/W6743923201']
receipt={'status':'PASS','scope':'Offline exact saved graph/count replay. Primary reference-list/theorem checks are separately attributed evidence, not machine-derived by this script.','seconds':time.perf_counter()-t,'backward_primary_entries':24,'indexed_direct_citers':6,'cursor_exhausted':True,'direct_seed_id_edges_pass':6,'primary_validated_index_edges':5,'additional_primary_direct_citer':1,'canonical_focus_families':13,'canonical_coupling_pairs':26,'raw_other_cocited_ids':131,'strongest_seed_coupling':6,'manual_additional_primary_coupling':4,'input_sha256':{n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['seed.json','direct-citers.json','coupling-and-cocitation.json','canonical-neighborhood.json','PRIMARY-EDGE-LEDGER.json','BACKWARD-REFERENCES.json']}}
(P/'neighborhood-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
