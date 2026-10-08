"""Add an explicit original-taxon display map to existing original solver outputs.
Preserves raw L_i target and prior comparison; does not relabel source certificates.
"""
from pathlib import Path
import json
B=Path(__file__).resolve().parent;P=B/'CWU-RUNS/COMPARISON.json'
x=json.loads(P.read_text());raw=P.read_bytes()
old=B/'CWU-RUNS/COMPARISON-before-explicit-ids.json'
if not old.exists():old.write_bytes(raw)
request=json.loads((B/'CWU-RUNS/synthetic_nuclear_like/REQUEST.json').read_text())
lookup={'L'+str(i):t for i,t in enumerate(request['taxa'])}
assert all(request['rows'][0]['samples'][t]==['L'+str(i)] for i,t in enumerate(request['taxa']))
def decode(t):
 if isinstance(t,list):return [decode(q) for q in t]
 if t is None:return None
 return lookup[t]
x['original_taxon_map']=lookup
for c in x['original_solver_controls']:c['decoded_original_taxon_target']=decode(c['target'])
x['mapping_evidence']='Original request taxa and original-taxon→copy sampling map; species-level display categories only, no verified specimen/accession join.'
assert x['original_solver_controls'][0]['decoded_original_taxon_target']==[[['Tsuga_chinensis','Tsuga_caroliniana'],['Tsuga_sieboldii_Japan','Tsuga_diversifolia']]]
assert x['original_solver_controls'][1]['decoded_original_taxon_target']==[[['Tsuga_chinensis','Tsuga_sieboldii_Japan'],['Tsuga_caroliniana','Tsuga_diversifolia']]]
P.write_text(json.dumps(x,indent=2)+'\n');print('PASS original-taxon map and both decoded targets; raw outputs preserved')
