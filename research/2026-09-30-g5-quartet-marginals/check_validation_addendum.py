"""Exact extracted-validator regression, not a replay of the full old script.

OldSource.__init__/validate below retain the validation logic retrieved from
verify_g5.py, Git blob 6f76613b69b12bda1633e398c45529c461d56765.
Only formatting is normalized. The current quartet fixtures use the earlier
Source implementation, which separately infers actual structural hybrids.
"""
from fractions import Fraction as F
from copy import deepcopy
from pathlib import Path
import json
import networkx as nx
from metric_partition_inverse import supplied_fixtures
from validate_source_record import validate_source_record

class OldSource:
    def __init__(self, record):
        self.name=record['name'];self.labels=tuple(record['labels'])
        self.ages={v:F(a) for v,a in record['ages'].items()}
        self.edges=tuple((e['id'],e['parent'],e['child']) for e in record['edges'])
        self.hybrids=set(record['inheritance'])
        self.ins={v:[] for v in self.ages};self.out={v:[] for v in self.ages}
        self.graph=nx.DiGraph();self.graph.add_nodes_from(self.ages)
        for eid,u,v in self.edges:
            self.ins[v].append(eid);self.out[u].append(eid);self.graph.add_edge(u,v)
        self.edge_map={e:(u,v) for e,u,v in self.edges}
        self.times=sorted(set(self.ages.values()))
        self.validate(record)
    def validate(self,record):
        assert nx.is_directed_acyclic_graph(self.graph)
        roots=[v for v in self.ages if not self.ins[v]];assert len(roots)==1
        self.root=roots[0]
        for v in self.ages:
            deg=(len(self.ins[v]),len(self.out[v]))
            assert deg==((0,2) if v==self.root else (1,0)) if v in self.labels or v==self.root else deg in ((1,2),(2,1))
        assert all(self.ages[u]>self.ages[v] for _,u,v in self.edges)
        assert all(self.ages[x]==0 for x in self.labels)
        assert all(F(e['rate'])>0 for e in record['edges']) and F(record['ancestral_rate'])>0
        assert all(0<F(g)<1 for g in record['inheritance'].values())
        U=nx.MultiGraph();U.add_nodes_from(self.ages)
        for eid,u,v in self.edges:U.add_edge(u,v,key=eid)
        for h in self.hybrids:
            eid=self.out[h][0];u,v=self.edge_map[eid];W=U.copy();W.remove_edge(u,v,eid)
            assert not nx.has_path(W,u,v)
        dom={}
        for v in nx.topological_sort(self.graph):
            parents=list(self.graph.predecessors(v))
            dom[v]={v}|(set.intersection(*(dom[p] for p in parents)) if parents else set())
        assert set.intersection(*(dom[x] for x in self.labels))=={self.root}
        aug=nx.Graph(U);aug.add_edges_from(('__apex__',x) for x in self.labels)
        assert nx.check_planarity(aug)[0]

s=supplied_fixtures()[2]
record={'name':s.name,'labels':s.labels,'ages':s.ages,'edges':[e.__dict__ for e in s.edges],
        'inheritance':{h:str(g) for h,g in s.inheritance.items()},'ancestral_rate':s.ancestral_rate}
OldSource(record);validate_source_record(record)
missing=deepcopy(record);missing['inheritance']={}
old=OldSource(missing)
assert 'h' not in old.hybrids and len(old.ins['h'])==2
caught=False
try:validate_source_record(missing)
except ValueError:caught=True
assert caught
suite=json.loads((Path(__file__).parent/'isolated-suite/fixtures.json').read_text())
for r in suite:validate_source_record(r)
result={'status':'PASS','extracted_old_validator_accepts_missing_hybrid_probability':True,
        'supplemental_guard_rejects_mutation':True,'current_source_records_passing_guard':len(suite),
        'effect':'Fixture-schema validation defect, not an admitted counterexample or a failure of the G5 theorem; supplied fixtures retained.'}
(Path(__file__).parent/'validation-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
