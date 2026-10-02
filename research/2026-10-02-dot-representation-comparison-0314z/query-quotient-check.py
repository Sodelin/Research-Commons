"""Exact finite codec/query quotient check; mathematical controls, no biological admission claim."""
from collections import defaultdict
import json
from pathlib import Path
PARTITIONS=((1,2,4),(3,4),(2,5),(1,6),(7,))
BLOCKS=(1,2,4,3,5,6,7)
MASKS=tuple(sum(1<<j for j,p in enumerate(PARTITIONS) if b in p) for b in BLOCKS)
assert MASKS==(9,5,3,2,4,8,16)
classes=defaultdict(list)
checks=0
for s in range(1,32):
    support=[PARTITIONS[j] for j in range(5) if s>>j&1]
    possible=sum(1<<i for i,m in enumerate(MASKS) if s&m)
    sure=sum(1<<i for i,m in enumerate(MASKS) if s&m==s)
    for i,b in enumerate(BLOCKS):
        assert bool(possible>>i&1)==any(b in p for p in support)
        assert bool(sure>>i&1)==all(b in p for p in support)
        checks+=1
    classes[possible,sure].append(s)
assert len(classes)==29
assert sorted(v for v in classes.values() if len(v)>1)==[[14,15],[30,31]]
report={'status':'PASS_FINITE_QUERY_QUOTIENT','attribution':'dot, representation literature lane, 2026-10-02',
'partition_alphabet':PARTITIONS,'block_order':BLOCKS,'incidence_masks':MASKS,
'exact_support_inputs':31,'block_query_pairs_checked':checks,'query_answer_classes':len(classes),
'full_support_fixed_width_bits':5,'query_quotient_fixed_width_bits':5,
'query_cache_bits':14,'cache_coarsening_collisions':sorted(v for v in classes.values() if len(v)>1),
'limits':['One declared 3-label panel and one calendar time only','All abstract nonempty supports checked; not all assumed source-admitted','Possible/sure query quotient is not an injective encoding of partition support','No law inversion, runtime speedup, source membership or entire calendar-law encoding claimed']}
Path(__file__).with_name('query-quotient-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
