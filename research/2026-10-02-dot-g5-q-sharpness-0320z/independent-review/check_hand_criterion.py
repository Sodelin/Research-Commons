"""Cross-check proposed closed absence criterion against independent selector oracle."""
from check_partition_kernel import restricted_growth, counts, selector_oracle, PAIRS, SPLITS
import json
from pathlib import Path

def absent_by_counts(k,a,b,c,d):
    m={frozenset(ij):v for ij,v in zip(PAIRS,k)}
    get=lambda i,j:m[frozenset((i,j))]
    x,y=get(a,b),get(c,d)
    ac,ad,bc,bd=get(a,c),get(a,d),get(b,c),get(b,d)
    return (
        (x==0 and y==0)
        or 4 in (ac,ad,bc,bd)
        or (x==1 and y==0 and ((ac==bc==2) or (ad==bd==2)))
        or (x==0 and y==1 and ((ac==ad==2) or (bc==bd==2)))
        or ({x,y}=={0,2} and ac==ad==bc==bd==2)
    )
checked=0
for r in restricted_growth(8):
    k=counts(r); mask=selector_oracle(r)
    for si,s in enumerate(SPLITS):
        assert absent_by_counts(k,*s)==(not bool(mask&(1<<si))),(r,k,s,mask)
        checked+=1
result={'status':'PASS','partition_split_checks':checked,'criterion':'five exact absence cases','domain':'four disjoint two-occurrence labels on arbitrary set partitions'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
