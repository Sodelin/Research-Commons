"""Independent Bell(8) kernel check, with a selector-based quartet oracle.
No external dependencies. Occurrences 0,1 are a; 2,3 b; 4,5 c; 6,7 d.
"""
from itertools import product
from collections import defaultdict, Counter
import json, hashlib
from pathlib import Path

PAIRS = tuple((i,j) for i in range(4) for j in range(i+1,4))
SPLITS = ((0,1,2,3),(0,2,1,3),(0,3,1,2))

def restricted_growth(n, prefix=(0,)):
    if len(prefix) == n:
        yield prefix
    else:
        for entry in range(max(prefix)+2):
            yield from restricted_growth(n, prefix+(entry,))

def counts(r):
    return tuple(sum(r[2*i+ci]==r[2*j+cj] for ci,cj in product(range(2),repeat=2)) for i,j in PAIRS)

def selector_oracle(r):
    mask=0
    for choice in product(range(2),repeat=4):
        chosen=tuple(r[2*i+choice[i]] for i in range(4))
        for si,(a,b,c,d) in enumerate(SPLITS):
            # One selected pair occupies a common block and the other two
            # selected labels are both outside that block.
            if ((chosen[a]==chosen[b] and chosen[c]!=chosen[a] and chosen[d]!=chosen[a]) or
                (chosen[c]==chosen[d] and chosen[a]!=chosen[c] and chosen[b]!=chosen[c])):
                mask |= 1<<si
    return mask

def occupancy_oracle(r):
    columns=[]
    for block in range(max(r)+1):
        columns.append(tuple(sum(r[2*i+k]==block for k in range(2)) for i in range(4)))
    mask=0
    for si,(a,b,c,d) in enumerate(SPLITS):
        if any((v[a]>0 and v[b]>0 and v[c]<2 and v[d]<2) or
               (v[c]>0 and v[d]>0 and v[a]<2 and v[b]<2) for v in columns):
            mask |= 1<<si
    return mask

def main():
    fibers=defaultdict(lambda:defaultdict(list))
    for r in restricted_growth(8):
        k=counts(r)
        direct=selector_oracle(r)
        assert direct==occupancy_oracle(r),r
        fibers[k][direct].append(r)
    collisions=[{'K':k,'witnesses': {str(q):rows[0] for q,rows in f.items()}} for k,f in fibers.items() if len(f)>1]
    assert not collisions, collisions
    assert len(fibers)==403, len(fibers)
    assert sum(sum(len(v) for v in f.values()) for f in fibers.values())==4140
    result={'partitions':sum(sum(len(v) for v in f.values()) for f in fibers.values()),
            'pair_count_vectors':len(fibers),'collisions':collisions,
            'quartet_mask_frequencies_by_partition':dict(Counter(q for f in fibers.values() for q,rs in f.items() for _ in rs)),
            'quartet_mask_frequencies_by_vector':dict(Counter(next(iter(f)) for f in fibers.values())),
            'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == "__main__":
    main()
