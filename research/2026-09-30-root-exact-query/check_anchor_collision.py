"""Fold two five-taxon occurrence trees; certify source admission and oracle collision."""
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path

SOURCE = Path(__file__).resolve().parent / 'inputs/exact_networks.py'
spec = importlib.util.spec_from_file_location('exact_networks', SOURCE)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

FIXTURES = [
    {'name':'N1','tips':(0,0,1,1,2,3,4), 'top':(0, ((((1,2),(3,4)),5),6)), 'expected':7021},
    {'name':'N2','tips':(0,0,1,2,2,3,4), 'top':(0, (((1,(2,3)),(4,5)),6)), 'expected':23405},
]

def construct(fix):
    edges, rot = set(), {}
    serial = 0
    def subtree(t, parent):
        nonlocal serial
        if isinstance(t,int):
            leaf = 'O'+str(t)
            edges.add(mod.edge(parent,leaf))
            rot[leaf] = [parent]
            return leaf
        v = 'U'+str(serial)
        serial += 1
        edges.add(mod.edge(parent,v))
        left = subtree(t[0],v)
        right = subtree(t[1],v)
        rot[v] = [parent,left,right]
        return v
    rootrest = subtree(fix['top'][1], 'O0')
    rot['O0'] = [rootrest]
    hybrids, leaves = {}, set()
    for label in range(5):
        occs = [i for i,t in enumerate(fix['tips']) if t==label]
        leaf = 'T'+str(label)
        leaves.add(leaf)
        if len(occs)==1:
            old = 'O'+str(occs[0])
            p = rot.pop(old)[0]
            edges.remove(mod.edge(old,p))
            edges.add(mod.edge(leaf,p))
            rot[p][rot[p].index(old)] = leaf
            rot[leaf] = [p]
        else:
            olda,oldb = ['O'+str(i) for i in occs]
            pa,pb = rot.pop(olda)[0],rot.pop(oldb)[0]
            assert pa!=pb, 'parent-coincident pair would introduce parallel edges'
            h = 'H'+str(label)
            hybrids[h] = (pa,pb)
            for old,p in ((olda,pa),(oldb,pb)):
                edges.remove(mod.edge(old,p))
                edges.add(mod.edge(h,p))
                rot[p][rot[p].index(old)] = h
            edges.add(mod.edge(h,leaf))
            rot[leaf] = [h]
    # Put the rooted partner's root on the ordinary taxon-4 pendant edge.
    root = 'ROOT'
    p = rot['T4'][0]
    edges.remove(mod.edge(p,'T4'))
    edges.update((mod.edge(p,root),mod.edge(root,'T4')))
    rot[p][rot[p].index('T4')] = root
    rot['T4'] = [root]
    rot[root] = [p,'T4']
    for signs in product((0,1),repeat=len(hybrids)):
        candidate = {v:ns.copy() for v,ns in rot.items()}
        for (h,(pa,pb)),sign in zip(sorted(hybrids.items()),signs):
            leaf = 'T'+h[1:]
            candidate[h] = [pa,pb,leaf] if sign==0 else [pa,leaf,pb]
        net = mod.Net(edges,leaves,hybrids,root,candidate,fix['name'])
        try:
            cert = net.validate()
        except AssertionError:
            continue
        return net,cert
    raise AssertionError('no source-admitted rotation/root certificate')

def encode(qs):
    value=0
    for i,q in enumerate(combinations(range(5),4)):
        taxa=tuple('T'+str(t) for t in q)
        a,b,c,d=taxa
        for j,pair in enumerate(((a,b),(a,c),(a,d))):
            if mod.canonical_split(pair,taxa) in qs[taxa]:
                value |= 1 << (3*i+j)
    return value

records=[]
systems=[]
supports=[]
for fix in FIXTURES:
    net,cert=construct(fix)
    qs,trees=mod.quartet_system(net)
    pattern=encode(qs)
    assert pattern==fix['expected'], (fix['name'],pattern)
    support=set().union(*trees)
    systems.append(qs)
    supports.append(support)
    records.append({'name':fix['name'],'admission':cert,'edges':sorted(net.edges),
                    'hybrids':net.hybrids,'root':net.root,'rotation':net.rotation,
                    'quartet_pattern':pattern,
                    'quartets':{''.join(t[1:] for t in q):sorted(map(list,s)) for q,s in qs.items()},
                    'distinct_displayed_trees':len(set(trees)),
                    'displayed_splits':sorted(map(list,support))})

anchored=[q for q in systems[0] if 'T0' in q]
assert all(systems[0][q]==systems[1][q] for q in anchored)
different=[q for q in systems[0] if systems[0][q]!=systems[1][q]]
assert different==[('T1','T2','T3','T4')]
witness=mod.canonical_split(('T2','T3'),['T'+str(t) for t in range(5)])
assert witness not in supports[0] and witness in supports[1]
record={'status':'PASS','source_verifier_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'fixtures':records,'fixed_anchor':'T0','equal_anchored_quartets':len(anchored),
        'different_quartets':different,
        'split_in_N2_not_N1':['T2','T3'],
        'N1_minus_N2':sorted(map(list,supports[0]-supports[1])),
        'N2_minus_N1':sorted(map(list,supports[1]-supports[0])),
        'scope':'Executed source admission and exact switching/support collision; not a master query bound.'}
Path(__file__).with_name('anchor-collision-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'fixtures':[(r['name'],r['admission']) for r in records],
                  'equal_anchored_quartets':len(anchored),'different_quartets':different,
                  'N1_minus_N2':record['N1_minus_N2'],'N2_minus_N1':record['N2_minus_N1']},indent=2))
