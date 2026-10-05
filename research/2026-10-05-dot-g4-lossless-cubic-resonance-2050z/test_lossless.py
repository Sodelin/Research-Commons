import unittest,hashlib,importlib.util
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import lossless_resonance as s
p=Path(__file__).resolve().parent.parent/'graph-g3-allcap-insertion-20261005-0601z/forest_algebra_pinned.py';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884':raise ValueError('test provider pin')
spec=importlib.util.spec_from_file_location('_forest_exact',p);a=importlib.util.module_from_spec(spec);exec(compile(raw,str(p),'exec'),a.__dict__)
def shape(t):return 'x' if isinstance(t,int) else s.tree(shape(t[0]),shape(t[1]))
class Small(unittest.TestCase):
    def test_orbit_sizes(self):
        for n in range(1,5):
            counts={}
            for f in a.forests(tuple(range(n))):
                k=tuple(sorted(map(shape,f)));counts[k]=counts.get(k,0)+1
            self.assertEqual(set(counts),set(s.forests(n)))
            self.assertEqual(counts,{f:s.orbit_size(f) for f in s.forests(n)})
    def test_exact_intertwining(self):
        states,ids,q,r=s.build(4)
        for f in a.forests(tuple(range(4))):
            k=len(f);outq={ids[tuple(sorted(map(shape,f)))]:F(-s.comb(k,2))};outr={ids[tuple(sorted(map(shape,f)))]:F(2*s.comb(k,3))}
            def add(d,ff,c):
                j=ids[tuple(sorted(map(shape,ff)))];d[j]=d.get(j,F(0))+c
            for i,j in combinations(range(k),2):
                ff=[a.tree(f[i],f[j])]+[f[h] for h in range(k) if h not in (i,j)];add(outq,ff,F(1));add(outr,ff,F(-(k-2)))
            for i,j,l in combinations(range(k),3):
                rest=[f[h] for h in range(k) if h not in (i,j,l)]
                for x,y,z in ((i,j,l),(i,l,j),(j,l,i)):add(outr,[a.tree(a.tree(f[x],f[y]),f[z])]+rest,F(1,3))
            row=ids[tuple(sorted(map(shape,f)))];self.assertEqual({j:v for j,v in outq.items() if v},q[row]);self.assertEqual({j:v for j,v in outr.items() if v},r[row])
    def test_projectors(self):
        states,ids,q,r=s.build(4);e=[F(0)]*len(states);e[ids[('x',)*4]]=F(1)
        parts=[s.project(e,j,q,4) for j in range(1,5)];self.assertEqual([sum(x) for x in zip(*parts)],e)
        for j,v in enumerate(parts,1):self.assertEqual(s.apply(v,q),[-s.comb(j,2)*x for x in v])
    def test_relation(self):
        self.assertEqual(s.relation([[F(1),F(0)],[F(0),F(2)]],[F(3),F(4)]),[F(3),F(2)])
        self.assertIsNone(s.relation([[F(1),F(0)]],[F(0),F(1)]))
if __name__=='__main__':unittest.main()
