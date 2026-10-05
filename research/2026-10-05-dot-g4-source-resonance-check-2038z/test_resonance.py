import unittest
from fractions import Fraction as F
import resonance as s
class Small(unittest.TestCase):
    def test_bounds(self):
        with self.assertRaises(ValueError):s.build(5,9)
    def test_projectors(self):
        states,index,q,r=s.build(2,4)
        for i in range(len(states)):
            e=[F(0)]*len(states);e[i]=F(1);parts=[s.projector(e,j,q,4) for j in range(1,5)]
            self.assertEqual([sum(z) for z in zip(*parts)],e)
            for j,p in enumerate(parts,1):
                self.assertEqual(s.apply(p,q),[-s.comb(j,2)*x for x in p]);self.assertEqual(s.projector(p,j,q,4),p)
    def test_marked_marginal(self):
        states,index,q,r=s.build(2,4)
        # R3 has zero two-marked restriction; Q merges that marked pair at rate1.
        for i,(f,n) in enumerate(states):
            pair=sum(v for j,v in r[i].items() if len(states[j][0])==1)
            if len(f)==2:self.assertEqual(pair,0)
            merge=sum(v for j,v in q[i].items() if len(states[j][0])==1)
            if len(f)==2:self.assertEqual(merge,1)
    def test_rank(self):
        self.assertEqual(s.rank([[F(1),F(2)],[F(2),F(4)]]),1)
if __name__=='__main__':unittest.main()
