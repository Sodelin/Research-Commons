import unittest,tempfile
from pathlib import Path
from fractions import Fraction as F
import check_weight30 as x
class TinyQuotientPreparation(unittest.TestCase):
    def test_ordinary_truncation(self):
        full,ids,q,r=x.m.build(3);z=x.Quotient(3,2)
        for mat,old in ((z.q,q),(z.r,r)):
            for i,f in enumerate(z.states):
                expected={z.ids[full[j]]:v for j,v in old[ids[f]].items() if full[j] in z.ids}
                self.assertEqual(mat[i],expected)
    def test_split_forget(self):
        z=x.Quotient(3,2)
        for i in range(len(z.states)):
            row=[F(k==i) for k in range(len(z.states))];col=x.c.split(row,z.states,z.cids);out=[F(0)]*len(row)
            for v,(a,b) in zip(col,z.colours):out[z.ids[tuple(sorted(a+b))]]+=v
            self.assertEqual(row,out)
    def test_projectors(self):
        z=x.Quotient(3,2)
        total=[F(0)]*len(z.states)
        for j in (2,3):
            p=z.project(z.e,j);self.assertEqual(z.project(p,j),p);total=[a+b for a,b in zip(total,p)]
        self.assertEqual(total,z.e)
    def test_small_normalization(self):
        z=x.Quotient(2,1)
        for name in ('R','B4','A5','D5'):self.assertFalse(any(z.actor(name,z.e)))
    def test_guard_solve_orientation(self):
        matrix=[[F(1),F(2),F(0)],[F(0),F(1),F(3)],[F(0),F(0),F(2)]]
        w=x.m.relation(matrix,[F(0),F(1),F(1)])
        self.assertEqual([sum(c*r[k] for c,r in zip(w,matrix)) for k in range(3)],[F(0),F(1),F(1)])
    def test_hash_and_bounds(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'bad.py';p.write_text('raise RuntimeError("must not run")')
            with self.assertRaisesRegex(ValueError,'helper hash'):x.load(p,'0'*64,'bad')
        for n,j in ((13,9),(9,0),(9,10)):
            with self.assertRaises(ValueError):x.Quotient(n,j)
if __name__=='__main__':unittest.main()
