import unittest,tempfile
from pathlib import Path
from fractions import Fraction as F
import check_source_premises as x
class TinyPreparation(unittest.TestCase):
    def test_kappa(self):
        self.assertEqual(x.kappa(3,0,1),3);self.assertEqual(x.kappa(1,1,1),-1)
    def test_small_normalization(self):
        for n in (0,1,2):
            c=x.Context(n)
            for name in ('R','B4','A5','B5'):self.assertFalse(any(c.actor(name,c.e)))
    def test_commutator_sign(self):
        c=x.Context(2);v=[F(1),F(0)]
        # Direct row orientation, independent of whether this small R vanishes.
        for name in ('R','B4'):
            expected=[a-b for a,b in zip(c.actor(name,x.m.apply(v,c.q)),x.m.apply(c.actor(name,v),c.q))]
            self.assertEqual(c.ad(name,1,v),expected)
    def test_positive_binomial(self):self.assertEqual(x.positive_binomial([F(1)],[{0:F(3)}],2),[F(3)])
    def test_determinant(self):
        self.assertEqual(x.determinant([[F(1),F(2)],[F(3),F(4)]]),F(-2))
        self.assertEqual(x.determinant([[F(0),F(1)],[F(2),F(0)]]),F(-2))
        self.assertEqual(x.determinant([[F(1),F(2)],[F(2),F(4)]]),0)
    def test_basis_selection(self):
        self.assertEqual(x.independent_indices([[F(0),F(0)],[F(1),F(2)],[F(2),F(4)],[F(0),F(1)]]),[1,3])
    def test_hash_rejection(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'bad.py';p.write_text('raise RuntimeError("must not run")')
            with self.assertRaisesRegex(ValueError,'provider hash'):x.load(p,'0'*64,'bad')
    def test_bounds(self):
        for n in (-1,11):
            with self.assertRaises(ValueError):x.Context(n)
if __name__=='__main__':unittest.main()
