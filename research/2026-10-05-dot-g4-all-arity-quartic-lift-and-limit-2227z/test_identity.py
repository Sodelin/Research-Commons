import unittest,tempfile
from pathlib import Path
from fractions import Fraction as F
import check_identity as x
class TinyPreparation(unittest.TestCase):
    def test_kappa(self):
        self.assertEqual(x.kappa(3,0,1),3)
        self.assertEqual(x.kappa(2,1,1),-1)
        self.assertEqual(x.kappa(1,1,1),-1)
        self.assertEqual(x.kappa(2,2,0),1)
    def test_positive_binomial(self):
        q=[{0:F(3)}]
        self.assertEqual(x.positive_binomial([F(1)],q,2),[F(3)])
        self.assertEqual(x.positive_binomial([F(1)],q,4),[F(0)])
    def test_small_pair_normalization(self):
        for n in (0,1,2):
            r=x.check_arity(n)
            self.assertTrue(r['identity_holds'])
            self.assertTrue(all(F(v)==0 for v in r['H40']+r['H41']))
    def test_split_forget(self):
        for n in (1,2):
            states,ids,_,_=x.m.build(n);colours,ci,_,_=x.c.coloured(n)
            for k in range(len(states)):
                row=[F(i==k) for i in range(len(states))]
                self.assertEqual(x.forget(x.c.split(row,states,ci),colours,ids),row)
    def test_hash_rejection(self):
        with tempfile.TemporaryDirectory() as td:
            p=Path(td)/'bad.py';p.write_text('raise RuntimeError("must not execute")')
            with self.assertRaisesRegex(ValueError,'provider hash'):x.authenticated_module(p,'0'*64,'bad')
    def test_range_rejection(self):
        for n in (-1,9):
            with self.assertRaises(ValueError):x.check_arity(n)
if __name__=='__main__':unittest.main()
