import unittest
from fractions import Fraction as F
import derive_fifth as d
class Tests(unittest.TestCase):
 def test_one_root(self):
  ctx=d.h.Quotient(1,1);self.assertEqual(d.source(ctx,5),{(0,0,0):ctx.e})
 def test_pair_full(self):
  ctx=d.h.Quotient(2,1);self.assertEqual(d.source(ctx,5),{(0,0,0):ctx.e})
 def test_cubic_full(self):
  ctx=d.h.Quotient(3,1);C=d.source(ctx,3);expected={(0,0,0):ctx.e}
  for (r,z),v in d.ETA.items():d.addrow(expected,(3,r,z),d.m.apply(ctx.e,ctx.r),v)
  self.assertEqual(C,expected)
 def test_z_small(self):
  for n in (1,2,3):self.assertTrue(all(not row for row in d.z_operator(d.h.Quotient(n,1))))
 def test_z_complete_four(self):
  ctx=d.h.Quotient(4,1);row=d.m.apply(ctx.e,d.z_operator(ctx))
  expected={('((xx)x)','x'):F(-6),('(xx)','(xx)'):F(18),('(((xx)x)x)',):F(1),('((xx)(xx))',):F(2)}
  actual={f:v/d.m.orbit_size(f) for f,v in zip(ctx.states,row) if v}
  self.assertEqual(actual,expected);self.assertEqual(sum(row),0)
 def test_t_pair(self):
  ctx=d.h.Quotient(2,1);self.assertTrue(all(not x for x in d.lower_rows(ctx)['T']))
 def test_commutator_small(self):
  ctx=d.h.Quotient(3,1);L=d.lower_rows(ctx)
  for name in ('adR','ad2R','adZ'):self.assertTrue(all(not x for x in L[name]))
 def test_exact_relations(self):
  a=[[F(1),F(2),F(3)],[F(0),F(1),F(1)]];v=[F(2),F(7),F(9)]
  self.assertEqual(d.m.relation(a,v),[F(2),F(3)])
if __name__=='__main__':unittest.main()
