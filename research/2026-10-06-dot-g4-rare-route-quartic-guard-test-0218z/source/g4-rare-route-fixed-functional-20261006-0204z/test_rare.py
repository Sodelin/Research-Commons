import unittest
from fractions import Fraction as F
from unittest.mock import patch
import check_rare as c
class Tests(unittest.TestCase):
 def test_pair(self):
  p=c.pair_series(2)
  self.assertEqual(p,{(0,0,0):F(1),(1,0,1):F(-1),(2,0,2):F(1,2),(2,0,1):F(2),(2,1,0):F(1),(2,0,0):F(-1)})
 def test_inverse(self):
  for k in (1,6,15):
   p={(0,0,0):F(1)}
   for _ in range(k):p=c.mul(p,c.pair_series(5))
   self.assertEqual(c.mul(p,c.inverse_pair(k,5)),{(0,0,0):F(1)})
 def test_split_occurrences(self):
  ctx=c.h.Quotient(2,1);v=ctx.e;rows=c.split_coeffs(ctx,v,2)
  self.assertEqual([sum(r) for r in rows],[F(1),F(0),F(0)])
  self.assertEqual(rows[1][ctx.cids[(('x',),('x',))]],2)
 def test_rare_project(self):
  ctx=c.h.Quotient(2,1);rows=c.split_coeffs(ctx,ctx.e,2)
  for row in rows:
   pieces=[c.rare_project(row,ctx.ql,r,(0,1)) for r in (0,1)]
   self.assertEqual([sum(x) for x in zip(*pieces)],row)
 def test_pair_diagonal(self):
  ctx=c.h.Quotient(2,2)
  self.assertEqual(c.coefficients(ctx,[(2,2,('x','x'),1,1)],5),[{(0,0,0):F(1)}])
 def test_pair_offdiagonal(self):
  ctx=c.h.Quotient(2,1)
  self.assertEqual(c.coefficients(ctx,[(2,1,('(xx)',),1,1)],5),[{}])
 def test_first_failure(self):
  with patch.object(c,'run_degree',return_value=({(4,0,0):F(1)},[])) as f:
   result=c.run();self.assertFalse(result['stage5_executed']);self.assertEqual(f.call_args_list,[((4,),)])
 def test_second_stage(self):
  with patch.object(c,'run_degree',side_effect=[({},[]),({(5,1,0):F(1)},[])]) as f:
   result=c.run();self.assertTrue(result['stage5_executed']);self.assertFalse(result['sign_theorem_claimed']);self.assertEqual(f.call_count,2)
if __name__=='__main__':unittest.main()
