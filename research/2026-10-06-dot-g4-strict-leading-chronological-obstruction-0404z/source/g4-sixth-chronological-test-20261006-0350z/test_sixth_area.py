import unittest
from fractions import Fraction as F
import check_sixth_area as c
class Tests(unittest.TestCase):
 def test_membership(self):
  x=c.decide([[F(1),F(0)],[F(0),F(1)]],[F(2),F(3)])
  self.assertEqual(x['decision'],'AREA_TEST_FAILS_MEMBERSHIP');self.assertEqual(x['membership_coefficients'],['2','3'])
 def test_nonmembership(self):
  x=c.decide([[F(1),F(0)]],[F(0),F(1)]);self.assertEqual(x['decision'],'DIRECT_SOURCE_ANNIHILATOR_FOUND');self.assertEqual(x['covector'],['0','1'])
 def test_empty_span(self):
  self.assertEqual(c.decide([], [F(0)])['membership_coefficients'],[])
  self.assertEqual(c.decide([], [F(2)])['covector'],['1/2'])
 def test_dependent(self):
  x=c.decide([[F(1),F(2)],[F(2),F(4)]],[F(3),F(6)]);self.assertEqual(x['span_rank'],1)
 def test_eta_square(self):
  p=c.product_poly(c.ETA,c.ETA)
  rho,z=F(1,4),F(3,8)
  self.assertEqual(sum(v*rho**r*z**q for (r,q),v in p.items()),0)
 def test_projected_pair(self):
  ctx=c.h.Quotient(2,1);self.assertEqual(c.c.coefficients(ctx,[(2,1,('(xx)',),1,1)],6),[{}])
 def test_area_identity(self):
  x=[F(1),F(-2),F(1)];p=[F(3),F(2),F(1)]
  half=sum(x[i]*x[j]*(p[i]-p[j])/2 for i in range(3) for j in range(i+1,3))
  integral=sum((sum(x[:i+1]))**2*(p[i]-p[i+1]) for i in range(2))
  self.assertEqual(half,-integral/2);self.assertLess(half,0)
if __name__=='__main__':unittest.main()
