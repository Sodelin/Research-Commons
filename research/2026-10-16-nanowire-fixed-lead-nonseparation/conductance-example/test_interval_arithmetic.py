"""Deterministic exact-rational controls for the interval kernel. No external packages."""
import unittest
from fractions import Fraction as F
from dyadic_interval import I,C,D,mm,inverse,determinant
from verify_finite_pair import check_particle_hole

def contains(x,q):return x.lower()<=q<=x.upper()
def cc(x,y):return (F(x),F(y))
def ca(a,b):return(a[0]+b[0],a[1]+b[1])
def cn(a):return(-a[0],-a[1])
def cm(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def ci(a):
 d=a[0]*a[0]+a[1]*a[1];return(a[0]/d,-a[1]/d)
def contains_c(z,q):return contains(z.r,q[0]) and contains(z.i,q[1])

class Controls(unittest.TestCase):
 def test_rational_conversion(self):
  for a in range(-31,32):
   for b in range(1,20):self.assertTrue(contains(I(F(a,b)),F(a,b)))
 def test_scalar_operations(self):
  for k in range(1,201):
   a=F((37*k)%101-50,k+1);b=F((53*k)%97-48,k+3)
   self.assertTrue(contains(I(a)+I(b),a+b))
   self.assertTrue(contains(I(a)*I(b),a*b))
   self.assertTrue(contains(I(a)-I(b),a-b))
   if b:self.assertTrue(contains(I(a)/I(b),a/b))
 def test_rectangle_endpoints(self):
  a,b=I(F(-2,3),F(7,11)),I(F(-9,5),F(3,7))
  for x in [F(-2,3),0,F(7,11)]:
   for y in [F(-9,5),0,F(3,7)]:self.assertTrue(contains(a*b,x*y))
 def test_negative_reciprocal(self):
  z=I(-3,-2).inv();self.assertTrue(contains(z,F(-1,2)));self.assertTrue(contains(z,F(-1,3)))
 def test_square_straddling_zero(self):
  z=I(-3,2).square();self.assertEqual(z.lower(),0);self.assertEqual(z.upper(),9)
 def test_zero_divisor_rejected(self):
  for a in [I(0),I(-1,1),I(0,1)]:
   with self.assertRaises(AssertionError):a.inv()
 def test_complex_zero_rejected(self):
  with self.assertRaises(AssertionError):C(I(-1,1),I(-1,1)).inv()
 def test_complex_operations(self):
  for k in range(1,101):
   a=cc(F(k-45,k+1),F(2,k+3));b=cc(F(3,k+2),F(k-23,k+4))
   z,w=C(*a),C(*b)
   self.assertTrue(contains_c(z*w,cm(a,b)))
   self.assertTrue(contains_c(z/w,cm(a,ci(b))))
 def test_complex_inverse_2x2(self):
  a,b,c,d=cc(3,1),cc(F(1,3),0),cc(0,F(-1,2)),cc(4,-2)
  den=ca(cm(a,d),cn(cm(b,c)))
  target=[[cm(d,ci(den)),cm(cn(b),ci(den))],[cm(cn(c),ci(den)),cm(a,ci(den))]]
  got=inverse([[C(*a),C(*b)],[C(*c),C(*d)]])
  for i in range(2):
   for j in range(2):self.assertTrue(contains_c(got[i][j],target[i][j]))
  self.assertTrue(contains_c(determinant([[C(*a),C(*b)],[C(*c),C(*d)]]),den))
 def test_singular_matrix_rejected(self):
  with self.assertRaises(AssertionError):inverse([[C(1),C(2)],[C(2),C(4)]])
 def test_four_by_four_diagonal(self):
  ds=[cc(1,1),cc(2,-1),cc(3,2),cc(4,-3)]
  A=[[C(*ds[i]) if i==j else C() for j in range(4)] for i in range(4)]
  got=inverse(A)
  for i in range(4):
   for j in range(4):self.assertTrue(contains_c(got[i][j],ci(ds[i]) if i==j else cc(0,0)))
  prod=cc(1,0)
  for d in ds:prod=cm(prod,d)
  self.assertTrue(contains_c(determinant(A),prod))
 def test_dual_derivative(self):
  a=D(F(3,2),1);z=a*a+a.inv()
  self.assertTrue(contains(z.v,F(9,4)+F(2,3)))
  self.assertTrue(contains(z.d,F(3)-F(4,9)))
 def test_particle_hole_basis(self):check_particle_hole()

if __name__=='__main__':unittest.main(verbosity=2)
