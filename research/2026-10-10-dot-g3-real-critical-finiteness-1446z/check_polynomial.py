from fractions import Fraction as F
# Pure standard-library coefficient arithmetic. No analytic theorem is executed.
def add(a,b):
 z=[F(0)]*max(len(a),len(b))
 for i,x in enumerate(a):z[i]+=x
 for i,x in enumerate(b):z[i]+=x
 while len(z)>1 and not z[-1]:z.pop()
 return z
def neg(a):return [-x for x in a]
def mul(a,b):
 z=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return add(z,[])
def deriv(a):return [i*a[i] for i in range(1,len(a))]
def T(n):return list(map(F,range(n-1,0,-1)))
for n in (3,6,10,15,21):
 R=[F(1)]*n
 lhs=add([F(n)],neg(R))
 assert lhs==mul([F(1),F(-1)],T(n))
print('PASS n-R_n=(1-r)T_n for every nontrivial observed exponent')
assert T(3)==[2,1] and T(6)==[5,4,3,2,1]
print('PASS exact T3 and T6 coefficient arrays')
W=add(mul(deriv(T(6)),T(3)),neg(mul(T(6),deriv(T(3)))))
assert W==[3,12,15,12,3] and all(x>0 for x in W)
print('PASS derivative numerator of T6/T3 is strictly positive on (0,1)')
assert add([1,1,1],[-3])==neg(mul([1,-1],T(3)))
print('PASS two-coordinate drift/residue determinant is nonzero on (0,1)')
print('SCOPE polynomial identities only; no normalization, divisor, critical census or QE replay')
