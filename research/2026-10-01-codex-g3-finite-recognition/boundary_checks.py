from fractions import Fraction as F
import json

def solve_square(a,b):
    a=[list(row)+[rhs] for row,rhs in zip(a,b)]
    n=len(a)
    for col in range(n):
        pivot=next(i for i in range(col,n) if a[i][col])
        a[col],a[pivot]=a[pivot],a[col]
        z=a[col][col]
        a[col]=[v/z for v in a[col]]
        for i in range(n):
            if i!=col:
                z=a[i][col]
                a[i]=[u-z*v for u,v in zip(a[i],a[col])]
    return [row[-1] for row in a]

def evaluate(poly,x):
    return sum(c*x**i for i,c in enumerate(poly))

def multiply(a,b):
    p=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            p[i+j]+=x*y
    return p

def divide(a,b):
    a=a[:]
    q=[F(0)]*(len(a)-len(b)+1)
    for j in range(len(q)-1,-1,-1):
        q[j]=a[j+len(b)-1]/b[-1]
        for k,c in enumerate(b):
            a[j+k]-=q[j]*c
    assert all(c==0 for c in a)
    return q

def expose(atoms):
    powers=[0,1,3,6,10,15,21]
    matrix=[]
    rhs=[]
    for x in atoms:
        matrix.append([x**k for k in powers[1:]])
        rhs.append(F(-1))
        matrix.append([k*x**(k-1) for k in powers[1:]])
        rhs.append(F(0))
    coefficients=[F(1)]+solve_square(matrix,rhs)
    p=[F(0)]*22
    for k,c in zip(powers,coefficients):
        p[k]=c
    dp=[(k+1)*p[k+1] for k in range(21)]
    for x in atoms:
        assert evaluate(p,x)==evaluate(dp,x)==0
    factor=[F(1)]
    for x in atoms:
        factor=multiply(factor,[x*x,-2*x,F(1)])
    remainder=divide(p,factor)
    assert all(c>0 for c in remainder)
    # P is nonnegative on [0,1], vanishing only at these interior atoms.
    return coefficients,remainder

def main():
    atoms=[F(1,4),F(1,2),F(3,4)]
    coeffs,remainder=expose(atoms)
    powers=[0,1,3,6,10,15,21]
    moments=[sum(x**k for x in atoms)/3 for k in powers]
    assert sum(c*m for c,m in zip(coeffs,moments))==0
    assert atoms[1]**2 != atoms[0]*atoms[2]
    geometric=[F(1,8),F(1,4),F(1,2)]
    coeffs_g,remainder_g=expose(geometric)
    weights=[F(1,4),F(1,2),F(1,4)]
    moments_g=[sum(w*x**k for w,x in zip(weights,geometric)) for k in powers]
    assert sum(c*m for c,m in zip(coeffs_g,moments_g))==0
    assert geometric[1]**2 == geometric[0]*geometric[2]
    distribution={F(1,2):F(1)}
    for _ in range(2):
        out={}
        for x,w in distribution.items():
            for z in [x,x/2]:
                out[z]=out.get(z,F(0))+w/2
        distribution=out
    assert [distribution[x] for x in geometric]==weights
    print(json.dumps({
      'status':'passed',
      'exact_exposing_polynomials':2,
      'positive_quotient_coefficients':[len(remainder),len(remainder_g)],
      'nongem_boundary_rejection':True,
      'geometric_boundary_attainment':True,
      'scope':'common typed cap-seven boundary; not all-input recognition'
    },indent=2))

if __name__=='__main__':
    main()
