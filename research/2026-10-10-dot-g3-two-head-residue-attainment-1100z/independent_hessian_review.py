from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parent
L=(1,3,6,10,15,21,28)
def rowdata(q):
 z=[q**l for l in L]
 return ([2*(1-a)/(1+a) for a in z], [l*a/(1+a) for l,a in zip(L,z)], [4*(1-a)**2/(1+a)**2 for a in z], [4*l*a/(1+a)**2 for l,a in zip(L,z)], [-l*l*a/(1+a)**2 for l,a in zip(L,z)])
d1,d2=rowdata(F(1,2)),rowdata(F(1,3))
M=[[F(a) for a in L],list(d1[0]),list(d1[1]),list(d2[0]),list(d2[1])]
# Independent rational Gauss-Jordan; no SymPy or companion basis import.
A=[r[:] for r in M];piv=[];rr=0
for col in range(7):
 k=next((i for i in range(rr,5) if A[i][col]),None)
 if k is None: continue
 A[rr],A[k]=A[k],A[rr]
 z=A[rr][col];A[rr]=[v/z for v in A[rr]]
 for i in range(5):
  if i!=rr:
   z=A[i][col];A[i]=[u-z*v for u,v in zip(A[i],A[rr])]
 piv.append(col);rr+=1
 if rr==5:break
free=[j for j in range(7) if j not in piv]
assert len(piv)==5 and free==[5,6]
basis=[]
for j in free:
 c=[F(0)]*7;c[j]=F(1)
 for i,col in enumerate(piv):c[col]=-A[i][j]
 assert all(sum(a*b for a,b in zip(r,c))==0 for r in M)
 basis.append(c)
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
h=[tuple(dot(c,v) for v in d2[2:]) for c in basis]
x,y=h
cross=(x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0])
a,b=cross[0]/cross[2],cross[1]/cross[2]
assert a>F(3,2) and -F(3,2)<b<0
assert all(a*xx+b*xy+yy==0 for xx,xy,yy in h)
assert cross[2]!=0
cert=(root/'compact-certificate.txt').read_text().splitlines()
assert a==F(cert[0].split('=',1)[1]) and b==F(cert[1].split('=',1)[1])
print('PASS: independent Fraction elimination rank5, free columns5/6, identical exact alpha/beta.')
print('PASS: alpha>3/2, -3/2<beta<0; dual matrix positive definite (det>15/16).')
print('PASS: Hessian map injective; every nonzero stationary normal has indefinite head Hessian.')
