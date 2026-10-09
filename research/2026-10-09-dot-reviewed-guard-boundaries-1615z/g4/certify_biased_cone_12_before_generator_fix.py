"""Exact integer-enclosure certificate. mpmath proposes inverse/weights only.
Every acceptance test below uses integers/Fractions and an explicit log series bound.
No general arity claim and no source-word mixture realization claim.
"""
from fractions import Fraction as Q
from math import comb
import mpmath as mp,json
mp.mp.dps=150
S=10**100; B=10**60; N=120
nodes=[('17/40','1/40'),('17/40','1/8'),('17/40','11/40'),('19/40','1/40'),('19/40','9/40'),('21/40','11/40'),('5/8','1/40'),('5/8','19/40'),('27/40','1/40'),('29/40','1/40'),('31/40','1/40')]
def ceil(a,b):return -((-a)//b)
def log_unit(y):
 assert 1<=y<=2
 z=(y-1)/(y+1);zl=(S*z.numerator)//z.denominator;zu=ceil(S*z.numerator,z.denominator)
 lo,hi=zl,zu;z2l=zl*zl//S;z2u=ceil(zu*zu,S);sl=su=0
 for j in range(N):
  sl+=lo//(2*j+1);su+=ceil(hi,2*j+1)
  lo=lo*z2l//S;hi=ceil(hi*z2u,S)
 rem=ceil(9*S,4*(2*N+1)*3**(2*N+1))
 return 2*sl,2*su+rem
L2=log_unit(Q(2))
def log_bound(x):
 assert x>=1
 k=x.numerator.bit_length()-x.denominator.bit_length()
 while Q(2)**k>x:k-=1
 while Q(2)**(k+1)<=x:k+=1
 l,u=log_unit(x/(Q(2)**k));return l+k*L2[0],u+k*L2[1]
def R(q,g,n):return sum(Q(comb(n,j))*g**j*(1-g)**(n-j)*q**(-j*(n-j)) for j in range(n+1))
A=[[log_bound(R(Q(q),Q(g),n)) for q,g in nodes] for n in range(2,13)]
b=[log_bound(R(Q(1,2),Q(1,4),n)) for n in range(2,13)]
M=mp.matrix([[mp.mpf(l+u)/(2*S) for l,u in row] for row in A]);v=mp.matrix([mp.mpf(l+u)/(2*S) for l,u in b]);inv=M**-1;w=inv*v
Bi=[[int(mp.nint(inv[i,j]*B)) for j in range(11)] for i in range(11)];wi=[int(mp.nint(x*B)) for x in w]
def scale(k,iv):
 l,u=iv;return (k*l,k*u) if k>=0 else (k*u,k*l)
def add(ivs):return sum(x[0] for x in ivs),sum(x[1] for x in ivs)
# BA has denominator B*S; ||I-BA|| infinity < 1.
delta_num=0
for i in range(11):
 rownorm=0
 for j in range(11):
  l,u=add(scale(Bi[i][k],A[k][j]) for k in range(11));d=B*S if i==j else 0
  rownorm+=max(abs(d-l),abs(d-u))
 delta_num=max(delta_num,rownorm)
assert delta_num<B*S
# Original residual b-A*w0 denominator S*B.
res=[]
for i in range(11):
 l,u=add(scale(wi[j],A[i][j]) for j in range(11));res.append((B*b[i][0]-u,B*b[i][1]-l))
# Preconditioned residual Bapprox*(b-A*w0) denominator S*B^2.
rnum=max(max(map(abs,add(scale(Bi[i][j],res[j]) for j in range(11)))) for i in range(11))
err=Q(rnum,S*B*B)/(1-Q(delta_num,S*B)); minw=Q(min(wi),B)
assert 0<minw and err<minw
out={'status':'PASS exact integer enclosures','arity':'2 through 12','target':{'q':'1/2','g':'1/4'},'nodes':nodes,'rational_clock_domain':'2/5 < q < 1','log_bound':'range reduction by powers of 2; 120 atanh terms; tail <= 9/[4(241)3^241]','preconditioner_residual_norm_bound':str(Q(delta_num,S*B)),'solution_error_infinity_bound':str(err),'smallest_proposed_weight':str(minw),'approximate_weights':[mp.nstr(x,30) for x in w],'limitations':'Conic representation of eleven log diagonal coordinates only. Positive real weights are not literal source multiplicities or a source mixture operation. No statement for higher arities, nonlinear guards, or full forests.'}
print(json.dumps(out,indent=2))
