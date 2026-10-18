"""Exact scalar consequences of the accepted full-forest quartet cocycle.
No numerical or unranked-forest simulation; all checks use rational arithmetic.
"""
from fractions import Fraction as F
from math import comb

def cell(x,p):
    q=1-p
    h3=1-F(3,2)*x+F(1,2)*x**3
    # Enumerate four-root routing classes: all-on-one-arm contributes zero;
    # 3+1 contributes -h3/3; 2+2 contributes 2(1-x)^2/3.
    contrast=F(0)
    for j in range(5):
        weight=comb(4,j)*p**j*q**(4-j)
        deviation=F(0) if j in (0,4) else (-h3/3 if j in (1,3) else F(2,3)*(1-x)**2)
        contrast+=weight*deviation
    b4=sum(F(comb(4,j))*p**j*q**(4-j)*x**(j*(j-1)//2+(4-j)*(3-j)//2) for j in range(5))
    return b4,contrast

def compose(a,b):
    ca,ta=a; cb,tb=b
    return ca*cb,ta+ca*tb

A=cell(F(9,10),F(1,2));B=cell(F(1,2),F(1,4))
assert A==(F(5877441,8000000),F(1,12000))
assert B==(F(953,8192),-F(7,512))
z6=-A[1]/(A[0]*B[1]);assert 0<z6<1
# E(u) has quartet diagonal u^6 and completed-quartet contrast zero.
E=(F(1,64),F(0));Z=(z6,F(0))
def product(seq):
    out=(F(1),F(0))
    for a in seq:out=compose(out,a)
    return out
W=product([E,A,Z,B,E]);V=product([E,B,Z,A,E]);pal=compose(W,V)
assert W[1]==0 and W[0]==V[0] and V[1]<0 and pal[1]<0
assert z6==F(1024000,123426261)
assert pal[1]==-F(2470115230049,66794081062282592256000)
# Swapping equal-arm parent names is immaterial, if included in reversal.
assert cell(F(1,2),F(3,4))==B
for name,value in [('A (b4,T)',A),('B (b4,T)',B),('middle z^6',z6),('W (b4,T)',W),('reverse (b4,T)',V),('palindrome (b4,T)',pal)]:
    print(name, value)
print('PASS: all parameters strict; forward quartet contrast zero; reversal and palindrome negative.')
print('No-merger diagonals at every arity agree under reversal by scalar product commutativity, proved in the accompanying note.')
print('Scope: failure of this symmetrization operation, not a full G4 counterexample or finite forcing theorem.')
