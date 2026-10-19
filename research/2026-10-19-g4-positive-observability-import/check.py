from fractions import Fraction as F
from itertools import product
from math import prod
alpha, delta, eta = F(1,3), F(1,2), F(1,4)
for L in range(1,5):
    states=list(product((-1,1),repeat=L)); D=len(states)
    P=[[alpha/D+(1-alpha)*(F(1,2)*(1+delta*prod(x)*z[-1]) if z[:-1]==x[1:] else 0) for z in states] for x in states]
    assert all(v>0 for row in P for v in row)
    assert all(sum(row)==1 for row in P)
    assert all(sum(P[i][j] for i in range(D))==1 for j in range(D))
    def probability(word):
        v=[F(1,D)*(1-eta if x[-1]==word[0] else eta) for x in states]
        for b in word[1:]:
            v=[sum(v[i]*P[i][j] for i in range(D))*(1-eta if states[j][-1]==b else eta) for j in range(D)]
        return sum(v)
    for n in range(1,L+2):
        for word in product((-1,1),repeat=n):
            expected=F(1,2**n)
            if n==L+1: expected*=1+(1-alpha)**L*delta*(1-2*eta)**(L+1)*prod(word)
            assert probability(word)==expected,(L,word,probability(word),expected)
    print('PASS L=',L,'states=',D,'first correlation=',(1-alpha)**L*delta*(1-2*eta)**(L+1))
print('Exact rational controls only; all-L proof is in the companion note. No forest-source admission asserted.')
