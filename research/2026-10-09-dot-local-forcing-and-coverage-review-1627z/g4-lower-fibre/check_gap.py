from math import comb
pairs = [(r,s) for r in range(1,10) for s in range(1,r)
         if comb(r,2)-comb(s,2)==30]
assert pairs == [(9,4)]
print('Exact cap-nine ordinary spectral-gap check:', pairs)
