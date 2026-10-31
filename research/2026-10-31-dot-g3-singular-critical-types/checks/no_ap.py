import itertools, json
exponents=[1,3,6,10,15,21]
triples=[{'a':a,'k':k,'b':b,'a_plus_b_minus_2k':a+b-2*k}
         for a,k,b in itertools.combinations(exponents,3)]
assert len(triples)==20
assert all(t['a_plus_b_minus_2k']!=0 for t in triples)
assert ((2*len(exponents)-3)*sum(exponents)-len(exponents)+1)==499
print(json.dumps({'exponents':exponents,'triples':triples,'type_bound':499},indent=2))
