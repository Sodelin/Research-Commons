#!/usr/bin/env python3
"""Source-labelled algebra integration checks; no new graph census."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from regular_action import ForestAlgebra,matrix,full_cell,full_cell_polynomials,structural_regular_certificate

ROOT=Path(__file__).resolve().parent
def main():
    identity=json.loads((ROOT/'UPSTREAM-IDENTITY.json').read_bytes())
    for record in identity['files']:assert hashlib.sha256((ROOT/'upstream'/record['path']).read_bytes()).hexdigest()==record['sha256']
    alg=ForestAlgebra(4);structure=structural_regular_certificate(alg);assert alg.dim==48
    cases=[]
    for mode in ('common','independent'):
        args=(Q(2,3),Q(1,2),Q(3,5),Q(2,7),Q(4,5));kernel=full_cell(alg,*args,mode)
        polys=full_cell_polynomials(alg,mode);evaluated=alg.evaluate(polys,args);assert kernel==evaluated
        action=matrix(alg,kernel)
        image=tuple(sum(action[i][j]*alg.unit[j] for j in range(alg.dim)) for i in range(alg.dim));assert image==kernel
        assert alg.mul(kernel,alg.unit)==kernel and alg.mul(alg.unit,kernel)==kernel
        scalars=[]
        for r in range(5):
            no_merge=kernel[alg.index[r,tuple(range(r))]];assert no_merge>0
            z,x,y,g,a=args
            if mode=='common':expected=z**(r*(r-1)//2)*a**(r*(r-1)//2)*(g*x**(r*(r-1)//2)+(1-g)*y**(r*(r-1)//2))
            else:
                from math import comb
                expected=z**(r*(r-1)//2)*a**(r*(r-1)//2)*sum(Q(comb(r,k))*g**k*(1-g)**(r-k)*x**(k*(k-1)//2)*y**((r-k)*(r-k-1)//2) for k in range(r+1))
            assert no_merge==expected
            scalars.append(str(no_merge))
            indices=[i for i,(k,f) in enumerate(alg.coords) if k==r]
            for i in indices:
                for j in indices:assert action[i][j]==(no_merge if i==j else 0)
        cases.append({'mode':mode,'parameters':[str(v) for v in args],'positive_diagonal_scalars':scalars,
                      'polynomial_family_equals_actual_cell':True,'faithful_unit_image_equals_FULL_family':True})
    out={'status':'PASS_EXISTING_SOURCE_FOREST_ALGEBRA_REGULAR_INTEGRATION','structure':structure,'physical_cell_cases':cases,
         'source_constructor_expanded':False,'complete_core_catalogue_implemented':False,
         'global_G3_certificate_from_this_algebra_alone_claimed':False,
         'equality_testing_bound_is_NOT_positive_realization_bound':True}
    (ROOT/'REGULAR-ACTION-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('physical_cell_cases','structure')},indent=2))

if __name__=='__main__':main()
