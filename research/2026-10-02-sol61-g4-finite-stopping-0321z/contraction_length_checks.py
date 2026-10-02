#!/usr/bin/env python3
"""Exact bounded controls for data-derived unknown-length contraction budgets."""
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
import json,sys
import tomography_check as T

def run():
    rows=[]
    for q in (Q(1,2),Q(4,5)):
        rho=(1+q)/2
        for length in range(0,7):
            start=('A1','A2');dist=T.edge(start,Q(2,3));p=Q(2,3)
            for i in range(1,length+1):
                x=q*Q(i+1,i+2);y=q*Q(1,2);g=Q(i,i+2)
                beta=g*g*x+(1-g)**2*y+2*g*(1-g)
                assert beta==1-g*g*(1-x)-(1-g)**2*(1-y)
                assert 0<beta<=rho<1
                dist=T.push(dist,lambda f:T.bigon(f,x,y,g))
                dist=T.push(dist,lambda f:T.edge(f,Q(3,4)))
                p*=beta*Q(3,4)
            assert dist[start]==p>0 and p<=rho**length
            b=1
            while rho**b>=p:b+=1
            B=b-1
            assert length<=B and rho**(B+1)<p<=rho**B
            rows.append({'known_arm_upper':str(q),'rho':str(rho),'actual_length':length,
                         'p2':str(p),'derived_length_upper':B})
    return {'status':'PASS','python':sys.version,'arithmetic':'fractions.Fraction',
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'source_engine_sha256':sha256(Path(T.__file__).read_bytes()).hexdigest(),
            'death_engine_sha256':sha256(Path(T.verify.__file__).read_bytes()).hexdigest(),
            'fixtures':rows,'limits':['Exact finite source/bound controls only; no unknown-length universal copy cap is executed.',
                                    'The uniform contraction must be a promise about every rival, not inferred from the true source alone.']}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
