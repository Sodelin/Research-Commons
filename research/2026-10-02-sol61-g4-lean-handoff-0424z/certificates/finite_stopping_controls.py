#!/usr/bin/env python3
"""Exact focused controls for cumulative stopping and Kingman Hankel algebra."""
from fractions import Fraction as Q
from hashlib import sha256
from math import comb, prod
from pathlib import Path
import json
import sys
import tomography_check as T


def determinant(matrix):
    a=[row[:] for row in matrix]
    value=Q(1)
    for i in range(len(a)):
        pivot=next((j for j in range(i,len(a)) if a[j][i]),None)
        if pivot is None:
            return Q(0)
        if pivot!=i:
            a[i],a[pivot]=a[pivot],a[i]
            value=-value
        v=a[i][i]
        value*=v
        for j in range(i+1,len(a)):
            c=a[j][i]/v
            for k in range(i,len(a)):
                a[j][k]-=c*a[i][k]
    return value


def run():
    hankel=[]
    for q in (Q(1,2),Q(2,3),Q(5,4)):
        for n in range(1,7):
            for shift in range(4):
                h=[[q**comb(shift+i+j,2) for j in range(n)] for i in range(n)]
                exponent=n*comb(shift,2)+shift*n*(n-1)+n*(n-1)*(n-2)//2
                formula=(-1)**comb(n,2)*q**exponent*prod((1-q**d)**(n-d) for d in range(1,n))
                actual=determinant(h)
                assert actual==formula and actual!=0
                hankel.append({'q':str(q),'size':n,'shift':shift,'determinant':str(actual)})
        if q<1:
            assert determinant([[Q(1),q],[q,q**3]])==q*q*(q-1)<0
    assert determinant([[Q(1),Q(1)],[Q(1),Q(1)]])==0
    cumulative=[]
    for length in range(11):
        start=('A1','A2')
        dist=T.edge(start,Q(3,4))
        p=Q(3,4)
        envelope=Q(1)
        for i in range(1,length+1):
            q=Q(i,i+2)
            x,y,g=q,q,Q(1,2)
            beta=g*g*x+(1-g)**2*y+2*g*(1-g)
            rho=Q(i+1,i+2)
            assert 0<x<1 and 0<y<1 and 0<g<1 and beta==rho
            connector=Q(i+4,i+5)
            assert 0<connector<1
            dist=T.push(dist,lambda f:T.bigon(f,x,y,g))
            dist=T.push(dist,lambda f:T.edge(f,connector))
            p*=beta*connector
            envelope*=rho
        assert envelope==Q(2,length+2)
        assert 0<dist[start]==p<=envelope
        b=1
        while Q(2,b+2)>=p:
            b+=1
        assert length<=b-1 and Q(2,b+2)<p
        if b>1:
            assert p<=Q(2,b+1)
        cumulative.append({'actual_length':length,'p2':str(p),'envelope':str(envelope),'derived_length_upper':b-1})
    return {'status':'PASS','python':sys.version,'arithmetic':'fractions.Fraction',
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'source_engine_sha256':sha256(Path(T.__file__).read_bytes()).hexdigest(),
            'death_engine_sha256':sha256(Path(T.verify.__file__).read_bytes()).hexdigest(),
            'hankel':hankel,'cumulative':cumulative,
            'limits':['72 exact matrix identities and 11 source fixtures; universal statements are separate hand proofs.',
                      'q>1 checks are algebra only, not admitted source probabilities.',
                      'The cumulative envelope is a promise about every rival.',
                      'No unrestricted unknown-length inverse stop, fixed-target replica or general QE cap was executed.']}


if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
