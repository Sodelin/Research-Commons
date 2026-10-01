"""Exact rational controls for the uniform approximate-factor theorem.

The positive-source signature is a multiplicative Bernoulli product. These
checks certify the rational conic reduction and error estimates, not exact
source compression or a full arbitrary-cap recognizer.
"""
from fractions import Fraction as F
from math import ceil
import json
from pathlib import Path
import sympy as sp

def lambdas(M):
    return [j*(j-1)//2 for j in range(2,M+1)]

def R(q,k):
    return sum((q**a for a in range(k)),F(0))

def budget(M,eta,epsilon):
    assert M>=2 and 0<eta<=1 and 0<epsilon<=1
    C=ceil(1/eta)
    L=lambdas(M)[-1]
    N=ceil(8*L*L*C*C/epsilon)
    return C,epsilon/(8*L*L*C),epsilon/(4*L*L*C),N,M*N

def cone_reduce(nodes,weights,exps):
    """Exact Caratheodory reduction; output nodes are input nodes."""
    nodes=list(nodes); weights=list(weights)
    initial=[sum((w*R(q,k) for q,w in zip(nodes,weights)),F(0)) for k in exps]
    while len(nodes)>len(exps):
        mat=sp.Matrix([[sp.Rational(R(q,k).numerator,R(q,k).denominator) for q in nodes] for k in exps])
        a=mat.nullspace()[0]
        a=[F(int(x.p),int(x.q)) for x in a]
        if not any(x>0 for x in a): a=[-x for x in a]
        t=min(w/x for w,x in zip(weights,a) if x>0)
        weights=[w-t*x for w,x in zip(weights,a)]
        assert all(w>=0 for w in weights)
        keep=[i for i,w in enumerate(weights) if w]
        nodes=[nodes[i] for i in keep]; weights=[weights[i] for i in keep]
    final=[sum((w*R(q,k) for q,w in zip(nodes,weights)),F(0)) for k in exps]
    assert initial==final
    return nodes,weights

def compress_certificate(M,eta,epsilon,factors):
    C,delta,beta,N,B=budget(M,eta,epsilon)
    exps=lambdas(M); L=exps[-1]
    large=[]; qs=[]; ws=[]
    for p,q in factors:
        assert 0<p<1 and 0<q<1
        r=p*(1-q)
        if r>delta: large.append((p,q))
        else: qs.append(q); ws.append(r)
    assert sum((p*(1-q) for p,q in factors),F(0))<=C
    # A=1/2 is a genuine positive baseline and its pair moment is >= eta.
    assert F(1,2)*(1-sum((p*(1-q) for p,q in factors),F(0)))>=eta
    qs,ws=cone_reduce(qs,ws,exps)
    clamped=[min(q,1-beta) for q in qs]
    ps=[w/(N*(1-q)) for q,w in zip(clamped,ws)]
    assert all(0<p<=F(1,2) and 0<q<1 for p,q in zip(ps,clamped))
    small_error=L*L*delta*C
    clamp_error=sum((w*abs(R(q,L)-R(q2,L)) for q,q2,w in zip(qs,clamped,ws)),F(0))
    binomial_error=L*L*sum((w*w for w in ws),F(0))/N
    assert small_error<=epsilon/8
    assert clamp_error<=epsilon/8
    assert binomial_error<=epsilon/8
    assert len(large)+len(qs)*N<=B
    return {'M':M,'factors':len(factors),'large':len(large),'cone_nodes':len(qs),
        'N':N,'bound':B,'rational_log_error_upper':str(3*epsilon/8),
        'computed_exact_bound_within_displayed_bound':small_error+clamp_error+binomial_error<=3*epsilon/8,
        'epsilon':str(epsilon),'exact_cone_coordinates_preserved':True,
        'strict_positive_approximate_source':True}

def main():
    cases=[]
    for M in range(2,9):
        factors=[(F((i%7)+1,1000),F(i+2,i+5)) for i in range(30)]
        # Include near-one q with appreciable p: small r does not imply small p.
        factors += [(F(9,10),F(100000+i,100001+i)) for i in range(12)]
        cases.append(compress_certificate(M,F(1,4),F(1,2),factors))
    # Exact scalar polynomial inequalities used by the proof.
    scalar=[]
    for L in range(1,29):
        for q in [F(0),F(1,9),F(1,2),F(8,9),F(1)]:
            assert 0<=R(q,L)<=L
            assert L-R(q,L)<=F(L*(L-1),2)*(1-q)
            scalar.append((L,str(q)))
    result={'status':'PASS','rational_compression_controls':cases,
        'scalar_endpoint_and_near_endpoint_controls':len(scalar),
        'limits':'Exact rational inequalities/conic identities only. General theorem is hand proved. No full QE distance catalogue or exact factor-size bound was executed/proved.'}
    Path(__file__).with_name('closure-bound-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
