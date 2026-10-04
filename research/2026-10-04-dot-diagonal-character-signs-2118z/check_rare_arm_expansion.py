"""Exact transcription controls for the uniform hand proof; no cap extrapolation."""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json

def log_coefficients(p):
    assert p[0]==1
    a=[Q(0)]*len(p)
    for n in range(1,len(p)):
        a[n]=p[n]-sum((k*a[k]*p[n-k] for k in range(1,n)),Q(0))/n
    return a

def actual_log(n,r,z,K):
    # Direct expansion of the actual binomial routing sum, without (6).
    p=[Q(0)]*(K+1)
    for j in range(min(n,K)+1):
        for h in range(min(n-j,K-j)+1):
            c=comb(n,j)*r**comb(j,2)*comb(n-j,h)*(-1)**h
            for ell in range(K-j-h+1):
                p[j+h+ell]+=c*(-z*comb(n-j,2))**ell/factorial(ell)
    return log_coefficients(p)

def P(k,r,z):
    # f_r(t exp(zt)) coefficient vector, followed by logarithmic derivative.
    p=[sum((r**comb(j,2)*Q((j*z)**(n-j),factorial(j)*factorial(n-j))
            for j in range(n+1)),Q(0)) for n in range(k+1)]
    return log_coefficients(p)[k]

def P0(k,z):
    return sum(((-1)**(ell-1)*Q(ell)**(k-ell-1)*z**(k-ell)/factorial(k-ell)
                for ell in range(1,k+1)),Q(0))

def main():
    controls=[]
    for k in range(3,10):
        for r in (Q(1,10),Q(1,2)):
            for z in (Q(1,3),Q(1),Q(5)):
                dual=[((-1)**(k-n))*comb(k,n) for n in range(2,k+1)]
                rows=[actual_log(n,r,z,k) for n in range(2,k+1)]
                pairing=[sum((c*row[h] for c,row in zip(dual,rows)),Q(0))
                         for h in range(k+1)]
                assert pairing[:k]==[0]*k
                expected=factorial(k)*P(k,r,z)
                assert pairing[k]==expected
                controls.append({'k':k,'r':str(r),'z':str(z),'coefficient':str(expected)})
    signs=[]
    for k in range(3,31):
        z=Q(k-1)*Q(2)**(k-4)
        v=P0(k,z)
        assert v==P(k,Q(0),z) and v<0
        signs.append({'k':k,'z':str(z),'value':str(v)})
    out={'status':'PASS','scope':'exact finite transcription controls; uniform proof is in the note',
         'direct_routing_binomial_moment_controls':controls,'coefficient_sign_controls':signs,
         'uniform_tail_bound':str(Q(3,4)+Q(1,40))}
    Path(__file__).with_name('RARE-ARM-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','direct_controls':len(controls),'sign_controls':len(signs)}))
if __name__=='__main__':main()
