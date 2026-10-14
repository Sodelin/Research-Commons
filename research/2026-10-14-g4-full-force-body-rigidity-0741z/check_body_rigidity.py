"""Exact checks for a scoped G4 body-rigidity argument.

Python standard library only. These are arithmetic/transcription controls,
not a source solver, independent review, or a Lean/Rust verification.
"""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json

P = 1_000_003

def moments(n):
    lam = n*(n-1)//2
    S = DX = G = H = tangent = 0
    for k in range(n+1):
        lx, ly = k*(k-1)//2, (n-k)*(n-k-1)//2
        w = comb(n,k)*2**(k*(n-k+1))
        d = -lam+3*lx+ly
        S += w; DX += 2*lx*w; G += (3*k-2*n)*w
        H += (d*d-lam-9*lx-ly)*w
        tangent += d*w
    return S,DX,G,H,tangent

def matrix(degree):
    return [[S*n**j for j in range(degree+1)]+[x,g,h]
            for n in range(2,degree+6)
            for S,x,g,h,_ in [moments(n)]]

def det_mod(mat, modulus):
    a = [[x%modulus for x in row] for row in mat]
    d = 1; pivots = []
    for k in range(len(a)):
        hit = next((i for i in range(k,len(a)) if a[i][k]),None)
        if hit is None: return 0,pivots
        if hit != k: a[k],a[hit] = a[hit],a[k]; d = -d
        pivot = a[k][k]; pivots.append(pivot)
        d = d*pivot%modulus; inv = pow(pivot,-1,modulus)
        for i in range(k+1,len(a)):
            f = a[i][k]*inv%modulus
            for j in range(k,len(a)):
                a[i][j] = (a[i][j]-f*a[k][j])%modulus
    return d%modulus,pivots

def det_bareiss(mat):
    a = [row[:] for row in mat]; prev = 1; sign = 1
    for k in range(len(a)-1):
        hit = next((i for i in range(k,len(a)) if a[i][k]),None)
        if hit is None: return 0
        if hit != k: a[k],a[hit] = a[hit],a[k]; sign = -sign
        pivot = a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                num = pivot*a[i][j]-a[i][k]*a[k][j]
                q,r = divmod(num,prev)
                assert r == 0
                a[i][j] = q
        for i in range(k+1,len(a)): a[i][k] = 0
        prev = pivot
    return sign*a[-1][-1]

def mul(a,b,R):
    c=[F(0)]*(R+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=R: c[i+j]+=x*y
    return c

def linear_power(a,b,k,R):
    return [F(comb(k,j))*a**(k-j)*b**j if j<=k else F(0)
            for j in range(R+1)]

def log_series(a,R):
    assert a[0] == 1
    u=a[:];u[0]=F(0); term=[F(1)]+[F(0)]*R; out=[F(0)]*(R+1)
    for k in range(1,R+1):
        term=mul(term,u,R)
        for j in range(R+1): out[j]+=F((-1)**(k+1),k)*term[j]
    return out

def diagonal_series(n,pars,R):
    (x0,x1),(y0,y1),(g0,g1)=pars
    out=[F(0)]*(R+1)
    for k in range(n+1):
        term=linear_power(g0,g1,k,R)
        for a,b,power in [(1-g0,-g1,n-k),(x0,x1,k*(k-1)//2),
                          (y0,y1,(n-k)*(n-k-1)//2)]:
            term=mul(term,linear_power(a,b,power,R),R)
        for j in range(R+1):out[j]+=comb(n,k)*term[j]
    return out

def difference_zero(values,order):
    for _ in range(order):values=[b-a for a,b in zip(values,values[1:])]
    return all(v==0 for v in values)

def variance_bounds(cut=8):
    # Truncated integer and half-integer discrete Gaussian moments at q=1/2.
    zi=F(1)+2*sum((F(1,2**(j*j)) for j in range(1,cut+1)),F(0))
    ni=2*sum((F(j*j,2**(j*j)) for j in range(1,cut+1)),F(0))
    zh=sum((F(1,2**(j*(j+1))) for j in range(cut+1)),F(0))
    nh=sum((F((2*j+1)**2,4*2**(j*(j+1))) for j in range(cut+1)),F(0))
    j=cut+1
    # Every subsequent denominator-term ratio is at most the shown r.
    ri=F(1,2**(2*j+1)); rh=F(1,2**(2*j+2))
    tzi=2*F(1,2**(j*j))/(1-ri)
    tzh=F(1,2**(j*(j+1)))/(1-rh)
    # Squared factors grow by less than 4 per next step for j>=1.
    tni=2*F(j*j,2**(j*j))/(1-4*ri)
    tnh=F((2*j+1)**2,4*2**(j*(j+1)))/(1-4*rh)
    lo_i,hi_i=ni/(zi+tzi),(ni+tni)/zi
    lo_h,hi_h=nh/(zh+tzh),(nh+tnh)/zh
    assert lo_h>hi_i
    assert lo_h-hi_i > F(5381,100_000_000)
    return {'integer_lower':str(lo_i),'integer_upper':str(hi_i),
            'half_integer_lower':str(lo_h),'half_integer_upper':str(hi_h),
            'difference_lower_exceeds':'5381/100000000','cut':cut}

def main():
    assert all(P%d for d in range(2,isqrt(P)+1))
    certificates=[]
    for degree,expected in [(6,172637),(12,220962)]:
        M=matrix(degree);mod,pivots=det_mod(M,P);exact=det_bareiss(M)
        assert mod==expected and exact%P==mod
        certificates.append({'degree':degree,'arities':list(range(2,degree+6)),
            'integer_matrix':M,'determinant':str(exact),'modulus':P,
            'determinant_modulus':mod,'modular_pivots':pivots,
            'two_exact_algorithms_agree':True})
    for n in range(2,41): assert moments(n)[4]==0
    # Direct product-rule check of the Hessian formula, independent of d^2-log'' form.
    for n in range(2,12):
        l=n*(n-1)//2;S,X,G,H,_=moments(n);coeff=0
        for k in range(n+1):
            lx=k*(k-1)//2;ly=(n-k)*(n-k-1)//2
            w=comb(n,k)*2**(k*(n-k+1))
            c2=comb(l,2)+9*comb(lx,2)+comb(ly,2)-3*l*lx-l*ly+3*lx*ly
            coeff+=2*w*c2
        assert coeff==H
    configs={
        'rare':((F(1,2),F(1,5)),(F(1),F(-1,3)),(F(0),F(1,2))),
        'comparable':((F(1),F(-1,3)),(F(1),F(-1,4)),(F(2,5),F(1,7)))
    }
    degree_controls=[];R=6
    for name,pars in configs.items():
        series=[log_series(diagonal_series(n,pars,R),R) for n in range(16)]
        f=[[s[r]-F(n*(n-1),2)*series[2][r] for r in range(R+1)]
           for n,s in enumerate(series)]
        for r in range(1,R+1):
            degree=max(2,r) if name=='rare' else 2*r
            assert difference_zero([v[r] for v in f],degree+1)
            degree_controls.append({'family':name,'order':r,'degree_bound':degree,'passed':True})
    result={'schema':'g4_body_rigidity_arithmetic_v1',
        'scope':'hand theorem support; no master proof, actual rival, compiler, or peer review',
        'rank_certificates':certificates,'tangent_transcription_controls':39,
        'hessian_product_rule_controls':10,'polynomial_degree_controls':degree_controls,
        'gaussian_variance_bounds':variance_bounds(),
        'g4_master_complete':False,'actual_source_zero_constructed':False,
        'independent_review':False,'lean_rust_execution':False}
    Path(__file__).with_name('RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'rank_moduli':[c['determinant_modulus'] for c in certificates],
        'tangent_controls':39,'hessian_controls':10,'polynomial_degree_controls':12,
        'gaussian_variance_gap_lower':'5381/100000000',
        'all_controls_passed':True,'master_complete':False},indent=2))

if __name__=='__main__':main()
