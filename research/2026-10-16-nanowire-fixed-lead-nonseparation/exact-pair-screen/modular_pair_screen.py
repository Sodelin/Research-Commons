"""Exact modular necessary test, own source. Python integers only for certificate.
No floating point, no network, no changes to the original finite-pair packet.
"""
from fractions import Fraction as F
import json, hashlib, sys
from pathlib import Path
P=1009
N=60
FIELD=F(0)
PARAMS={'t':F('25.08215'),'lambda':F('2.5'),'Delta':F('.2'),
        'barrier':F(1000),'base':F('49.37274649512004')}
PROFILES={'minus':PARAMS['base']+F(1,100000000),
          'plus':PARAMS['base']+F(1,10000)}
def residue(x):
    x=F(x)
    assert x.denominator%P !=0
    return (x.numerator*pow(x.denominator,-1,P))%P

def matrix(a):
    t,l,d=map(residue,[PARAMS['t'],PARAMS['lambda'],PARAMS['Delta']]); b=residue(FIELD)
    T=[[-t,0,-l,0],[0,t,0,l],[l,0,-t,0],[0,-l,0,t]]
    H=[[0]*(4*N) for _ in range(4*N)]
    for site in range(N):
        v=residue(PARAMS['barrier'] if site in (0,N-1) else a)
        U=[[v,d,b,0],[d,-v,0,b],[b,0,v,d],[0,b,d,-v]]
        for i in range(4):
            for j in range(4):
                H[4*site+i][4*site+j]=U[i][j]%P
                if site<N-1:
                    H[4*site+i][4*(site+1)+j]=T[i][j]%P
                    H[4*(site+1)+j][4*site+i]=T[i][j]%P
    return H

def charpoly(A):
    """Ascending coefficients of det(xI-A), similarity Hessenberg recurrence."""
    A=[r[:] for r in A]; n=len(A)
    for k in range(1,n):
        pivot=next((i for i in range(k,n) if A[i][k-1]),None)
        if pivot is None: continue
        if pivot!=k:
            A[k],A[pivot]=A[pivot],A[k]
            for row in A: row[k],row[pivot]=row[pivot],row[k]
        inv=pow(A[k][k-1],-1,P)
        for i in range(k+1,n):
            c=A[i][k-1]*inv%P
            if c:
                A[i]=[(x-c*y)%P for x,y in zip(A[i],A[k])]
                for row in A: row[k]=(row[k]+c*row[i])%P
    assert all(A[i][j]==0 for i in range(n) for j in range(i-1))
    polys=[[1]]
    for i in range(1,n+1):
        old=polys[-1]; cur=[0]+old[:]
        for j,v in enumerate(old):cur[j]=(cur[j]-A[i-1][i-1]*v)%P
        product=1
        for k in range(i-1,0,-1):
            product=product*A[k][k-1]%P
            c=A[k-1][i-1]*product%P
            for j,v in enumerate(polys[k-1]):cur[j]=(cur[j]-c*v)%P
        polys.append(cur)
    return polys[-1]

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def remainder(a,b):
    a=a[:]; inv=pow(b[-1],-1,P)
    while a!=[0] and len(a)>=len(b):
        c=a[-1]*inv%P; offset=len(a)-len(b)
        for j,v in enumerate(b):a[offset+j]=(a[offset+j]-c*v)%P
        trim(a)
    return a

def gcd(a,b):
    degrees=[]
    while b!=[0]:
        degrees.append(len(b)-1);a,b=b,remainder(a,b)
    inv=pow(a[-1],-1,P)
    return [v*inv%P for v in a],degrees

def controls():
    import sympy as s
    assert s.isprime(P)
    count=0
    for n in range(1,9):
        for seed in range(4):
            A=[[(i*i+3*j+seed*i*j+7*seed)%P for j in range(n)] for i in range(n)]
            expected=[int(x)%P for x in reversed(s.Matrix(A).charpoly().all_coeffs())]
            assert charpoly(A)==expected
            count+=1
    return {'sympy_version':s.__version__,'independent_small_matrix_controls':count,'prime_verified':P}

def main():
    result={'controls':controls(),'python':sys.version,'prime':P,'B':str(FIELD),'N':N,
            'parameters':{k:str(v) for k,v in PARAMS.items()},
            'interior_profiles':{k:str(v) for k,v in PROFILES.items()},
            'denominator_residues':{k:v.denominator%P for k,v in (PARAMS|PROFILES|{'B':FIELD}).items()}}
    polynomials={}
    for name,a in PROFILES.items():
        H=matrix(a)
        assert H==list(map(list,zip(*H)))
        f=charpoly(H)
        assert len(f)==241 and f[-1]==1
        assert all(f[j]==0 for j in range(1,len(f),2))
        polynomials[name]=f
    g,seq=gcd(polynomials['minus'],polynomials['plus'])
    result.update({'charpolys_ascending_mod_p':polynomials,'gcd':g,'euclidean_divisor_degrees':seq,
                  'status':'COPRIME' if g==[1] else 'INCONCLUSIVE'})
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    target=Path(__file__).with_name('MODULAR-PAIR-RESULT.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='charpolys_ascending_mod_p'},indent=2))
if __name__=='__main__':main()
