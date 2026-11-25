from math import isqrt
def primes(n):
    a=bytearray(b'\1')*(n+1); a[:2]=b'\0\0'
    for p in range(2,isqrt(n)+1):
        if a[p]: a[p*p::p]=b'\0'*((n-p*p)//p+1)
    return a
seen=0; cases=[]
for k in (12,14,16,18):
    N=2**k; a=primes(N); counts=[0,0,0]
    low=[p for p in range(3,N) if a[p] and p**4<N]
    for p in low:
        if p**8>N: break
        for r in low:
            if r<=p or (p*r)**4<N: continue
            d=p*r
            for h in range(1,(N-1)//d+1,2):
                if any(h%t==0 for t in low): continue
                m=d*h
                if m**4<=N**3 or not a[N-m]: continue
                hrem=h; j=0
                for t in range(3,isqrt(h)+1,2):
                    if not a[t] or hrem%t: continue
                    hrem//=t; j+=1
                    if hrem%t==0: break
                else:
                    if hrem>1: j+=1
                    assert j<=2
                    assert [q for q in range(1,isqrt(isqrt(N))+2) if q**4<N and m%q==0]==[1,p,r]
                    counts[j]+=1
    seen+=sum(counts); cases.append((k,counts))
print(cases, seen)
