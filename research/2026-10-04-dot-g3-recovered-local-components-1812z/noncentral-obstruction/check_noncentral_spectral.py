#!/usr/bin/env python3
"""Exact finite transcription controls, not a substitute for the all-length proof."""
from fractions import Fraction as F
from pathlib import Path
import hashlib, json

def mul(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def eye(n):
    return [[F(i==j) for j in range(n)] for i in range(n)]
def lift(T):
    return [r+[1-sum(r)] for r in T]+[[F(0),F(0),F(0),F(1)]]
def D(a):
    return [[a**3,F(0),F(0)],[F(0),a,F(0)],[F(0),F(0),F(1)]]
def H(t):
    return [[F(1),t**4/4,t**6/120],[F(0),F(1),t**2/4],[F(0),F(0),F(1)]]
def O(a): return lift(D(a))
def M(t,v):
    a=(1-v)*(1-t/3)
    return lift(mul(D(a),H(t)))
def coords(K):
    A=K[1][1]
    assert K[0][0]==A**3 and K[2][2]==1
    return A, K[1][2]/A*4, K[0][1]/A**3*4, K[0][2]/A**3*16

counts={"finite_words":0,"geometric_prefixes":0,"stochastic_weak_controls":0}
for length in range(1,25):
    ts=[F(1+(7*i+length)%11,15) for i in range(length)]
    vs=[F(1+(3*i+length)%9,12) for i in range(length)]
    gaps=[F(1+(5*i+length)%8,11) for i in range(length)]
    aa=[(1-v)*(1-t/3) for t,v in zip(ts,vs)]
    K=O(F(2,3))
    for t,v,a in zip(ts,vs,gaps): K=mul(mul(K,M(t,v)),O(a))
    suffix=F(1); us=[]
    for i in reversed(range(length)):
        suffix*=gaps[i]
        us.append(ts[i]**2/suffix)
        suffix*=aa[i]
    us=list(reversed(us))
    A,X,Y,Z=coords(K)
    assert A==F(2,3)*suffix
    assert X==sum(us) and Y==sum(u*u for u in us)
    assert Z==F(2,15)*sum(u**3 for u in us)+sum(us[i]**2*us[j] for i in range(length) for j in range(i+1,length))
    sos=sum(us[i]*(us[i]-F(3,4)*sum(us[i:]))**2 for i in range(length))
    assert sos==F(3,16)*X**3-F(15,16)*Z>0
    counts["finite_words"]+=1

for n in range(1,25):
    K=O(F(1,2))
    for i in range(1,n+1):
        z=F(1,2**i); b=(1-z)/(1-z/2)
        t=z*(1-z)*(1-z/2); v=1-b*b/(1-t/3)
        assert 0<t<1 and 0<v<1 and (1-v)*(1-t/3)==b*b
        K=mul(mul(K,M(t,v)),O(b*b))
    A,X,Y,Z=coords(K)
    factor=(1-F(1,2**(n+1)))**4
    us=[F(1,4**i)*factor for i in range(1,n+1)]
    assert A==F(1,32)/(1-F(1,2**(n+1)))**4
    assert X==sum(us) and Y==sum(u*u for u in us)
    assert Z==F(2,15)*sum(u**3 for u in us)+sum(us[i]**2*us[j] for i in range(n) for j in range(i+1,n))
    counts["geometric_prefixes"]+=1

for i in range(1,20):
  for j in range(1,20):
    t=F(i,20);v=F(j,20);a=(1-v)*(1-t/3)
    B=M(t,v); E=O(a)
    assert all(sum(r)==1 and min(r)>=0 for r in B)
    tv=max(sum(abs(x-y) for x,y in zip(r,s))/2 for r,s in zip(B,E))
    assert tv<=F(93,40)*(1-a)**2
    counts["stochastic_weak_controls"]+=1

K=[[F(1,32768),F(1,1966080),F(1,70778880),F(70776683,70778880)],
   [F(0),F(1,32),F(1,384),F(371,384)],
   [F(0),F(0),F(1),F(0)],[F(0),F(0),F(0),F(1)]]
assert coords(K)==(F(1,32),F(1,3),F(1,15),F(1,135))
assert all(sum(r)==1 for r in K)
assert mul(O(F(1,2)),M(F(1,3),F(1,4)))!=mul(M(F(1,3),F(1,4)),O(F(1,2)))

out={"status":"PASS","scope":"Finite transcription controls; universal theorem has a separate hand proof; abstract family only.","counts":counts,"endpoint":[[str(v) for v in r] for r in K],"script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name("NONCENTRAL-SPECTRAL-CONTROLS.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))
