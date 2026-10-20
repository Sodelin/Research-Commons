import sympy as s
import json
I=s.eye(2); X=s.Matrix([[0,1],[1,0]]); H=s.Matrix([[1,1],[1,-1]])/s.sqrt(2)
r0=s.diag(s.Rational(9,25),s.Rational(16,25));t0=s.diag(s.Rational(3,5),s.Rational(4,5))
Us=[I,X,H,H*X]
rhos=[s.simplify(U*r0*U.T) for U in Us]; roots=[s.simplify(U*t0*U.T) for U in Us]
quarters=[s.simplify(U*s.diag(s.sqrt(s.Rational(3,5)),s.sqrt(s.Rational(4,5)))*U.T)for U in Us]
assert sum(rhos,s.zeros(2))/4==I/2
assert rhos[0]*rhos[2]!=rhos[2]*rhos[0]
for r,t,h in zip(rhos,roots,quarters):
 assert s.simplify(t*t-r)==s.zeros(2)
 assert s.simplify(h*h-t)==s.zeros(2)
A=s.Matrix.hstack(*[t/2 for t in roots]); G=A.T*A; sqrtG=s.sqrt(2)*G
assert s.simplify(sqrtG*sqrtG-G)==s.zeros(8)
assert s.trace(G)==1
# Direct Kraus construction from the submitted channel's definition.
Vs=[]
for a in range(2):
 V=s.zeros(16,8)
 for i in range(4):
  for c in range(2):
   for b in range(2):V[i*4+c*2+b,i*2+c]=roots[i][b,a]
 Vs.append(V)
assert sum((V.T*V for V in Vs),s.zeros(8))==s.eye(8)
PhiG=sum((V*G*V.T for V in Vs),s.zeros(16))
Ap=s.Matrix.hstack(*[s.kronecker_product(roots[i],roots[i])/2 for i in range(4)])
assert PhiG==Ap.T*Ap
B=s.zeros(16);x=0;wtotal=0;Q=0;counts=0
for i in range(4):
 for j in range(4):
  sg=sqrtG[i*2:i*2+2,j*2:j*2+2]
  w=s.simplify(s.trace(sg.T*sg))
  wp=s.simplify(s.trace(rhos[i]*s.sqrt(2)*I*rhos[j]*s.sqrt(2)*I)/16)
  assert w==wp and w>=0
  affinity=s.trace(roots[i]*roots[j]); x+=w*affinity;wtotal+=w;Q+=2*w*(1-affinity)
  B[i*4:i*4+4,j*4:j*4+4]=s.kronecker_product(sg,quarters[i]*quarters[j]);counts+=1
assert wtotal==1
assert s.simplify(s.trace(B.T*B)-x)==0
assert s.simplify(x-(1-Q/2))==0
print(json.dumps({'status':'PASS','fixture':'Four faithful noncommuting qubit states; n=1; uniform prior; rational square roots; singular 8x8 Gram of rank 2.','block_weight_checks':counts,'channel_TP_and_output_Gram_exact':True,'sqrt_Gram_exact':True,'sum_weights':str(wtotal),'normalized_channel_HS_squared':str(s.simplify(x)),'affinity_risk':str(s.simplify(Q)),'scope':'Exact structural identities, not a proof of entropy/interpolation inequality or a general Gibbs rate.'},indent=2))
