import resource
resource.setrlimit(resource.RLIMIT_CPU,(10,10));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import mpmath as m,json,time
from pathlib import Path
start=time.monotonic();m.mp.dps=60
base=json.loads(Path('stage1-result.json').read_text());row=json.loads(Path('stage4-result.json').read_text())['candidate_pairs'][0]
p=m.mpf(row['p']);q=m.mpf(row['q']);r=m.mpf('.5');ls=base['lambda'];cs=[m.mpf(c)/m.mpf(base['normal_sum']) for c in base['normal']]
def F(x):return sum(c*(1-x**l) for c,l in zip(cs,ls))
J=m.matrix([[l,1-r**l,-l*r**(l-1),(1-q**l)/(1-p+p*q**l),-p*l*q**(l-1)/(1-p+p*q**l)] for l in ls]);rhs=m.matrix([1-r**(2*l) for l in ls]);t=m.lu_solve(J[1:6,:],rhs[1:6,:])
H=m.matrix([[0,0],[0,0]])
for c,l in zip(cs,ls):
 f=1-p+p*q**l;H[0,0]+=c*(1-q**l)**2/f**2;H[0,1]-=c*l*q**(l-1)/f**2;H[1,1]+=c*(-p*l*(l-1)*q**(l-2)/f+p*p*l*l*q**(2*l-2)/f**2)
H[1,0]=H[0,1];tr=m.matrix([t[3],t[4]]);B=(tr.T*H*tr)[0]/8
F2=-sum(c*l*(l-1)*r**(l-2) for c,l in zip(cs,ls));A=F(r**3)/3+F2*t[2]**2/8
out={'status':'NUMERICAL EXPLORATION ONLY','t':[m.nstr(x,55) for x in t],'A':m.nstr(A,55),'B':m.nstr(B,55),'candidate_threshold':m.nstr(-A/B,55) if B<0 else None,'full_tangent_residual':m.nstr(max(abs(x) for x in J*t-rhs),10),'seconds':time.monotonic()-start}
Path('one-copy-defect-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
