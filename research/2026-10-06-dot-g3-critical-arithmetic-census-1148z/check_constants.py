import hashlib,json,math,time,sys
from pathlib import Path
start=time.monotonic()
p=Path('../g3-astra-continuous-20261006-0732z/providers/symbolic-normal-pilot.json')
b=p.read_bytes(); expected='cc57db65563ac4a7e2f5bf9581b8b75803f2052a49d19442f5e756a0f82996e3'
assert hashlib.sha256(b).hexdigest()==expected
j=json.loads(b)
lam=[1,3,6,10,15,21]
assert j['lambda']==lam
norms=[sum(abs(int(v)) for v in row) for row in j['B_coefficients_descending']]
S=sum(norms); Sl=sum(n*x for n,x in zip(lam,norms))
L=max(1,486*S,1215*Sl)
c=(2*math.factorial(9)*L**9).bit_length(); ell=(2*L).bit_length()
# A-degree increasing, homogeneous degree 1 and 3 respectively.
x=[2,1]; y=[-2,3,0,1]
prod=[0]*5
for i,a in enumerate(x):
 for k,v in enumerate(y): prod[i+k]+=a*v
prod[0]+=9
assert prod==[5,4,3,2,1]
assert 44*24745+42*441==1107302
result={'status':'PASS new integer bound/identity check only','python':sys.version,
'input_sha256':expected,'B_l1_norms':norms,'S':S,'S_lambda':Sl,'L':L,'c':c,'ell':ell,
'q_height_logB_coefficient':441,'q_height_constant':c,
'p_height_logB_coefficient':24745,'p_height_constant':56*c+ell,
'factor_beta21_logB_coefficient':1107302,
'factor_beta21_constant':44*(56*c+ell)+42*c+44,
'P6_division_identity_verified':True,'elapsed_seconds':time.monotonic()-start,
'not_executed':['input endpoint/count QE','critical locus census','input Bmax','recognition']}
Path('constant-check-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
