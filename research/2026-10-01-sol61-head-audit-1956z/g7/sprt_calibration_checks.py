"""Exact rational source and error check for the scoped CONCUR threshold audit."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib

def mul(v,M):return [sum((v[i]*M[i][j] for i in range(len(v))),F(0)) for j in range(len(v))]
def prefix(v,matrices,word):
    for c in word:v=mul(v,matrices[c])
    return sum(v)

def check():
    za=[[F(0) for _ in range(3)] for _ in range(3)];zb=[row[:] for row in za]
    za[0][1]=F(22,25);zb[0][1]=F(3,25);za[1][1]=1;zb[2][2]=1
    M={'a':za,'b':zb};p=[F(1),F(0),F(0)];q=[F(0),F(0),F(1)]
    assert all(sum(za[i])+sum(zb[i])==1 for i in range(3))
    for n in range(1,9):
        assert prefix(p,M,'a'*n)==F(22,25) and prefix(q,M,'a'*n)==0
        assert prefix(p,M,'b'+'a'*(n-1))==F(3,25)
        assert prefix(q,M,'b'*n)==1
        if n>1:assert prefix(p,M,'b'*n)==0 and prefix(q,M,'b'+'a'*(n-1))==0
    alpha,beta=F(1,10),F(1,5);lower=alpha/(1-beta);upper=(1-alpha)/beta
    lr=prefix(p,M,'b')/prefix(q,M,'b')
    assert lr<lower and lr>alpha and lower==F(1,8) and upper==F(9,2)
    assert F(3,25)>alpha
    # Initial-mixture form, with states A,D,B.
    a=[[F(1),F(0),F(0)],[F(0),F(0),F(0)],[F(0),F(0),F(0)]]
    b=[[F(0),F(0),F(0)],[F(1),F(0),F(0)],[F(0),F(0),F(1)]]
    pm=[F(22,25),F(3,25),F(0)];qm=[F(0),F(0),F(1)]
    assert prefix(pm,{'a':a,'b':b},'b')==lr
    assert prefix(qm,{'a':a,'b':b},'b')==1
    out={'status':'PASS','alpha':str(alpha),'beta':str(beta),'nominal_lower':str(lower),
         'nominal_upper':str(upper),'first_b_likelihood_ratio':str(lr),
         'nominal_actual_pi1_error':'3/25','nominal_actual_pi2_error':'0',
         'three_state_Dirac_and_initial_mixture_models_checked':True,
         'safe_gate':'ratio<=alpha or ratio>=1/beta; abstract anytime proof separate',
         'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('sprt-calibration-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':check()
