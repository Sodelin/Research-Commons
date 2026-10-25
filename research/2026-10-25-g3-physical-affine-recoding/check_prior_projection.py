"""Check projection rank on the prior fixed-pair hyperplane. Not a new bank proof."""
from pathlib import Path
import json
ns={}
source=Path(__file__).with_name('check_nonadjacent_channels.py')
exec(source.read_text().split('j0=matrix_at(boundary)')[0],ns)
s=ns['s'];x,y,g=ns['variables'];b=ns['b']
pt={x:s.Rational(1,2),y:s.Rational(1,3),g:s.Rational(2,5)}
J=ns['matrix_at'](pt)
for i in (0,1):
    for j,t in enumerate((x,y,g)):
        J[i,j]-=9*ns['log_derivative'](b[2],t,pt)
det=s.factor(J.det())
assert b[2].subs(pt)==s.Rational(17,25)
assert det==s.Rational(10123781818781620345671359,3619497406158882904299761)
z=s.Rational(1,4)/b[2].subs(pt)
assert z==s.Rational(25,68) and 0<z<1
report={'scope':'Projection rank only; inherited rank18 bank not rerun','bare_point':{str(k):str(v) for k,v in pt.items()},'pair':'1/4','total_padding':str(z),'prefix_and_suffix':'5/sqrt(68)','transformed_matrix':[[str(a) for a in row] for row in J.tolist()],'determinant':str(det),'result':'PASS'}
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
