"""Additional exact point/codec scope controls; SAME_BACKEND, no census replay."""
from pathlib import Path
import json,sys,hashlib
import z3
root=Path(sys.argv[1]).resolve()
sys.path.insert(0,str(root))
from algebraic_history_point import decode_exact,encode_exact,evaluate_section
def true(p):return z3.is_true(z3.simplify(p))
def section(coeff,lo='-4',hi='4'):
 return {'name':'action_root_extra','coefficients':coeff,'lower':lo,'upper':hi}
checks=[]
for i,(square,positive) in enumerate(((3,False),(2,False),(2,True),(3,True)),1):
 value=decode_exact({'kind':'algebraic','polynomial_ascending':['6','0','-5','0','1'],'real_root_index':i})
 assert true(value*value==square) and true(value>0 if positive else value<0)
 assert true(decode_exact(encode_exact(value))==value)
 checks.append({'name':'four-real-root-index-'+str(i),'pass':True})
neg=decode_exact({'kind':'algebraic','polynomial_ascending':['6/7','0','-1/7'],'real_root_index':1})
pos=decode_exact({'kind':'algebraic','polynomial_ascending':['-6/7','0','1/7'],'real_root_index':2})
assert true(pos+neg==0) and true(pos*pos==6)
checks.append({'name':'positive-denominator-clearing-with-leading-sign-change','pass':True})
# Bounds and coefficients from two independent exact algebraic inputs.
rt2=decode_exact({'kind':'algebraic','polynomial_ascending':['-2','0','1'],'real_root_index':2})
rt3=decode_exact({'kind':'algebraic','polynomial_ascending':['-3','0','1'],'real_root_index':2})
out,v=evaluate_section(section(['-(h0_0+h0_1)','1'],'h0_0','2*h0_1'),{'h0_0':encode_exact(rt2),'h0_1':encode_exact(rt3)})
assert out['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND' and true(v==rt2+rt3)
checks.append({'name':'two-algebraic-coefficient-fields-and-algebraic-bounds','pass':True})
# The same algebraic value in two equivalent encodings must make a written denominator zero.
rt8half=z3.simplify(z3.Sqrt(z3.RealVal(8))/2)
assert true(rt2==rt8half)
bad=section(['-(h0_0-h0_1)/(h0_0-h0_1)','1'])
out,v=evaluate_section(bad,{'h0_0':encode_exact(rt2),'h0_1':encode_exact(rt8half)})
assert out['status'].startswith('UNKNOWN_') and v is None
checks.append({'name':'equivalent-algebraic-encodings-undefined-cancelled-domain','pass':True})
for name,point,known in [
 ('reversed-algebraic-bounds',section(['0','1'],'h0_1','h0_0'),{'h0_0':encode_exact(rt2),'h0_1':encode_exact(rt3)}),
 ('algebraic-bound-endpoint-root',section(['-h0_0','1'],'h0_0','h0_1'),{'h0_0':encode_exact(rt2),'h0_1':encode_exact(rt3)}),
 ('coefficient-list-not-carrier',{'name':'action_root_extra','coefficients':None,'lower':'0','upper':'1'},{}),
 ('algebraic-codec-extra-field',section(['-h0_0','1']),{'h0_0':{'kind':'rational','value':'1/2','hidden':'s'}}),
 ('root-index-beyond-real-carrier',section(['-h0_0','1']),{'h0_0':{'kind':'algebraic','polynomial_ascending':['-2','0','1'],'real_root_index':3}})
]:
 out,v=evaluate_section(point,known)
 assert out['status'].startswith('UNKNOWN_') and v is None,(name,out)
 checks.append({'name':name,'pass':True,'status':out['status']})
result={'status':'PASS','checks':checks,'source_sha256':hashlib.sha256((root/'algebraic_history_point.py').read_bytes()).hexdigest(),
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'trust':'exact Z3/codec SAME_BACKEND controls; not independent backend certification',
'scope':'closed algebraic point boundaries only; actual source chronology remains separately verified'}
Path(__file__).with_name('ADDITIONAL-POINT-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

