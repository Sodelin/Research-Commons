"""Extra exact structured Root value controls, without a source-census replay."""
import sys,json,hashlib
from pathlib import Path
import z3
stage=Path(sys.argv[1]).resolve();sys.path.insert(0,str(stage))
from cad_value import evaluate_value
from algebraic_history_point import encode_exact,decode_exact
def R(x):return {'kind':'rational','value':str(x)}
def O():return {'kind':'observation','name':'h0_0'}
def P(x,e):return {'kind':'power','base':x,'exponent':e}
def M(*xs):return {'kind':'multiply','args':list(xs)}
def A(*xs):return {'kind':'add','args':list(xs)}
def Root(cs,k):return {'kind':'root','coefficients':cs,'real_root_index':k}
a=decode_exact({'kind':'algebraic','polynomial_ascending':['-2','0','1'],'real_root_index':2})
known={'h0_0':encode_exact(a)};checks=[]
def yes(name,t,want,scope=known):
 r,v=evaluate_value(t,scope);assert r['status']=='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND',(name,r)
 assert z3.is_true(z3.simplify(v==want)),name
 checks.append({'name':name,'status':'PASS'})
def no(name,t,scope=known,**kw):
 r,v=evaluate_value(t,scope,**kw);assert r['status'].startswith('UNKNOWN_') and v is None,(name,r)
 checks.append({'name':name,'status':r['status']})
cs=[M(R(-2),P(O(),3)),M(R(5),P(O(),2)),M(R(-4),O()),R(1)]
for k,want in [(1,a),(2,a),(3,2*a)]:yes('algebraic-double-root-'+str(k),Root(cs,k),want)
cs2=[P(O(),2),A(P(O(),2),M(R(-2),O())),A(R(1),M(R(-2),O())),R(1)]
for k,want in [(1,z3.RealVal(-1)),(2,a),(3,a)]:yes('negative-simple-before-double-'+str(k),Root(cs2,k),want)
yes('quartic-zero-counts-four',Root([R(0),R(0),R(0),R(0),R(1)],4),z3.RealVal(0),{})
yes('real-root-before-complex-pair',Root([R(0),R(1),R(0),R(1)],1),z3.RealVal(0),{})
no('complex-index-after-real',Root([R(0),R(1),R(0),R(1)],2),{})
yes('principal-fourth-negative-exponent',{'kind':'principal_power','base':R(16),'numerator':-3,'denominator':4},z3.RealVal('1/8'),{})
yes('minimum-maximum-algebraic',{'kind':'minimum','args':[O(),{'kind':'maximum','args':[R(1),M(R(2),O())]}]},a)
no('written-zero-product-keeps-division-domain',M(R(0),{'kind':'divide','numerator':R(1),'denominator':R(0)}),{})
no('leading-zero-at-exact-algebraic-history',Root([R(1),A(O(),M(R(-1),O()))],1))
cycle={'kind':'add','args':[]};cycle['args'].append(cycle);no('cyclic-API-tree',cycle,{})
result={'status':'PASS','checks':checks,'source_sha256':hashlib.sha256((stage/'cad_value.py').read_bytes()).hexdigest(),
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'trust':'exact SAME_BACKEND controls, not independent backend certification',
'scope':'supported structured values only; no symbolic cell or full-policy coverage inferred'}
Path(__file__).with_name('ADDITIONAL-CAD-VALUE-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

