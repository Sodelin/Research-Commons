import hashlib,json,unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch
import interval_math as m
import interval_ad as ad
import joint_contractor as j
I=m.I
REFERENCE=Path(__file__).resolve().parent.parent/'msci-330-feature-public-20261005-1039z/evaluator/CONTROL-RESULTS.json'
REFERENCE_SHA='acf3a3cfe6addaa79a29106c3aca9985e5247b18e4c31b41a50ff0d9e8552c6a'
def source(name):
    raw=REFERENCE.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=REFERENCE_SHA:raise ValueError('reference identity')
    p={key:F(value) for key,value in json.loads(raw)['fixtures'][name]['parameters'].items()};x={key:p[key] for key in ad.COORDS if key not in ('u','v')};x['u']=p['t1']-p['h'];x['v']=p['t0']-p['t1'];return p,{key:I.point(value) for key,value in x.items()}
def identity():return tuple(tuple(F(int(i==k)) for k in range(9)) for i in range(9))
def mock_state():return j.initial({key:I(F(1,4),F(3,4)) for key in ad.COORDS},{key:I(F(2,3),F(5,6)) for key in m.FEATURES})
def identity_ad(box):return tuple(box[key] for key in ad.COORDS),tuple(tuple(I.point(v) for v in row) for row in identity())
class Tests(unittest.TestCase):
    def test_point_values_and_analytic_root_gradient(self):
        for name in ('distinct_rates','equal_rates'):
            p,box=source(name);values,J=ad.evaluate(box);_,raw,_=m.forward.evaluate(p,128)
            for i,key in enumerate(m.FEATURES):
                reference=raw[key[:-1]][int(key[-1])-1];self.assertLessEqual(values[i].lo,reference.lo);self.assertGreaterEqual(values[i].hi,reference.hi)
            for i,k in [(0,1),(1,2)]:
                z=F(8*k,3);value=m.tail(z,I.point(p['t0']),I.point(p['rR']));dtime=value*(-z);dr=m.E(I.point(z*p['t0']))*(z/(p['rR']+z)**2)
                for col in (0,1,2):self.assertTrue(J[i][col].intersects(dtime))
                self.assertTrue(J[i][7].intersects(dr))
                for col in (3,4,5,6,8):self.assertEqual(J[i][col],I.point(0))
    def test_H_gradient_against_independent_formula(self):
        r=F(2);ell=F(1,16);z=F(8,3);ar=ad.seed(I.point(r),0);al=ad.seed(I.point(ell),1)
        value=ar/(ar+z)*(1-ad.exp_negative((ar+z)*al));E=m.E(I.point((r+z)*ell))
        dr=(1-E)*(z/(r+z)**2)+E*(r*ell/(r+z));dl=E*r
        self.assertTrue(value.gradient[0].intersects(dr));self.assertTrue(value.gradient[1].intersects(dl))
    def test_S_R_gradients_independently(self):
        r=F(2);ell=F(1,16);z=F(8,3);ar=ad.seed(I.point(r),0);al=ad.seed(I.point(ell),1)
        survival=ad.exp_negative(ar*al);E=m.E(I.point(r*ell));root=ar/(ar+z)
        self.assertTrue(survival.gradient[0].intersects(E*(-ell)));self.assertTrue(survival.gradient[1].intersects(E*(-r)));self.assertTrue(root.gradient[0].contains(z/(r+z)**2))
    def test_BB_tied_rate_derivative_independently(self):
        p,box=source('distinct_rates');_,J=ad.evaluate(box);z=F(8,3);h=p['h'];u=p['t1']-h;v=p['t0']-p['t1'];L=u+v;b=p['rB'];d=p['rAB'];c=p['rC'];R=p['rR'];g=p['g'];q=1-g
        exp=lambda x:m.E(I.point(x))
        H=lambda rate,length:m.H(z,I.point(rate),I.point(length))
        def Hr(rate,length):
            E=exp((rate+z)*length);return (1-E)*(z/(rate+z)**2)+E*(rate*length/(rate+z))
        tail=exp(z*p['t0'])*(R/(R+z));sbh=exp(b*h);sbu=exp(b*u);sdv=exp(d*v);scL=exp(c*L)
        continuation=q*q*(exp(z*h)*H(b,u)+sbu*exp(z*p['t1'])*H(d,v))+g*g*exp(z*h)*H(c,L)+(q*q*sbu*sdv+g*g*scL+2*g*q)*tail
        derivative=Hr(b,h)-h*sbh*continuation+sbh*q*q*(exp(z*h)*Hr(b,u)-u*sbu*(exp(z*p['t1'])*H(d,v)+sdv*tail))
        self.assertTrue(J[8][4].intersects(derivative))
    def test_shared_variable_product_derivative(self):
        x=ad.seed(I(1,2),0);value=x*x
        self.assertLessEqual(value.gradient[0].lo,2);self.assertGreaterEqual(value.gradient[0].hi,4)
        with self.assertRaises(ValueError):ad.AD.cast(.1)
    def test_physical_rewrite_preserves_nonnegative_exp_arguments(self):
        box={key:I(F(1,2),6) for key in ad.COORDS}
        for key in ('h','u','v'):box[key]=I(F(1,32),F(1,8))
        box['g']=I(F(1,6),F(2,3));x={key:ad.seed(box[key],i) for i,key in enumerate(ad.COORDS)};seen=[]
        def mock_exp(arg):
            seen.append(arg.value);return ad.AD.cast(1)
        ad.physical_pair_expressions(x,F(8,3),mock_exp)
        self.assertGreater(len(seen),0);self.assertTrue(all(value.lo>=0 for value in seen))
    def test_old_time_subtraction_dependency_artifact_is_explicit(self):
        box={key:I(F(1,2),6) for key in ad.COORDS}
        for key in ('h','u','v'):box[key]=I(F(1,32),F(1,8))
        box['g']=I(F(1,6),F(2,3));x={key:ad.seed(box[key],i) for i,key in enumerate(ad.COORDS)};p={key:x[key] for key in ('h','rA','rB','rC','rAB','rR','g')};p['t1']=x['h']+x['u'];p['t0']=p['t1']+x['v'];seen=[]
        def mock_exp(arg):seen.append(arg.value);return ad.AD.cast(1)
        m.forward.pair_expressions(p,F(8,3),mock_exp)
        self.assertTrue(any(value.lo<0 for value in seen))
    def test_exact_rational_inverse_and_singular_refusal(self):
        matrix=tuple(tuple(F(i+1) if i==k else F(0) for k in range(9)) for i in range(9));inverse=j.rational_inverse(matrix)
        self.assertEqual(inverse[8][8],F(1,9))
        with self.assertRaises(j.PreconditionerRefusal):j.rational_inverse(((F(0),)*9,)*9)
    def test_interval_rhs_not_replaced_by_center(self):
        state=mock_state()
        with patch.object(ad,'evaluate',side_effect=identity_ad):out,receipt=j.operate(state,'joint')
        for box in out['physical'].values():self.assertTrue(box.contains(F(1,3)));self.assertTrue(box.contains(F(2,3)));self.assertGreater(box.width,0)
        self.assertEqual(receipt['target_units'],'raw_laplace_moments')
    def test_q_ignores_inherited_auxiliary_restrictions(self):
        state=mock_state();state['aux']['T']=I.point(F(3,4));seen=[]
        def fake(box):seen.append(dict(box));return identity_ad(box)
        with patch.object(ad,'evaluate',side_effect=fake):out,receipt=j.operate(state,'joint')
        self.assertEqual(sum(seen[0][key].lo for key in ('h','u','v')),F(3,2));self.assertEqual(state['aux']['T'],I.point(F(3,4)));self.assertFalse(receipt['auxiliary_or_target_clipping_used_for_Fq_or_J'])
    def test_zero_preconditioner_preserves_box(self):
        state=mock_state()
        with patch.object(ad,'evaluate',side_effect=identity_ad):out,receipt=j.operate(state,'joint_zero')
        self.assertEqual(j.record(out),j.record(state));self.assertEqual(receipt['preconditioner_mode'],'DECLARED_ZERO_NOOP')
    def test_singular_finite_matrix_is_safe_noop(self):
        state=mock_state()
        with patch.object(ad,'evaluate',return_value=((I.point(0),)*9,((I.point(0),)*9,)*9)):out,receipt=j.operate(state,'joint')
        self.assertEqual(j.record(out),j.record(state));self.assertEqual(receipt['preconditioner_mode'],'CONDITIONING_REFUSAL_ZERO_NOOP')
    def test_sign_aware_matrix_vector(self):
        matrix=tuple(tuple(F(-2) if i==k else F(0) for k in range(9)) for i in range(9));value=j.matrix_vector(matrix,(I(1,3),)*9);self.assertEqual(value,(I(-6,-2),)*9)
if __name__=='__main__':unittest.main()
