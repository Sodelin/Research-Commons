"""One exact source-group target checked against the concrete cap-five gate.

The target's E(4) suffix is mathematical, not a physical population. Its
positive realization is supplied only by the independently reviewed box gate.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import types
import mpmath as mp

HELPER="research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/exact_forest_layer.py"
HELPER_SHA="e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"
INPUT_SHA="bb6bcc498125a86b797748f8f936b60051ac327f07d761fab2caeab531d70a8e"
CERT_SHA="30c045b785dc0e2e8fe5b7ef3dd794c128638d39dd8766d8b613b326991cbe28"


def iv(q):
    q=F(q);return mp.iv.mpf(q.numerator)/q.denominator


def rational(t):
    sign,n,e,_=t;q=F((-1 if sign else 1)*n)
    return q*2**e if e>=0 else q/F(2**(-e))


def enclosure(x):return list(map(str,map(rational,x._mpi_)))


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[4])
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if args.output.exists():raise ValueError('refusing to overwrite saved target gate')
    base=Path(__file__).resolve().parent
    raw=(base/'RATIONAL-BOX-INPUT.json').read_bytes();cr=(base/'INTERVAL-BOX-CERTIFICATE.json').read_bytes()
    if sha256(raw).hexdigest()!=INPUT_SHA or sha256(cr).hexdigest()!=CERT_SHA:raise ValueError('frozen box pin mismatch')
    inputs,cert=json.loads(raw),json.loads(cr)
    hraw=(args.root/HELPER).read_bytes()
    if sha256(hraw).hexdigest()!=HELPER_SHA:raise ValueError('authenticated helper mismatch')
    h=types.ModuleType('read_only_target_forest_helper');h.__file__=str(args.root/HELPER)
    exec(compile(hraw,h.__file__,'exec'),h.__dict__)
    fa,original_sha=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES5];index={s:i for i,s in enumerate(h.SHAPES5)}
    E=h.ordinary_polynomials(states,index,fa);B=h.bigon_polynomials(states,index,fa)
    ordinary=lambda z:[[h.eval_poly(p,z) for p in row] for row in E]
    epsilon=F(1,10**80);x=1-epsilon;v=1-epsilon/2;d=F(1,4);t=F(1,10000)
    bare=[[sum((c*x**(p+q) for (p,q),c in poly.items()),F(0)) for poly in row] for row in B]
    # Exact target source comparison, with currently merged older subtrees
    # grafted intact, for every one of the ten cap-five orbit states.
    for i,f in enumerate(states):
        direct=[F(0)]*10
        for out,p in fa.bigon_law(len(f),x,x,F(1,2),'independent').items():
            direct[index[h.forest_shape(fa.graft(f,out))]]+=p
        assert direct==bare[i]
    K=h.matmul(h.matmul(ordinary(F(1,16)),bare),ordinary(F(4)))
    N=h.matmul(ordinary(1/(d*v)),K)
    row=N[0]
    q4=[row[0]+F(2,5)*row[1],F(3,5)*row[1]+F(4,5)*row[2]+F(3,5)*row[3],
        F(2,5)*row[3]+F(2,5)*row[4]+F(4,5)*row[5]+F(4,5)*row[6],F(1,5)*row[2]+F(3,5)*row[4],
        F(1,5)*row[5]+F(1,5)*row[7]+F(3,5)*row[9],F(1,5)*row[6]+F(4,5)*row[7]+row[8]+F(2,5)*row[9]]
    C=q4[3]-(q4[2]+q4[3])/3;H=q4[4]-(q4[4]+q4[5])/3
    b=[sum((F(__import__('math').comb(n,k),2**n)*x**(__import__('math').comb(k,2)+__import__('math').comb(n-k,2)) for k in range(n+1)),F(0)) for n in range(2,6)]
    assert b[0]==v and sum(row,F(0))==1
    mp.mp.dps=mp.iv.dps=120
    l2,l3,l4,l5=[mp.iv.log(iv(z)) for z in b]
    target=[iv(v-1),(l3-3*l2)/iv(t**3),(l4-4*l3+6*l2)/iv(t**4),
            (l5-5*l4+10*l3-10*l2)/iv(t**5),iv(C/t**3),iv((C+H)/t**3),*(iv(row[j]/t**3) for j in [7,8,9])]
    bound=max(max(abs(rational(q)) for q in value._mpi_) for value in target)
    eta=F(cert['certified_target_scaled_coordinate_radius_exact_rational'])
    assert bound<eta and abs(v-1)<F(inputs['parameter_cube_radius'])
    # This exact diagnostic prevents advertising the library factor as an
    # ordinary-target rival. Ordinary padding preserves its strict sign.
    cap3_discrepancy=d**3*(b[1]-v**3)
    assert cap3_discrepancy==-d**3*epsilon**3/8<0
    result={'status':'EXACT_SOURCE_TARGET_AND_OUTWARD_COORDINATE_GATE_PASS',
        'own_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'box_input_sha256':INPUT_SHA,'box_certificate_sha256':CERT_SHA,
        'original_source_sha256':original_sha,'helper_sha256':HELPER_SHA,'interval_precision_decimal_digits':120,
        'target':'E(1/16)*B_ind(1-10^-80,1-10^-80,1/2)*E(4)',
        'ordinary_clock_description':'p=q=log(2), a=log(8); E_p E_a B E_-a E_q. E(4) is an inverse-time proof suffix.',
        'cell_epsilon_exact':str(epsilon),'pair_target_exact':str(d*v),'leading_pair_control_v_exact':str(v),
        'complete_normalized_cap5_row_exact_rationals':list(map(str,row)),
        'scaled_nine_target_coordinate_enclosures_exact_rationals':list(map(enclosure,target)),
        'coordinate_infinity_upper_bound_exact_rational':str(bound),'certified_radius_exact_rational':str(eta),
        'original_ten_current_forest_target_source_rows_exact_equal':True,
        'cap3_nonordinary_diagonal_discrepancy_exact':str(cap3_discrepancy),
        'conclusion':'Conditional on the frozen box gate independent acceptance, this exact original-group shifted target has an actual positive eight-cell realization with one shared tuple inside the certified source cube and v as specified.',
        'not_claimed':['E(4) physical','explicit exact target realization tuple','ordinary-target G4 rival','cap-six equality','controlled allcap libraries or hazard budget']}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'status':result['status'],'bound_approx':mp.nstr(mp.mpf(bound.numerator)/bound.denominator,10),'eta_approx':mp.nstr(mp.mpf(eta.numerator)/eta.denominator,10),'target_nonordinary_at_three':True}))


if __name__=='__main__':main()
