"""Exact rational-input, outward-rounded certificate for a fixed finite nanowire pair.
Own checker; no floating-point acceptance, external solver, or model fitting.
Run with ordinary Python 3 (not python -O). No network or mutable external input.
"""
import hashlib, json
from pathlib import Path
from fractions import Fraction as F
from dyadic_interval import I, C, mm, P
import fixed_lead_scattering as model
from fixed_lead_scattering import scattering

if not __debug__:
    raise RuntimeError('Assertions are certificate guards; optimized Python is unsupported')

N=60; M=1000; t=F('25.08215'); lam=F('2.5'); B=F(2); Delta=F('.2')
a_base=F('49.37274649512004')
c_minus=F(1,100); c_plus=F(100)
# These are exact rational onsite coefficients, not uncertain decimal measurements.
a_minus=a_base+c_minus/(M*M); a_plus=a_base+c_plus/(M*M)


def check_particle_hole():
    J=[[0,0,0,-1],[0,0,1,0],[0,1,0,0],[-1,0,0,0]]
    identity=[[int(i==j) for j in range(4)] for i in range(4)]
    assert mm(J,J)==identity
    # Real linear basis matrices: tau_z, sigma_x, tau_x, spin-orbit hopping.
    mats=[[[1,0,0,0],[0,-1,0,0],[0,0,1,0],[0,0,0,-1]],
          [[0,0,1,0],[0,0,0,1],[1,0,0,0],[0,1,0,0]],
          [[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]],
          [[0,0,-1,0],[0,0,0,1],[1,0,0,0],[0,-1,0,0]]]
    for A in mats:
        assert mm(mm(J,A),J)==[[-x for x in row] for row in A]
    # Thus J H* J = -H, and the identity contact broadening preserves PHS.
    # At E=0, J r* J=r, so det(r) is real exactly.


def rational_bound(v,key):
    return F(v[key])


def main():
    assert P==1024
    assert (model.N,model.lam,model.B,model.Delta)==(N,lam,B,Delta)
    assert t>=F('25.08210') and t<=F('25.08220')
    check_particle_hole()
    output={'status':'PASS','precision_bits':P,
        'model':{'N':N,'M_meV':M,'t_meV':str(t),'lambda_meV':str(lam),
                 'B_label_meV':str(B),'Delta_meV':str(Delta),
                 'a_base_meV':str(a_base),'a_minus_meV':str(a_minus),'a_plus_meV':str(a_plus),
                 'lead_hopping_meV':'1','contact_hopping_meV':'1','internal_dissipation':'0'},
        'claims':{},'visibility':{}}
    for name,a,lo,hi in [('minus',a_minus,F(-203,1000),F(-202,1000)),
                         ('plus',a_plus,F(996,1000),F(997,1000))]:
        v=scattering(I(a),M,t)
        re,im=v['real'],v['imag']
        assert rational_bound(re,'lower')>lo
        assert rational_bound(re,'upper')<hi
        assert rational_bound(im,'lower')<=0<=rational_bound(im,'upper')
        output['visibility'][name]={'certified_open_interval':[str(lo),str(hi)],
                                   'real':re,'imag':im}
    gap=a_plus-a_minus
    assert gap==F(9999,100000000)
    assert gap==F('0.00009999')
    output['claims']={'energy_curve_sup_bound_meV':str(gap),
                      'common_midpoint_error_bound_meV':str(gap/2),
                      'scope':'Every common B value; the 512-setting menu is a subset. Fixed rational t only.',
                      'label_margin':'TV_minus < -1/10 and TV_plus > 1/10 at B=2.'}
    folder=Path(__file__).parent
    output['source_sha256']={name:hashlib.sha256((folder/name).read_bytes()).hexdigest()
       for name in ['dyadic_interval.py','fixed_lead_scattering.py','verify_finite_pair.py']}
    (folder/'FINITE-PAIR-RESULT.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],'rational_parameters':output['model'],
                      'claims':output['claims'],
                      'TV_minus_interval':['-0.203','-0.202'],
                      'TV_plus_interval':['0.996','0.997']},indent=2))

if __name__=='__main__':main()
