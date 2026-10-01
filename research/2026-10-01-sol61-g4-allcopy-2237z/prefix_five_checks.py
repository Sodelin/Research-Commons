#!/usr/bin/env python3
"""Exact uniform five-input diagnostic cutoff for g=1/2 bigon vs ordinary edge."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import sys
import sympy as S

s,p=S.symbols("s p")
pstar=(7*s**3-6*s**2+12*s-8)/(24*s)
power=[S.Integer(2),s]
for k in range(2,11):
    power.append(S.expand(s*power[-1]-p*power[-2]))
b2=(s+2)/4
b3=(power[3]+3*s)/8
b4=power[6]/16+power[3]/4+3*p/8
b5=(power[10]+5*power[6]+10*p*power[2])/32
f=131*s**5+121*s**4-754*s**3+392*s**2+40*s-16
G=(25193*s**11+335944*s**10+118700*s**9-1709040*s**8
   +472080*s**7+2579136*s**6-2459712*s**5-1098240*s**4
   +1512960*s**3-240640*s**2+22528*s-4096)

def run():
    assert S.cancel((b3-b2**3)-(7*s**3-6*s**2+12*s-8-24*p*s)/64)==0
    assert S.cancel((b3-b2**3).subs(p,pstar))==0
    assert S.cancel((b4-b2**6).subs(p,pstar)+(s-2)**4*f/(55296*s**3))==0
    assert S.cancel((b5-b2**10).subs(p,pstar)+(s-2)**4*G/(254803968*s**5))==0
    assert S.cancel(s**2-4*pstar-(2-s)**3/(6*s))==0
    U,V,H=S.gcdex(f,G,s)
    assert H==1 and S.expand(U*f+V*G)==1
    lo,hi=S.Rational(151,100),S.Rational(152,100)
    assert S.Poly(f,s).count_roots(lo,hi)==1
    for poly in [7*s**3-6*s**2+12*s-8,7*s**3-30*s**2+36*s-8]:
        assert S.Poly(poly,s).count_roots(lo,hi)==0
        assert poly.subs(s,(lo+hi)/2)>0
    # A unique root in this exact interval, p(s)>0 and 1-s+p(s)>0,
    # together with discriminant>0 and 0<s<2, implies both arms lie in (0,1).
    roots=S.polys.polytools.intervals(f,eps=S.Rational(1,10**10))
    selected=[(a,m) for a,m in roots if a[0]>=lo and a[1]<=hi]
    assert len(selected)==1
    interval,multiplicity=selected[0]
    approx_s=sum(interval)/2
    approx_p=pstar.subs(s,approx_s)
    approx_d=(2-approx_s)**3/(6*approx_s)
    approx_x=(approx_s+S.sqrt(approx_d))/2
    approx_y=(approx_s-S.sqrt(approx_d))/2
    approx_delta5=S.N((-(s-2)**4*G/(254803968*s**5)).subs(s,approx_s),20)
    return {
      "status":"PASS","python":sys.version,"sympy":S.__version__,
      "source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
      "f":str(f),"G":str(G),
      "bezout_U":str(U),"bezout_V":str(V),"verified_U_f_plus_V_G":"1",
      "exact_witness":{"s_polynomial":str(f),"s_isolating_interval":["151/100","152/100"],
                      "s_root_count":1,"p_formula":str(pstar),
                      "arms":"roots of z^2-s*z+p(s)",
                      "positive_arm_checks":"p>0, (1-x)(1-y)>0, 0<s<2, discriminant>0",
                      "ordinary_survival":"(s+2)/4",
                      "leading_and_trailing_survivals":["1/2","1/2"]},
      "illustrative_approximations":{"s":str(S.N(approx_s,18)),
                                     "x":str(S.N(approx_x,18)),
                                     "y":str(S.N(approx_y,18)),
                                     "bare_delta_at_n5":str(approx_delta5)},
      "uniform_g_half_bigon_vs_edge_no_merger_cutoff":5,
      "cap4_no_merger_counterexample":True,
      "limits":["The exact witness is the polynomial with rational isolating interval, not decimals.",
                "This is a cutoff for the no-merger diagnostic, not a minimal complete-law copy cap.",
                "The colliding sources are not claimed equal on all four-input forest coordinates.",
                "No g!=1/2 universal cutoff and no arbitrary-chain numerical cutoff was computed."]
    }

if __name__=="__main__":
    print(json.dumps(run(),indent=2,sort_keys=True))
