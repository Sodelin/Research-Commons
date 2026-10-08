"""All-degree symbolic diagonal jets and exact fixed-body tangent controls.

This does not search a source fibre or treat a diagonal match as a full match.
Original source bytes are captured and hashed before the bounded cap-four
full-kernel polynomial control. No inherited imports or pycache writes.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import comb, factorial
from pathlib import Path
import json
import types
import sympy as sp

ROOT = Path(__file__).resolve().parents[4]
FOREST = "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py"
FOREST_SHA = "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884"
EPPF = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py"
EPPF_SHA = "a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b"

def captured(path, pin):
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == pin
    module = types.ModuleType("captured_" + path.stem)
    module.__file__ = str(path)
    exec(compile(raw, str(path), "exec"), module.__dict__)
    return module, {"path": str(path.relative_to(ROOT)), "sha256": pin, "bytes": len(raw)}

def fall(n, k):
    return sp.prod(n-j for j in range(k))

def binpoly(n, k):
    return fall(n, k) * sp.Rational(1, factorial(k))

def newton_pair_power(p):
    """binom(j(j-1)/2,p)=sum_r c[r](j)_r, exactly as polynomials."""
    result = {}
    for r in range(2*p+1):
        val = sum(F((-1)**(r-s)*comb(r,s)*comb(s*(s-1)//2,p))
                  for s in range(r+1)) / factorial(r)
        if val:
            result[r] = val
    return result

def log_coefficients(coefficients):
    # b0=1; coefficient of formal log through degree four.
    b = coefficients
    return [sp.Integer(0), b[1], b[2]-b[1]**2/2,
            b[3]-b[1]*b[2]+b[1]**3/3,
            b[4]-b[1]*b[3]-b[2]**2/2+b[1]**2*b[2]-b[1]**4/4]

def body_row(n):
    x=y=F(1,2); g=F(2,3); h=1-g
    b=dx=dy=dg=F(0)
    for j in range(n+1):
        px, py = comb(j,2), comb(n-j,2)
        w = F(comb(n,j))*g**j*h**(n-j)*x**px*y**py
        b += w
        dx += w*px/x
        dy += w*py/y
        dg += w*(F(j)/g-F(n-j)/h)
    return [F(comb(n,2)), dx/b, dy/b, dg/b, F(comb(n,3)), F(comb(n,4))]

def main():
    n, g, ell, z = sp.symbols("n g ell z")
    lam = n*(n-1)/2
    newton = [newton_pair_power(p) for p in range(4)]
    balanced = []
    for k in range(4):
        coefficient = 0
        for p in range(k+1):
            q = k-p
            for r, cr in newton[p].items():
                for s, cs in newton[q].items():
                    coefficient += (-1)**k * sp.Rational(cr.numerator,cr.denominator) * sp.Rational(cs.numerator,cs.denominator) * fall(n,r+s) * g**(r-p) * (1-g)**(s-q)
        balanced.append(sp.factor(coefficient))
    expected = [(-1)**k*binpoly(lam,k) for k in range(4)]
    expected[3] -= binpoly(n,3)
    assert all(sp.expand(a-b)==0 for a,b in zip(balanced,expected))

    # Actual rare family x=1-ell, g=t, y=1-z*t/(1-t).
    rare = []
    for k in range(5):
        coefficient = 0
        for j in range(k+1):
            m = n-j
            lam_m = m*(m-1)/2
            first_exp = m-lam_m
            for p in range(k-j+1):
                q = k-j-p
                coefficient += binpoly(n,j)*(1-ell)**(j*(j-1)//2)*(-1)**(p+q)*binpoly(first_exp,p)*binpoly(lam_m,q)*(1+z)**q
        rare.append(sp.factor(coefficient))
    normalized = log_coefficients(rare)
    # Exact pair survival beta=1-z*t-(ell-z)*t^2.
    beta = [sp.Integer(1),-z,z-ell,sp.Integer(0),sp.Integer(0)]
    log_beta = log_coefficients(beta)
    normalized = [sp.factor(a-lam*b) for a,b in zip(normalized,log_beta)]
    assert normalized[:3] == [0,0,0]
    P = sp.factor(normalized[3].subs(n,3))
    Q3 = sp.factor(normalized[4].subs(n,3))
    Q4 = sp.factor(normalized[4].subs(n,4)-4*Q3)
    assert sp.expand(P-(3*(ell-z)**2-ell**3))==0
    assert sp.expand(normalized[3]-binpoly(n,3)*P)==0
    assert sp.expand(normalized[4]-binpoly(n,3)*Q3-binpoly(n,4)*Q4)==0

    forest, forest_pin = captured(ROOT/FOREST, FOREST_SHA)
    eppf, eppf_pin = captured(ROOT/EPPF, EPPF_SHA)
    alg = forest.ForestAlgebra(4)
    polys = alg.cell_polynomials("independent")
    low_full_controls = 0
    for (arity,f), poly in zip(alg.coords, polys):
        edge = forest.edge_polynomials(arity)[f]
        for degree in range(3):
            Bcoef = 0
            for (px,py,pg,pa), c in poly.items():
                for i in range(degree+1):
                    j = degree-i
                    if i<=px and j<=py:
                        Bcoef += sp.Rational(c.numerator,c.denominator)*comb(px,i)*comb(py,j)*(-1)**degree*g**(pg-i)*(1-g)**(-j)
            Ecoef = sum((sp.Rational(c.numerator,c.denominator)*comb(e,degree)*(-1)**degree for e,c in edge.items() if e>=degree),sp.Integer(0))
            assert sp.cancel(Bcoef-Ecoef)==0,(arity,f,degree)
            low_full_controls += 1

    rows = [body_row(k) for k in range(2,7)]
    body_matrix = sp.Matrix([[sp.Rational(v.numerator,v.denominator) for v in row[:4]] for row in rows])
    assert body_matrix.rank()==3
    normal = [-260,8910,-10815,3842]
    assert all(sum(F(c)*r[j] for c,r in zip(normal,rows[:4]))==0 for j in range(4))
    assert sum(F(c)*r[4] for c,r in zip(normal,rows[:4]))==4070
    assert all(r[2]==2*r[0]-3*r[1] for r in rows)
    cubic_minor = sp.Matrix([[sp.Rational(r[j].numerator,r[j].denominator) for j in (0,1,3,4)] for r in rows[:4]])
    quartic_minor = sp.Matrix([[sp.Rational(r[j].numerator,r[j].denominator) for j in (0,1,3,4,5)] for r in rows])
    assert cubic_minor.det()!=0 and quartic_minor.det()!=0
    # Explicit uniform diagonal remainder bounds. Choose the rare arm with
    # g<=1/2 (source arm exchange); strict balance implies d<g and h>=1/2.
    remainder_bounds=[]
    for arity in range(2,6):
        lam_k=comb(arity,2)
        basis=[newton_pair_power(p) for p in range(lam_k+1)]
        raw_bound=F(0)
        for p in range(lam_k+1):
            for q in range(lam_k+1):
                if p+q<4:
                    continue
                for rr,cr in basis[p].items():
                    for ss,cs in basis[q].items():
                        if rr+ss<=arity:
                            assert p<=rr or rr>=4
                            raw_bound += abs(cr*cs)*F(factorial(arity),factorial(arity-rr-ss))*2**max(q-ss,0)
        ordinary_bound=sum((F(comb(lam_k,k)) for k in range(4,lam_k+1)),F(0))
        K=raw_bound+ordinary_bound
        Klog=(1+2*lam_k)*K+2*lam_k*comb(arity,3)
        remainder_bounds.append({"n":arity,"raw_diagonal_d4_remainder_bound":str(K),
                                 "log_normalized_d4_remainder_bound":str(Klog),
                                 "domain_d_upper_bound":str(F(1,2*lam_k))})
    covector_remainder=sum(F(abs(c))*F(r["log_normalized_d4_remainder_bound"])
                            for c,r in zip(normal,remainder_bounds))
    full_tv_bounds=[]
    for arity in range(5):
        bound=F(0)
        for left in range(arity+1):
            right=arity-left
            for pa in forest.edge_polynomials(left).values():
                for pb in forest.edge_polynomials(right).values():
                    for ex,ca in pa.items():
                        for ey,cb in pb.items():
                            for pp in range(ex+1):
                                for qq in range(ey+1):
                                    if pp+qq>=3:
                                        assert pp<=left or left>=4
                                        bound+=comb(arity,left)*abs(ca*cb)*comb(ex,pp)*comb(ey,qq)*2**max(qq-right,0)
        bound+=sum((abs(c)*comb(e,k) for p in forest.edge_polynomials(arity).values()
                    for e,c in p.items() for k in range(3,e+1)),F(0))
        full_tv_bounds.append(bound/2)
    full_cap4_tv_constant=max(full_tv_bounds)
    aa,xx,yy,gg,rr=sp.symbols("a x y gamma r")
    bb=[sum(binpoly(k,j)*gg**j*(1-gg)**(k-j)*xx**(j*(j-1)//2)*yy**((k-j)*(k-j-1)//2)
            for j in range(k+1)) for k in (2,3,4)]
    VV=lambda s:(2-3*s+s**3)/6
    cc=2*(gg**2*(1-gg)**2*(1-xx)*(1-yy)-gg**3*(1-gg)*VV(xx)-gg*(1-gg)**3*VV(yy))
    full_body=sp.Matrix([aa*rr*bb[0],aa**3*rr**3*bb[1],aa**6*rr**6*bb[2],aa**6*rr*cc,aa**6*(1-rr)*cc])
    body_jac=full_body.jacobian([aa,xx,yy,gg,rr]).subs({xx:sp.Rational(1,2),yy:sp.Rational(1,2),gg:sp.Rational(2,3)})
    body_det=sp.factor(body_jac.det())
    assert body_det==-sp.Rational(17,816293376)*aa**21*rr**10
    for k in range(2,9):
        assert eppf.diag(k,F(1,2),F(1,2),F(2,3))==sum((F(comb(k,j))*F(2,3)**j*F(1,3)**(k-j)*F(1,2)**(comb(j,2)+comb(k-j,2)) for j in range(k+1)),F(0))
    branch_controls=[]
    for rz in (F(3,8),F(9,8)):
        subs={ell:sp.Rational(3,4),z:sp.Rational(rz.numerator,rz.denominator)}
        assert P.subs(subs)==0
        branch_controls.append({"ell":"3/4","z":str(rz),"P":str(P.subs(subs)),"Q3":str(Q3.subs(subs)),"Q4":str(Q4.subs(subs))})
    report={
        "status":"PASS", "scope":"All-degree symbolic source coefficient identities plus bounded exact tangent/full-cap4 controls; no full-return witness",
        "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
        "arithmetic":"Fraction and exact SymPy polynomial identities", "sympy_version":sp.__version__,
        "executed_provider_bytes":[forest_pin,eppf_pin],
        "balanced_diagonal_coefficients_d0_through_d3":[str(c) for c in balanced],
        "balanced_normalized_cubic":"-binom(n,3)*d^3",
        "rare_normalized_cubic_P":str(P),"rare_normalized_quartic_Q3":str(Q3),"rare_normalized_quartic_Q4":str(Q4),
        "body_target":{"x":"1/2","y":"1/2","g":"2/3"},
        "body_rows_n2_through_n6":[[str(x) for x in r] for r in rows],
        "body_row_columns":["lambda_n","dlogB_dx","dlogB_dy","dlogB_dg","binom_n_3","binom_n_4"],
        "body_tangent_rank":3,"all_degree_body_derivative_identity":"dlogB_dy=2*lambda_n-3*dlogB_dx; hand pairing proof required",
        "n2_through_n5_integer_normal":normal,"normal_cubic_pairing":4070,
        "cubic_augmented_minor_det":str(cubic_minor.det()),"quartic_augmented_minor_det":str(quartic_minor.det()),
        "full_cap_four_balanced_kernel_d0_d1_d2_controls":low_full_controls,
        "newton_coefficients_p0_through_p3":[{str(k):str(v) for k,v in b.items()} for b in newton],
        "uniform_balanced_diagonal_remainder_bounds":remainder_bounds,
        "integer_normal_log_remainder_constant":str(covector_remainder),
        "uniform_full_cap_four_balanced_tv_constant":str(full_cap4_tv_constant),
        "full_cap_four_body_jacobian_variables":["a","x","y","gamma","r"],
        "full_cap_four_body_jacobian_coords":["b2","b3","b4","c","h"],
        "full_cap_four_body_det_for_arbitrary_positive_a_r":str(body_det),
        "rare_cubic_zero_branch_controls":branch_controls,
        "claim_limits":["Uniform remainder/local inverse are hand arguments", "Only local fixed-body retuning addressed", "Mixed unbalanced leading sources remain possible", "No all-cap actual common-zero construction", "No original full-menu G4 closure"]}
    print(json.dumps(report,indent=2)+"\n",end="")

if __name__=="__main__":
    main()
