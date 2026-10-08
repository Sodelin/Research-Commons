"""Exact derived constants for a source-word count obstruction.

Reads the authenticated inherited rational certificate as data, not executable
code. Does not run a source with 2**200 cells or expand its observed fractions.
The all-parameter count theorem and source-to-original transfer are hand proofs.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import platform


CERTIFICATE_SHA = "2a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118"
CHECKS = 0


def require(condition):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(f"derived constant check {CHECKS} failed")


def sparse_value(record, q):
    return sum(F(c) * (1-q**l)
               for c, l in zip(record["c"], record["exponents"]))


def log_loss_interval(z, terms=7):
    """Exact enclosure of -log(1-z), for 0<=z<1."""
    require(0 <= z < 1)
    lower = sum(z**k/k for k in range(1, terms+1))
    upper = lower + z**(terms+1)/((terms+1)*(1-z))
    return lower, upper


def scale_interval(a, interval):
    values = [a*interval[0], a*interval[1]]
    return min(values), max(values)


def sum_intervals(intervals):
    captured = list(intervals)
    return (sum(x[0] for x in captured), sum(x[1] for x in captured))


def ceil_rational(x):
    return -((-x.numerator)//x.denominator)


def main():
    # Locate repository from the additive packet, without importing prior code.
    repo = Path(__file__).resolve().parents[3]
    source = repo / "research/2026-10-01-sol61-g3-boundary-resume-2124z/paired-normal-certificate.json"
    captured = source.read_bytes()
    source_sha = hashlib.sha256(captured).hexdigest()
    require(source_sha == CERTIFICATE_SHA)
    data = json.loads(captured)
    v = data["constants"]
    B0, B1, delta, gamma, Q, p0, eta, Cstar = (
        F(v[k]) for k in ["B0", "B1", "delta", "gamma", "Q", "p0",
                         "root_interval_half_width", "C_star"])
    f_out = F(v["outside_U_F0_lower_bound"])
    fpp = F(data["normal_records"]["F0"]["F_second_derivative_at_one"])
    r, u = F(1, 2), F(1, 2)+eta
    kappa = min(f_out/12, fpp*Q**3/12)
    C0 = min(Cstar, gamma*(1-u)/(4*B1*(B0/delta)**2))
    K, L = 2*B1/delta**2, 6+B0*p0/kappa
    require(0 < eta <= F(1, 32))
    require(u < Q < 1)
    require(0 < p0 <= F(1, 2))
    require(p0 <= f_out/(2*B0))
    require(C0 <= p0*(1-Q))
    require(2*B1*(B0/delta)**2*C0/(1-u) <= gamma/2)
    require(kappa > 0 and K > 0 and L > 0)
    require(C0 == Cstar)
    for rec in data["normal_records"].values():
        ls, cs = rec["exponents"], [F(x) for x in rec["c"]]
        require(sum(cs) == 1)
        require(sum(c*l for c, l in zip(cs, ls)) == 0)
        require(sum(abs(c) for c in cs) == F(rec["coefficient_L1"]))
        require(sparse_value(rec, r) == 0)
    a0 = sparse_value(data["normal_records"]["F0"], r*r)
    a1 = sparse_value(data["normal_records"]["F1"], r*r*r)
    require(a0 > 0 and a1 > 0)
    require(sparse_value(data["normal_records"]["F1"], r*r) == 0)
    require(a1 == F(v["T13_at_r"]))
    require(gamma == a1/12)

    N0 = 2**200
    theta_bar = F(4, 2**175)
    tau_bar = theta_bar+F(1, N0)
    p_bar = tau_bar/N0
    d = F(5, 8)
    loss_upper = theta_bar+F(1, 2*N0)+tau_bar*p_bar/(2*(1-p_bar))
    require(0 < p_bar <= p0)
    require(loss_upper < C0)
    require(B0*p_bar/(3*(1-p_bar)) < a0/2)
    require(d-2*p_bar/(1-p_bar) > 0)
    rate_squared = (gamma*(d-2*p_bar/(1-p_bar))**3 /
                    (2*L**3*(a1/3+B1*p_bar/2+K*B0**2*tau_bar)))
    require(rate_squared > F(1, 128**2))

    # Exact polynomial identity behind the all-p near-one defect bound.
    for p in [F(1, 97), F(1, 2), F(96, 97)]:
        for q in [F(1, 101), F(1, 2), F(100, 101)]:
            f1 = 1-p+p*q
            f3 = 1-p+p*q**3
            require(f3-f1**3 == p*(1-p)*(1-q)**2*(2+q-p*(1-q)))
    # These nine substitutions support the identity; its general factorization
    # is supplied in the hand proof, rather than inferred from this finite list.

    # Certified log enclosures for three compact rational source descriptions.
    # No power f_l**N is expanded and no N-cell source process is executed.
    theta_bounds = scale_interval(2, log_loss_interval(F(1, 2**175)))
    fixtures = []
    exponents = [1, 3, 6, 10, 15, 21]
    for exponent in [200, 220, 240]:
        N = 2**exponent
        ceiling_low = ceil_rational(theta_bounds[0]*N)
        ceiling_high = ceil_rational(theta_bounds[1]*N)
        require(ceiling_low == ceiling_high)
        p = F(ceiling_low, N*N)
        require(0 < p <= p_bar and N*p <= tau_bar)
        factor = {l:log_loss_interval(p*(1-r**l)) for l in exponents}
        alpha = scale_interval(N, sum_intervals(
            scale_interval(F(c), factor[l]) for c,l in zip(
                data["normal_records"]["F0"]["c"],
                data["normal_records"]["F0"]["exponents"])))
        beta = scale_interval(N, sum_intervals(
            scale_interval(F(c), factor[l]) for c,l in zip(
                data["normal_records"]["F1"]["c"], exponents)))
        defect = scale_interval(N, sum_intervals(
            [scale_interval(3, factor[1]), scale_interval(-1, factor[3])]))
        require(alpha[1] < 0)
        P_lower = (defect[0]-alpha[1]/kappa)/L
        E_upper = beta[1]+K*max(abs(alpha[0]), abs(alpha[1]))**2
        require(P_lower > 0 and E_upper > 0)
        require(gamma*P_lower**3/2 > F(N*N, 128**2)*E_upper)
        fixtures.append({"N":"2^"+str(exponent),
                         "ceil_theta_times_N":str(ceiling_low),
                         "factor_probability":str(p),
                         "certified_minimum_factor_count_at_least":"ceil(N/128)",
                         "expanded_observed_moments":False})
    result = {"status":"PASS", "checks":CHECKS,
              "python":platform.python_version(),
              "source_certificate_sha256":source_sha,
              "source_buffer_used_as":"JSON data only; captured once and hashed",
              "uniform_rate_start":"2^200", "uniform_minimum_count":"ceil(N/128)",
              "C0_equals_inherited_C_star":C0==Cstar,
              "rate_squared_exact":str(rate_squared),
              "fixtures":fixtures,
              "limits":"Exact derived rational constants and finite log intervals; all-parameter inequalities, integer-count argument and original all-core transfer are hand proofs. No source execution, large graph, expanded observation fractions, QE, native binary or Lean."}
    destination = Path(__file__).with_name("log-product-count-test-receipt.json")
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status":result["status"], "checks":CHECKS,
                      "fixtures":len(fixtures),
                      "uniform_minimum_count":result["uniform_minimum_count"]}))


if __name__ == "__main__":
    main()
