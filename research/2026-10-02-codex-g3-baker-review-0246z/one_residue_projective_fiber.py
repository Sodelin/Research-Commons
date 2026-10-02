"""Bounded exact projective-fiber probe for the Baker residue-rationality route.

Finite resultant/Sturm algebra only; log/source transfer is a separate proof.
"""
import json
import resource
import time
from pathlib import Path
import sympy as S

resource.setrlimit(resource.RLIMIT_AS, (600*1024**2, 600*1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
start = time.monotonic()
r, x = S.symbols("r x")
T4 = sum((5-j)*x**j for j in range(5))
T8 = sum((9-j)*x**j for j in range(9))
P = S.expand((r+2)*T4-T4.subs(x, r)*(x+2))
Q = S.expand((r+2)*T8-T8.subs(x, r)*(x+2))
P1, p_rem = S.div(P, x-r, x)
Q1, q_rem = S.div(Q, x-r, x)
assert p_rem == q_rem == 0
res = S.Poly(S.resultant(P1, Q1, x), r)
assert not res.is_zero
factor = S.factor(res.as_expr())
count = res.count_roots(0, 1)
record = {
    "status": "EXECUTED exact resultant/Sturm probe",
    "P": str(P), "Q": str(Q),
    "P_div_x_minus_r": str(P1),
    "Q_div_x_minus_r": str(Q1),
    "resultant_factorization": str(factor),
    "resultant_coefficients": [str(c) for c in res.all_coeffs()],
    "root_count_closed_0_1": int(count),
    "resultant_at_zero": str(res.eval(0)),
    "resultant_at_one": str(res.eval(1)),
    "seconds": time.monotonic()-start,
    "sympy": S.__version__,
    "scope": "Exact finite fiber algebra only. Baker/log rationality and source-positivity consequences require separate hand proof and review."
}
out = Path(__file__).with_name("one-residue-projective-fiber.json")
out.write_text(json.dumps(record, indent=2)+"\n")
print(json.dumps({k: record[k] for k in ['status','resultant_factorization','root_count_closed_0_1','resultant_at_zero','resultant_at_one','seconds']}))
