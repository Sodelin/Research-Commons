"""Bounded exact algebra checks only; not a P5 proof or model simulation."""
import sympy as s


def add(*polys):
    out = {}
    for p in polys:
        for word, coeff in p.items():
            out[word] = s.expand(out.get(word, 0) + coeff)
    return {w: c for w, c in out.items() if c != 0}


def scale(c, p):
    return {w: s.expand(c * a) for w, a in p.items() if c * a != 0}


def mul(p, q):
    out = {}
    for u, a in p.items():
        for v, b in q.items():
            out[u + v] = s.expand(out.get(u + v, 0) + a * b)
    return {w: c for w, c in out.items() if c != 0}


def comm(p, q):
    return add(mul(p, q), scale(-1, mul(q, p)))


def cyclic(p):
    out = {}
    for w, a in p.items():
        key = min(w[j:] + w[:j] for j in range(len(w))) if w else w
        out[key] = s.expand(out.get(key, 0) + a)
    return {w: a for w, a in out.items() if a != 0}


A, B, D, F = ({(x,): s.Integer(1)} for x in "ABDF")
K = add(B, scale(s.I, D))
Kd = add(B, scale(-s.I, D))
AF = comm(A, F)
RstarF = add(mul(AF, K), scale(-1, mul(Kd, AF)))
V = add(comm(K, A), comm(A, Kd))
assert add(V, scale(-2 * s.I, comm(D, A))) == {}
lhs = mul(F, RstarF)
# [A,F]^dagger=-[A,F], since A,F are Hermitian.
rhs = add(mul(AF, comm(B, F)), scale(s.Rational(1, 2), mul(V, mul(F, F))))
assert cyclic(add(lhs, scale(-1, rhs))) == {}
print("PASS: exact unitality-defect and cyclic energy identities")

I = s.eye(2)
X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -s.I], [s.I, 0]])
Z = s.diag(1, -1)
for P, expected in [(I, 0), (X, 8), (Y, 8), (Z, 8)]:
    energy = sum(s.trace((Q * P - P * Q).conjugate().T * (Q * P - P * Q)) / 2
                 for Q in (X, Y, Z))
    assert s.simplify(energy - expected) == 0
print("PASS: on-site Hilbert-Schmidt gradient factor eight")

gamma, tau, u = s.symbols("gamma tau u", positive=True)
# Substitute a*tau=1-u, u>0, so the infinite integral converges.
t = s.symbols("t", nonnegative=True)
integrand = gamma / tau * (s.exp(-u * t / tau) - s.exp(-t / tau))
val = s.integrate(integrand, (t, 0, s.oo))
assert s.simplify(val - gamma * (1 - u) / u) == 0
assert s.Rational(48, 8) == 6
assert s.Integer(6) < 9  # sqrt(6)/24 < 1/8, exact squaring.
b = s.symbols("b", positive=True)
assert s.simplify(gamma * (b / 8) / (1 - b / 8) - gamma * b / (8 - b)) == 0
assert s.Rational(1) - s.Rational(1, 7) == s.Rational(6, 7)
print("PASS: envelope integral and explicit-box arithmetic")
print("All checks passed. Scope: exact finite algebra only; no P5 closure.")
