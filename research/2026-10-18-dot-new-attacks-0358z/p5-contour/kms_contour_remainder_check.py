"""Exact matrix/algebra checks for KMS-CONTOUR-REMAINDER-0410Z.md.

This reuses the full-filter coefficient parameterization of accepted note24.
It does not verify contour analysis, bath admission, infinite-volume estimates,
or the original P5 claim. No numerical filter truncation is made.
"""
import hashlib
import json
from pathlib import Path
import platform
import sympy as s

I = s.eye(2)
X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -s.I], [s.I, 0]])
Z = s.diag(1, -1)
kron = s.kronecker_product
II = s.eye(4)
P = (kron(Z, I) + kron(X, X)) / s.sqrt(2)
Qb = (kron(Z, I) - kron(X, X)) / s.sqrt(2)
Tb = kron(Y, X)
r0, e, r, f, d, theta = s.symbols('r0 e r f d theta', real=True)
k0 = r0 + s.I * e
C = r + s.I * f
D = d - s.I * theta * r
den = 1 - theta**2
W = II - theta * P
Wi = (II + theta * P) / den
rhoG = W / 4
Delta = f - theta * d - e
axes = [kron(A, I) for A in (X, Y, Z)] + [kron(I, A) for A in (X, Y, Z)]
checks = []


def eq(label, lhs, rhs):
    diff = lhs - rhs
    entries = list(diff) if isinstance(diff, s.MatrixBase) else [diff]
    if not all(s.simplify(v) == 0 for v in entries):
        raise AssertionError((label, diff))
    checks.append(label)


def comm(A, B):
    return A * B - B * A


def filt(A):
    Ac = (A + P * A * P) / 2
    Aa = (A - P * A * P) / 2
    return k0 * Ac + C * Aa - s.I * D * P * Aa


def dissipator(A, V):
    K = filt(A)
    return comm(K * V - V * K.adjoint(), A)


def rem_flux(A, V):
    q = filt(A) - k0 * A
    return W * q.adjoint() * Wi * V - V * q.adjoint()


def rem_map(V):
    return sum((comm(rem_flux(A, V), A) for A in axes), s.zeros(4))


eq('reference inverse', W * Wi, II)
eq('Hamiltonian fixes reference', comm(P, rhoG), s.zeros(4))
full_first = sum((dissipator(A, rhoG) for A in axes), s.zeros(4))
eq('actual first derivative from note24', full_first, -Delta * Tb)
eq('summed Q remainder vanishes initially', rem_map(rhoG), s.zeros(4))

expected = (4 * (d - theta * (f - e) + s.I * r0 * theta) / den) * Qb
expected += (8 * (r0 - r * den + s.I * Delta) / den) * Tb
eq('summed Q remainder on reached direction, full matrix', rem_map(Tb), expected)
eq('summed Q remainder time derivative', rem_map(full_first), -Delta * expected)
coef_Q = s.simplify(s.trace(Qb * expected) / 4)
eq('strictly nonzero imaginary Q coefficient', s.im(coef_Q), 4 * r0 * theta / den)

# The split is algebraic for arbitrary input, not just the Gibbs input.
for a, A in enumerate(axes):
    q = filt(A) - k0 * A
    B = q - W * q.adjoint() * Wi
    for name, V in [('I', II), ('P', P), ('Q', Qb), ('T', Tb), ('X1', kron(X, I))]:
        eq(f'exact Q flux split {a} {name}', q * V - V * q.adjoint(), B * V + rem_flux(A, V))

# At H=0 the unsusbtracted modular remainder contains the real frozen noise.
b, c = s.symbols('b c', real=True)
A, V = Z, X
Kzero = (b + s.I * c) * A
Czero = -2 * c * A
local_piece = -s.I * comm(Czero * V, A)
remainder = comm(comm(Kzero.adjoint(), V), A)
eq('H=0 finite-strip piece', local_piece, 2 * s.I * c * (A * V * A - V))
eq('H=0 remainder carries real damping', remainder, 2 * (b - s.I * c) * (A * V * A - V))
eq('H=0 exact sum', local_piece + remainder, 2 * b * (A * V * A - V))

path = Path(__file__)
print(json.dumps({
    'status': 'PASS',
    'check_count': len(checks),
    'checks': checks,
    'python_version': platform.python_version(),
    'sympy_version': s.__version__,
    'checker_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    'scope': 'Exact finite matrix identities only; source-admission and strip proof are hand arguments.'
}, indent=2))
