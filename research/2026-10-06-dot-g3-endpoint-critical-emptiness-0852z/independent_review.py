"""New bounded reviewer reconstruction, not execution of the author's scripts."""
import resource
resource.setrlimit(resource.RLIMIT_CPU, (60, 60))
resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
import hashlib, json, math, sys, time
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix

start = time.monotonic()
root = Path(__file__).resolve().parent
pins = {
    'stage1-result.json': '9f139fad69e095bb0721234ecd246dd1b1cc26dae4c05503f3670712d770bd69',
    'stage2-result.json': '6ee7b14b67796b1a25aee02a623bce2538216ba894775399e5b09c420f76c20e',
    'stage3-result.json': '091f24d4160c296f70424e0739c70ad360adc9fd8581898663260599e210d252',
}
data = {}
for name, want in pins.items():
    raw = (root/name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == want
    data[name] = json.loads(raw)

def mul(a, b):
    out = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            key = (i+k, j+l)
            out[key] = out.get(key, 0) + x*y
    return {key: value for key, value in out.items() if value}

def add_scaled(out, a, scale):
    for key, value in a.items():
        out[key] = out.get(key, 0) + scale*value

lam = (1, 3, 6, 10, 15, 21)
c = (297, -275, 154, -54, 11, -1)
assert sum(c) == 132
assert all(sum(ci*li**k for ci, li in zip(c, lam)) == 0 for k in range(1, 6))
f = [{(0,0):1, (1,0):-1, (1,l):1} for l in lam]
p0, q0 = {}, {}
for i in range(6):
    product = {(0,0):1}
    for j in range(6):
        if i != j:
            product = mul(product, f[j])
    add_scaled(p0, mul(product, {(0,0):1, (0,lam[i]):-1}), c[i])
    add_scaled(q0, mul(product, {(0,lam[i]-1):1}), c[i]*lam[i])

p, q = s.symbols('p q')
P0 = s.Poly.from_dict(p0, (p,q), domain=s.ZZ)
Q0 = s.Poly.from_dict(q0, (p,q), domain=s.ZZ)
P = P0.exquo(s.Poly((q-1)**6, p,q, domain=s.ZZ))
Q = Q0.exquo(s.Poly((1-p)*(q-1)**5, p,q, domain=s.ZZ))
for name, poly in [('P', P), ('Q', Q)]:
    expected = {tuple(m):int(v) for m,v in data['stage1-result.json']['polynomials'][name]['terms']}
    assert poly.as_dict() == expected, name
print('PASS independently convolved source derivative polynomials and exact strict-domain divisions', flush=True)

# Independent Sylvester matrix construction and exact DomainMatrix determinant.
a = s.Poly(P.as_expr(), p).all_coeffs()
b = s.Poly(Q.as_expr(), p).all_coeffs()
m, n = len(a)-1, len(b)-1
rows = []
for shift in range(n):
    rows.append([0]*shift + a + [0]*(n-1-shift))
for shift in range(m):
    rows.append([0]*shift + b + [0]*(m-1-shift))
dm = DomainMatrix.from_Matrix(s.Matrix(rows))
res = s.Poly(dm.domain.to_sympy(dm.det()), q, domain=s.ZZ)
expected_res = [int(v) for v in data['stage2-result.json']['coefficients_descending']]
assert list(map(int, res.all_coeffs())) == expected_res
print('PASS alternate exact 9x9 Sylvester determinant, degree', res.degree(), flush=True)

# Separate integer-only endpoint removal and Mobius coefficient transform.
coeff = expected_res[:]
content = math.gcd(*coeff)
coeff = [v//content for v in coeff]
q_zero_mult = 0
while coeff[-1] == 0:
    coeff.pop()
    q_zero_mult += 1
assert sum(coeff) != 0  # no q=1 root
degree = len(coeff)-1
ascending = coeff[::-1]
mobius = [sum(ascending[k]*math.comb(degree-k, j-k) for k in range(j+1))
          for j in range(degree+1)]
stage3 = data['stage3-result.json']
assert coeff == list(map(int, stage3['reduced_coefficients_descending']))
assert mobius[::-1] == list(map(int, stage3['mobius_coefficients_descending']))
nonzero = [v for v in mobius if v]
assert nonzero and (all(v>0 for v in nonzero) or all(v<0 for v in nonzero))
assert stage3['removed_endpoint_multiplicities'] == {'0':q_zero_mult, '1':0}
for name, want in pins.items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest() == want
out = {
    'status': 'PASS_NEW_INDEPENDENT_ENDPOINT_K1_EMPTY_CERTIFICATE',
    'new_execution': True,
    'historical_execution_recreated': False,
    'python': sys.version,
    'sympy': s.__version__,
    'input_sha256': pins,
    'normal_moment_identities': True,
    'independent_integer_convolution': True,
    'exact_divisions_and_all_coefficients_match': True,
    'alternate_sylvester_determinant_all_coefficients_match': True,
    'resultant_degree': int(res.degree()),
    'removed_q_zero_multiplicity': q_zero_mult,
    'removed_q_one_multiplicity': 0,
    'reduced_degree': degree,
    'integer_mobius_coefficients_match': True,
    'all_nonzero_mobius_coefficients_one_sign': True,
    'strict_resultant_root_count': 0,
    'scope': 'No strict critical pair for the fixed rational r=1 normal; no source simulation or general G3 decision.',
    'seconds': time.monotonic()-start,
}
(root/'independent-review-result.json').write_text(json.dumps(out, indent=2)+'\n')
print(out['status'], out['seconds'], flush=True)
