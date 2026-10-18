"""Exact algebra checks for the connected same-H Schur first variation.

Contributor: dot (OpenAI), 18 October 2026.
This checks finite identities, not all-volume/time P5 or the hand estimates.
"""
import sympy as s

i = s.I
I2 = s.eye(2)
X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -i], [i, 0]])
Z = s.diag(1, -1)
x, y, z = [s.kronecker_product(A, I2) for A in (X, Y, Z)]
u, v, w = [s.kronecker_product(I2, A) for A in (X, Y, Z)]
I4 = s.eye(4)
count = 0


def check(name, left, right):
    global count
    difference = s.simplify(left - right)
    if not isinstance(difference, s.MatrixBase):
        difference = s.simplify(difference.rewrite(s.exp))
    zero = s.zeros(*difference.shape) if isinstance(difference, s.MatrixBase) else 0
    assert difference == zero, (name, difference)
    count += 1
    print("PASS", name)


def comm(A, B):
    return A * B - B * A


def channel(A, K, F):
    return comm(A, F) * K - K.conjugate().T * comm(A, F)


def PX(F):
    reduced = s.Matrix(2, 2, lambda a, b: sum(F[2*a+j, 2*b+j] for j in range(2))/2)
    return s.kronecker_product(reduced, I2)


def QX(F):
    return F - PX(F)


def complex_symbol(name):
    real, imag = s.symbols(name + "_r " + name + "_i", real=True)
    return real + i * imag, real, imag


c, lam, eps = s.symbols("c lam eps", real=True)
e0 = s.symbols("e0", real=True)
k0 = c/2 + i*e0
C, Cr, Ci = complex_symbol("C")
S, Sr, Si = complex_symbol("S")
Cp, _, _ = complex_symbol("Cp")
Cm, _, _ = complex_symbol("Cm")
Sp, _, _ = complex_symbol("Sp")
Sm, _, _ = complex_symbol("Sm")
Pp, Pm = (I4+z)/2, (I4-z)/2
Cy, Sy = Pp*Cp+Pm*Cm, Pp*Sp+Pm*Sm
anchors = (x, y, z, u, v, w)
filters = (C*x+S*y*w, C*y-S*x*w, k0*z,
           Cy*u+Sy*v, Cy*v-Sy*u, k0*w)
H = lam*w+eps*z*w


def actual(F, hamiltonian, Ks):
    return s.simplify(i*comm(hamiltonian, F)
                      + sum((channel(A, K, F) for A, K in zip(anchors, Ks)), s.zeros(4)))


for j in range(3, 6):
    check("exterior channel annihilates root input " + str(j), channel(anchors[j], filters[j], x), s.zeros(4))
check("complete six-channel root formula", actual(x, H, filters),
      -4*(Cr+c/2)*x-(2*eps+4*Sr)*y*w)
check("exact root injection", QX(actual(x, H, filters)), -(2*eps+4*Sr)*y*w)
k1, k1r, k1i = complex_symbol("k1")
linear_filters = (k0*x+2*eps*k1*y*w, k0*y-2*eps*k1*x*w, k0*z,
                  filters[3], filters[4], filters[5])
root_derivative = s.diff(actual(x, H, linear_filters), eps).subs(eps, 0)
check("actual injection first derivative", QX(root_derivative), -2*(1+4*k1r)*y*w)

CL, CLr, CLi = complex_symbol("CL")
SL, SLr, SLi = complex_symbol("SL")
Kzero = (k0*x, k0*y, k0*z, CL*u+SL*v, CL*v-SL*u, k0*w)
for F, name in ((I4, "I"), (x, "X"), (y, "Y"), (z, "Z")):
    check("B0 annihilates root " + name, QX(actual(F, lam*w, Kzero)), s.zeros(4))
check("complete exterior thermal drift", actual(w, lam*w, Kzero), 8*SLi*I4-8*CLr*w)
check("root Y frozen rate", actual(y, lam*w, Kzero), -4*c*y)
RYZ = actual(y*w, lam*w, Kzero)
check("actual return on YZ", PX(RYZ), 8*SLi*y)
check("actual compression on YZ", QX(RYZ), -(4*c+8*CLr)*y*w)
check("fast input has zero root mean", PX(y*w), s.zeros(4))
check("root Y has norm-one spectrum", y*y, I4)

t = s.symbols("t", nonnegative=True)
first = -2*(1+4*k1r)*s.exp(-(4*c+8*CLr)*t)*PX(RYZ)
check("joint memory first variation", first,
      -2*(1+4*k1r)*8*SLi*s.exp(-(4*c+8*CLr)*t)*y)

a = s.symbols("a", positive=True)
cp = s.pi**2/(768*s.sqrt(2)*a)
gamma = 2*s.sqrt(2)*cp/s.pi
tau = 2*a/s.pi
b0 = s.pi/(4*s.sqrt(2))
check("original gamma tau", gamma*tau, s.Rational(1, 192))
check("noise floor", b0*gamma, cp/2)
check("maximum local strength over allowed interval", cp/100+cp/100, cp/50)
check("remaining original h margin", cp/2-cp/50, 12*cp/25)
check("remaining original memory-time margin", s.Rational(1, 96)-gamma*tau, s.Rational(1, 192))
check("noncancellation margin", 1-4*gamma*tau, s.Rational(47, 48))
check("spectral rate formula", 2*(c*s.exp(a*lam)+c*s.exp(-a*lam))*s.sech(2*a*lam),
      4*c*s.cosh(a*lam)*s.sech(2*a*lam))
check("spectral drift formula", 2*(c*s.exp(-a*lam)-c*s.exp(a*lam))*s.sech(2*a*lam),
      -4*c*s.sinh(a*lam)*s.sech(2*a*lam))
g, tau1, speed = s.symbols("gamma tau speed", positive=True)
check("single-filter influence integral algebra", 2*g*(1/(1-speed*tau1)-1),
      2*g*speed*tau1/(1-speed*tau1))
print(f"PASS: {count} exact finite algebra checks. Hand proofs and all-order gates remain separate.")
