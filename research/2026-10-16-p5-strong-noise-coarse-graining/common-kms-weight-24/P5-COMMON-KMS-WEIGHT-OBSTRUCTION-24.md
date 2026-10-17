# P5: no common KMS weight for the actual two-site generator and a deleted-site generator

17 October 2026. dot (OpenAI). Hand-proof candidate for independent review.

## Result

The actual full-filter two-site Redfield family below has no trace-one Hermitian operator stationary under both its full generator and the generator obtained by deleting all three bath channels anchored at site 1. Consequently, no faithful density matrix makes both Heisenberg evolutions contractive in the same sandwich KMS norm. This conclusion includes any actual faithful stationary state of the full generator, whose existence is established below for explicit admitted parameters.

The bare-Gibbs failure was already recorded in note09. The additional result here is that replacing the bare Gibbs weight by the true stationary weight cannot repair this particular common-weight, deleted-site contraction mechanism. This is not a counterexample to the fixed-support P5 error bound, and does not rule out different weights for different generators, a modified decomposition, controlled norm growth, or another response estimate. No novelty or Lean verification is claimed.

## 1. Actual generator and deletion convention

Let a,c>0. Use six independent on-site Pauli bath channels with the same covariance

    Phi(s) = c/(2a) sech[pi(s+i a/2)/(2a)],
    J_bath(omega) = c exp(a omega/2) sech(a omega).

The inverse temperature is a. The positive spectrum, bath KMS relation and envelope constants are inherited from the [reviewed physical bath](https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md):

    tauB = 2a/pi, gamma = 2 sqrt(2)c/pi, b0 = pi/(4 sqrt(2)),
    |Phi(s)| <= (gamma/tauB) exp(-|s|/tauB),
    Re integral_0^infinity Phi(s) ds = c/2 = b0 gamma.

Set lambda>0 and

    H = lambda(Z_1 + X_1 X_2),  Omega = sqrt(2) lambda,
    P = (Z_1 + X_1 X_2)/sqrt(2),
    Q = (Z_1 - X_1 X_2)/sqrt(2),  T = Y_1 X_2.

Thus H=Omega P, P^2=Q^2=T^2=I, and {I,P,Q,T} is trace-orthogonal, with Tr(B^2)=4 for each basis element B.

For each A in {X_1,Y_1,Z_1,X_2,Y_2,Z_2}, retain its full one-sided bath filter:

    K_A = integral_0^infinity Phi(s) exp(-iHs) A exp(iHs) ds,
    D_A(rho) = K_A rho A - A K_A rho + A rho K_A^dagger - rho K_A^dagger A.

Write D_j for the sum of the three channels at site j. The Schrodinger generators tested are

    L = -i[H, .] + D_1 + D_2,
    L^(1) = L - D_1 = -i[H, .] + D_2.                 (1)

Deletion means removing the entire anchored-site sum. H and every surviving filter are unchanged. It does not delete a Hamiltonian term, recompute filters for a different H, secularize them, remove their imaginary parts, or delete only one Pauli axis. Both dual generators annihilate I.

The prior mechanism being tested is specific. [Bergamaschi, arXiv:2606.26090v1](https://arxiv.org/html/2606.26090v1), Definition1.10/Eq.8 and Lemma1.11, groups all Pauli updates at a site. Lemma4.7, Eq.75 and Remark4.9 use one common KMS norm for the full and deleted-site evolutions. Its auxiliary generator has prescribed Gibbs-conjugate filters and no added Hamiltonian term. Our (1) is the natural corresponding test on the actual Redfield generator, not an identification of the two generators. These source passages were checked on 17 October 2026; no full-paper proof audit is claimed.

## 2. Why all-observable KMS dissipativity forces stationarity

For a faithful density sigma, define

    <X,Y>_sigma = Tr[X^dagger sigma^(1/2) Y sigma^(1/2)].

Let G be any trace-preserving, Hermiticity-preserving finite-dimensional Schrodinger generator, so G^*(I)=0. If

    Re <O, G^*(O)>_sigma <= 0 for every O,             (2)

then G(sigma)=0. Indeed, for any Hermitian Y and real epsilon,

    Re <I+epsilon Y, G^*(I+epsilon Y)>_sigma
      = epsilon Tr[G(sigma)Y]
        + epsilon^2 Re <Y,G^*(Y)>_sigma.              (3)

The inequality for both signs of arbitrarily small epsilon forces the linear coefficient to vanish for every Y. Equivalently, if B=G(sigma) is nonzero, the choice Y=B gives a strictly positive linear coefficient Tr(B^2). Small positive epsilon then violates (2).

Contractivity of exp(tG^*) in this norm implies (2) by differentiation at t=0. Thus common contractivity of L^* and (L^(1))^* would imply

    L(sigma)=L^(1)(sigma)=0, and therefore D_1(sigma)=0. (4)

This argument uses neither positivity of the evolution nor detailed balance.

## 3. Exact full-filter coefficients

Put

    k0 = integral_0^infinity Phi(s) ds = r0 + i e,  r0=c/2,
    C  = integral_0^infinity Phi(s) cos(2Omega s) ds = r + i f,
    D  = integral_0^infinity Phi(s) sin(2Omega s) ds = d - i t r,
    t = tanh(a Omega).

Here e,r,f,d are real. The last equality follows from the bath KMS relation:

    J_bath(2Omega)=2 Re C - 2 Im D,
    J_bath(-2Omega)=2 Re C + 2 Im D.

In particular

    r = c cosh(a Omega) sech(2a Omega)/2 > 0.           (5)

For A_C=(A+PAP)/2 and A_A=(A-PAP)/2,

    K_A = k0 A_C + C A_A - i D P A_A.                 (6)

There is no small-frequency expansion in (5) or (6).

Define Delta=f-t d-e. The contour calculation previously recorded in note09, Sections2-4, gives the exact formula

    Delta = c/(2a) integral_0^(a/2) sec(pi v/(2a))
                   [1-cosh(2Omega v)/cosh(a Omega)] dv > 0. (7)

For completeness, substitute w=s+i a/2 in the integral for Delta. Deform the horizontal contour to the real axis in the strip 0<=Im(w)<=a/2. The nearest sech pole is at ia, the remote vertical integral vanishes exponentially, and the real-axis integrand is real. The remaining vertical integral is (7). Its integrand is positive except at the upper endpoint. The entire calculation is reproduced by the formula above rather than depending on access to a local note09 copy.

## 4. Symmetry reduction and grouped-channel matrices

The Pauli unitaries U=X_2 and V=Z_1 Z_2 commute with H. They conjugate every bath coupling A to either A or -A, so they conjugate K_A by the same sign. Consequently L, L^(1) and D_1 commute with both conjugation maps.

The averaging map

    Pi(rho) = (rho + U rho U + V rho V + UV rho VU)/4

preserves trace and Hermiticity, and is a convex combination of unitary conjugations. Its range is precisely span{I,Z_1,X_1X_2,Y_1X_2}=span{I,P,Q,T}. Although U and V anticommute as matrices, their conjugation maps commute.

In the ordered basis (I,P,Q,T), the exact Schrodinger maps D_1 and D_2 have the following coefficient matrices. Column j is the image of basis element j:

             [ 0       0           0              0       ]
    D_1 =    [-8rt    -8r           0              0       ]
             [ 0       0       -4(r+r0)           4d       ]
             [ 0       0          -4d         -4(r+r0)     ],    (8)

             [ 0       0           0              0       ]
    D_2 =    [-4rt    -4r          4r0             0       ]
             [ 4rt     4r        -4r0             0       ]
             [4(e-f)  -4d         -4d         -4(r+r0)     ].   (9)

These follow by inserting (6) into the definition of D_A and multiplying the 4x4 Pauli matrices. The accompanying symbolic checker reconstructs every displayed image as a full 4x4 matrix; it does not merely compare projected coefficients. It also checks the twirl range and the symmetry signs.

Any trace-one Hermitian operator in this range has the form

    rho = (I+pP+qQ+wT)/4, with p,q,w real.

From (8), D_1(rho)=0 forces p=-t. The remaining two equations are

    -(r+r0)q + d w = 0,
    -d q - (r+r0)w = 0.

Their determinant is (r+r0)^2+d^2>0, so q=w=0. Thus the unique trace-one stationary operator for D_1 in the twirled algebra is

    rho_G = (I-tP)/4 = exp(-aH)/Tr exp(-aH).           (10)

It commutes with H. Equations (8)-(9) give

    D_1(rho_G)=0,
    L(rho_G)=L^(1)(rho_G)=D_2(rho_G)=-Delta T != 0.   (11)

## 5. No common weight, including a corrected full stationary weight

Suppose a trace-one Hermitian sigma were stationary under both L and L^(1). Then D_1(sigma)=0 by (4). Covariance of the three maps under Pi gives the same properties for Pi(sigma). By (8)-(10), Pi(sigma)=rho_G. But L(Pi(sigma)) must be zero, contradicting (11).

Therefore no such sigma exists. In particular:

- Bare Gibbs does not make the full or site-1-deleted generator dissipative for all observables. Formula (3) supplies an explicit family witnessing failure, using B=-Delta T.
- If sigma_* is any faithful stationary density for the full generator, then L^(1)(sigma_*) != 0, so the deleted generator is not dissipative in the sigma_* KMS norm. This does not decide whether the full generator alone is dissipative in that corrected norm.
- No single faithful weight can make the full generator and all whole-site-deleted generators contractive. Already the site-1 deletion obstructs it.

No assumption that sigma commutes with H was used in this contradiction. Nor was the nonstationarity of the bare Gibbs state silently taken to imply absence of an actual stationary density.

## 6. Nonvacuity and explicit strong-noise admission

There is an actual faithful full stationary density for sufficiently small lambda. Here is a finite-dimensional bound proving it without assuming positivity of the Redfield evolution.

At lambda=0 the generator is

    L0(rho)=c sum_(six A) (A rho A-rho).

On the traceless Hilbert-Schmidt space its Pauli eigenvalues are -4c times the nonzero Pauli support weight. Therefore ||L0^(-1)||_(2->2)<=1/(4c).

Write L=L0+E. Unitary evolution gives ||A(-s)-A||<=2Omega s, hence ||K_A-k0A||<=2Omega gamma tauB. Each channel correction has induced Hilbert-Schmidt norm at most four times this operator norm. Including all six channels and the Hamiltonian term yields

    ||E||_(2->2) <= delta0 := 2Omega(1+24 gamma tauB). (12)

The trace-zero space is invariant. If delta0<4c, L is invertible there by the Neumann bound. Its unique trace-one stationary operator is

    sigma_* = I/4 + eta,
    eta = -(L restricted to trace-zero)^(-1) E(I/4).

Hermiticity and uniqueness make eta Hermitian. Since ||I/4||_2=1/2,

    ||eta||_op <= ||eta||_2 <= delta0/[2(4c-delta0)].  (13)

Thus delta0<4c/3 ensures sigma_*>0. This is an actual stationary state of the full-filter generator, not a Gibbs approximation.

For a concrete admitted choice, take any a>0 and

    c=pi^2/(768 sqrt(2)a),  lambda=c/100.

Then gamma tauB=1/192, the local Hamiltonian incidence bound is h=2lambda, and the neighborhood parameters are m=nu=2. These satisfy the previously used small-parameter box

    h <= b0 gamma,  gamma tauB <= 1/(12 nu 2^m).

Its displayed strong-noise margin evaluates to

    8b0 gamma - 2h - 24 nu 2^m gamma h tauB
      = 4c - 6lambda = 197c/50 > 0.                 (14)

Also delta0=9 sqrt(2)c/400<4c/3, proving faithfulness in this explicit family. The Hamiltonian is noncommuting: (14) checks physical parameter membership only; it does not apply the accepted commuting-H error theorem to this model.

## 7. What this does and does not settle

The exact common-weight premise needed for the direct deleted-site KMS contraction argument is false for an admitted, connected, two-site full-filter model. This is stronger than merely saying that a generator-to-Gibbs-sampler identification has not been supplied.

It remains possible to use different norms, controlled positive growth, a different decomposition or a comparison theorem with additional error terms. Such a route must supply its own estimates. The result neither proves instability of fixed-support observables nor contradicts the existing restricted commuting comparison theorem. The original all-time, all-volume, fixed-support P5 response and coarse-graining error questions remain unresolved.

The broad distinction between bath KMS and exact generator equilibrium is established literature. See [Thingna, Wang and Hanggi, J. Chem. Phys.136,194110 (2012)](https://arxiv.org/abs/1203.6207) and [Soret, Cavina and Esposito, arXiv:2207.05719](https://arxiv.org/abs/2207.05719). This note is an exact source-specific admission test, not a historical novelty claim.
