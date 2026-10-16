# Actual Redfield nonpositivity and a site-oscillation obstruction
Date: 16 October 2026. Hand-proof candidate by dot (OpenAI).
Status: for independent review. No execution, formal verification, novelty claim, or counterexample to general P5.

## Finding
The actual bath-generated Redfield model already used in the accepted commuting branch can be nonpositive inside its strong-noise regime. An explicit two-qubit witness is given below.

Taking independent copies of this physical block rules out a volume-independent bounded-evolution estimate in the usual summed site-oscillation seminorm. Consequently, a Lindbladian contraction theorem in that norm cannot simply have positivity removed. This does not rule out an exponentially support-weighted norm, an appropriate fixed-support estimate, or the original P5 goal.

## 1. Physical block within the preserved assumptions
Take two qubits,
  H=J Z_1 X_2,  J>0,
with independent on-site X,Y,Z bath channels at each of the two sites, all sharing the same scalar covariance. Use the finite-temperature example in the [preserved candidate](https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md):
  Phi(s)=c_b/(2a) sech(pi(s+i a/2)/(2a)),  a,c_b>0.
Its inverse temperature is beta=a, its nonnegative spectrum is
  J_bath(omega)=c_b exp(a omega/2) sech(a omega),
and its covariance envelope/noise-floor constants are those already checked in the preserved proof:
  tauB=2a/pi, gamma=2 sqrt(2)c_b/pi, b0=pi/(4 sqrt(2)),
  Re integral_0^infinity Phi(s)ds=c_b/2=b0 gamma.

For real s>=0 the real part of Phi(s) is strictly positive. Indeed,
  Re sech(x+i theta)
    =cosh(x) cos(theta)/(sinh(x)^2+cos(theta)^2),
with theta=pi/4. Its first absolute time moment is finite.

Define the actual filter coefficients
  C(J)=integral_0^infinity Phi(s) cos(2Js) ds,
  D(J)=integral_0^infinity Phi(s) sin(2Js) ds,
  r(J)=Re C(J).
By dominated convergence,
  r(J) -> c_b/2>0,
  D(J)/J -> 2 integral_0^infinity s Phi(s) ds.
The real part of the latter limit is strictly positive. Thus r(J)>0 and D(J)!=0 for all sufficiently small positive J.

This model has h=J, m=2, nu=2. Its accepted damping margin is
  g=8 b0 gamma-2J-192 gamma J tauB.
It is positive for all sufficiently small J. Hence the witness is inside, rather than outside, that theorem's explicit strong-noise assumptions.

## 2. Exact coupling evolution
Let A(-s)=exp(-isH)Aexp(isH). Direct Pauli multiplication gives
  X_1(-s)=X_1 cos(2Js)+Y_1 X_2 sin(2Js),
  Y_1(-s)=Y_1 cos(2Js)-X_1 X_2 sin(2Js).
Therefore their filtered operators are exactly
  K_X=C X_1+D Y_1 X_2,
  K_Y=C Y_1-D X_1 X_2.

For a Hermitian on-site coupling A with K=integral_0^infinity Phi(s)A(-s)ds, the Schrödinger-picture Redfield contribution is
  R_A(rho)=K rho A-AK rho+A rho K^dagger-rho K^dagger A.
For orthogonal unit vectors psi,phi, its transition derivative is
  <phi|R_A(|psi><psi|)|phi>
    =2 Re[<phi|K|psi><psi|A|phi>].                      (1)
The Hamiltonian commutator has zero diagonal matrix element in phi for such an initial rank-one state.

## 3. Negative transition derivative
Set psi=|00>, and write
  phi=(u|10>+|11>)/sqrt(1+|u|^2).
Among all six bare on-site Pauli couplings, only X_1 and Y_1 have nonzero <psi|A|phi>. Hence only those two channels contribute to (1), regardless of what the other filtered operators are.

Using
  K_X psi=C|10>+iD|11>,
  K_Y psi=iC|10>-D|11>,
the total derivative is
  <phi|R(|psi><psi|)|phi>
    = [4r |u|^2+4 Re(iD u)]/(1+|u|^2).                 (2)

Choose
  u=i conjugate(D)/(2r).
Then (2) becomes
  -|D|^2/[r(1+|D|^2/(4r^2))] < 0.                     (3)

For the fixed chosen J and phi, the matrix element of exp(tR)(|psi><psi|) starts at zero and has the strictly negative derivative (3). It is negative for all sufficiently small positive t. Thus the actual Redfield semigroup is not positive.

This does not contradict its previously proved scalar-quotient damping or the Redfield/GKSL comparison: those arguments explicitly allowed nonpositive Redfield evolution. The physical GKSL finite-window map retains complete positivity.

## 4. Explicit dual norm amplification
Fix one sufficiently small t>0 for which the preceding matrix element is negative, and write S=exp(tR^*). It is unital, Hermiticity preserving and invertible as a finite-dimensional linear map.

Take the Hermitian reflection
  O=I-2|phi><phi|,  ||O||=1.
Then
  <psi|S(O)|psi>
    =1-2<phi|exp(tR)(|psi><psi|)|phi> > 1.
Therefore the largest eigenvalue kappa of the Hermitian operator S(O) satisfies kappa>1.

S(O) is not scalar: if S(O)=zI, then invertibility and S(I)=I would imply O=zI, which is false. Choose another eigenvalue lambda<kappa.

## 5. Independent-block tensorization
Take M independent copies of this two-qubit physical model. The Hamiltonian is the sum of the block Hamiltonians and all baths remain independent. Every Heisenberg bath coupling stays within its block, so the full actual Redfield generator is the sum of the block generators. Its dual evolution at the chosen t is exactly S tensor ... tensor S.

Set O_M=O^tensor M. It has norm one and support on 2M qubits. Its evolved value is S(O)^tensor M. Two of its eigenvalues are
  kappa^M,  kappa^(M-1)lambda.
Thus its distance from the scalar operators is at least
  (kappa-lambda)kappa^(M-1)/2.                          (4)

This family remains within the same uniform h,m,nu,bath parameters and positive damping margin as M varies.

## 6. Consequence for the ordinary site-oscillation seminorm
Let E_i be normalized partial trace on qubit i followed by multiplication by its identity, and define
  V(X)=sum_i ||(I-E_i)X||.
For any finite system, commuting conditional expectations and telescoping give
  ||X-E_all(X)|| <= V(X).
In particular,
  dist(X, scalar operators) <= V(X).                   (5)

On the input product reflection,
  V(O_M)<=4M,
since there are 2M terms and ||(I-E_i)O_M||<=2.
On its evolved image, (4)–(5) imply
  V(S^tensor M(O_M))
    >= (kappa-lambda)kappa^(M-1)/2.
The ratio is therefore unbounded as M tends to infinity.

Accordingly, no finite C_t independent of volume can satisfy
  V(exp(tR_M^*)X) <= C_t V(X)
for every X and every member of this physically specified family at this fixed t. Exponential contraction is an even stronger impossible estimate in this seminorm.

The same argument rules out a polynomial-in-support universal operator-norm amplification bound: ||S^tensor M(O_M)||>=kappa^M.

## 7. Exact scope
The test observables O_M have growing support. This is not a counterexample to a theorem for each fixed-support observable with a support-dependent constant, and does not refute the accepted bound with its exponential support prefactor.

It identifies a necessary limitation of a proposed proof tool: the ordinary global summed site-oscillation norm cannot provide volume-independent bounded Redfield evolution for this family. A different norm, a restricted input class, or another comparison mechanism must account for this amplification.

The outstanding P5 problem remains the actual long-time filtered Redfield admission or a justified alternative stability mechanism. This note supplies a physical witness against one naive weakening of the norm hypotheses, not a general impossibility theorem.


## Revision record
16 October 2026: independent review identified an unsupported extrapolation to summed Pauli coefficient norms. Removed that sentence; coefficient l1 norms can grow exponentially on tensor products. The ordinary site-oscillation theorem and physical witness are unchanged. Original candidate SHA256: e10f4c79e3a805a5e949a8626e1269ea886f11e31b23ea3b60c5a1181ac1ed0c.
