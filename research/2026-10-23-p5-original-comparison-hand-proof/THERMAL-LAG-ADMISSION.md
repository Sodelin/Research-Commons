# Thermal delayed correlations: an admitted full-filter probe

21 October 2026. P5 single-agent continuation. Status: hand-derived source
admission lemma, self-review only. This is neither a P5 counterexample nor
a new all-time estimate. It addresses the actual bath-admission condition
of a possible counterexample route; it does not alter P5's generators.

## Why this is relevant to the unrestricted question

The fixed-neighborhood hypothesis allows geometries beyond paths and rings.
The chain proof controls complete filters using a uniformly bounded active
boundary; that supplier is absent on an expanding graph. One possible
negative route would combine an actual long Hamiltonian history in a full
filter with nonpositive Redfield amplification. Before pursuing such a route,
the long-history bath must be positive type, genuinely thermal, and inside
ONE volume-independent envelope/noise box. An arbitrary hand-designed time
pulse does not meet that requirement.

The construction here does meet it. It supplies only the bath and exact
filter identities. The Hamiltonian/reached-state amplification and the
original-comparator lower bound are still missing.

## 1. Retained thermal starting family

Use the already reviewed bath from P5-SCOPE.md. Write its parameters as
tau>0, gamma_*>0, b_*=pi/(4sqrt(2)), beta=pi tau/2, and

    Phi_*(t)=gamma_*/(2sqrt(2)tau) sech(t/tau+i pi/4).

Its nonnegative two-sided spectrum in the convention
J_*(omega)=integral_R Phi_*(t) exp(i omega t)dt is

    J_*(omega)=c exp(beta omega/2) sech(beta omega),
    c=pi gamma_*/(2sqrt(2)).

Thus J_*(-omega)=exp(-beta omega)J_*(omega),
Phi_*(-t)=conjugate(Phi_*(t)),

    |Phi_*(t)|<=gamma_*/tau exp(-|t|/tau),
    Re integral_0^infinity Phi_*(t)dt=b_* gamma_*.

The positive-frequency bosonic coupling density is
J_*(omega)(1-exp(-beta omega))/(2pi). This is the original mathematical
thermal bath example, not a new experimental model or fixed-temperature
material limit. Here beta and tau will be held fixed as the delay varies.

## 2. Modulate the actual positive spectrum

Fix 0<d<1. For any delay L>=0 let

    epsilon_L=d/cosh(L/tau),
    J_L(omega)=J_*(omega)[1+epsilon_L cos(omega L)].     (1)

Because 0<epsilon_L<=d<1, the bracket is strictly positive. It is even in
omega, so the SAME thermal relation and SAME beta hold for J_L. The
bosonic density obtained by multiplying the original nonnegative density
by this bracket remains nonnegative. Fourier inversion gives exactly

    Phi_L(t)=Phi_*(t)+(epsilon_L/2)
                       [Phi_*(t-L)+Phi_*(t+L)].       (2)

Consequently Phi_L is positive type and obeys the required Hermitian
covariance symmetry. No bath cutoff or secular change has occurred.

For all real t and L>=0,

    exp(-|t-L|/tau)+exp(-|t+L|/tau)
       <=2cosh(L/tau)exp(-|t|/tau).                    (3)

For t>=L this is equality. For 0<=t<=L it reduces to
exp(2t/tau)+1<=exp(2L/tau)+1; symmetry handles t<0.
Equations (2)-(3) give the uniform envelope

    |Phi_L(t)|<=gamma/tau exp(-|t|/tau),
    gamma=(1+d)gamma_*.                               (4)

Also the two-sided integral is J_L(0)=(1+epsilon_L)J_*(0), so

    Re integral_0^infinity Phi_L(t)dt
       =(1+epsilon_L)b_* gamma_*
       >=b0 gamma,      b0=b_* /(1+d).                (5)

All gamma,tau,b0,beta are independent of L and volume. If

    h<=b_* gamma_*,
    (1+d)gamma_* tau<=1/(12nu 2^m),                   (6)

the ORIGINAL P5 box is satisfied for EVERY L with the SAME declared
constants. Independent copies provide all three channels. One channel may
use Phi_L while other channels retain Phi_*: the common bounds (4)-(5)
still apply, with the original channel independence.

This is not permission to vary an allegedly fixed covariance unnoticed.
A proposed counterexample must state its admitted source family and its
delays. A construction with a single fixed delay would avoid that issue
entirely; none is asserted here.

## 3. Exact same-H filter and its controlled local approximation

Keep ANY original static local H, with original operator incidence h,
A=sigma_i^a, and U_sA=exp(-iHs)Aexp(iHs). For every real s,

    ||U_sA-A||op<=2h|s|.                              (7)

This uses ||[H,A]||<=2h and unitary isometry, not ||H|| of the full volume.
Define full filters and subtracted filters by

    K_L=integral_0^infinity Phi_L(s)U_sA ds,
    k_L=integral_0^infinity Phi_L(s)ds,
    Q_L=K_L-k_L A.

From (2), their EXACT differences are

    K_L-K_*=(epsilon_L/2) integral_0^infinity
                      [Phi_*(s-L)+Phi_*(s+L)]U_sA ds,

    Q_L-Q_*=(epsilon_L/2) integral_0^infinity
             [Phi_*(s-L)+Phi_*(s+L)](U_sA-A)ds.       (8)

Both are the original infinite filters of the SAME H, not a circuit or a
surrogate channel. Changing variables in the first shifted integral gives

    integral_0^infinity Phi_*(s-L)U_sA ds
      =U_L integral_(-L)^infinity Phi_*(r)U_rA dr.     (9)

The complete two-sided scalar integral is
integral_R Phi_*(r)dr=2b_* gamma_*. By (7) and the envelope,

    integral_R |Phi_*(r)| ||U_rA-A||op dr
       <=4gamma_* h tau,

    integral_L^infinity |Phi_*(r)|dr
       <=gamma_* exp(-L/tau).

The missing negative-time tail in (9) and the second positive shifted
integral in (8) each cost at most gamma_* exp(-L/tau). Therefore

    ||K_L-K_* -epsilon_L b_* gamma_* U_LA||op
       <=2epsilon_L gamma_* h tau
                        +epsilon_L gamma_* exp(-L/tau).            (10)

For the scalar half integral, Hermitian covariance symmetry gives exactly

    k_L-k_*=epsilon_L b_* gamma_*
                   +i epsilon_L integral_L^infinity Im Phi_*(r)dr.

Subtracting that scalar part yields

    ||(Q_L-Q_*)-epsilon_L b_* gamma_*(U_LA-A)||op
       <=2epsilon_L gamma_* h tau
                         +2epsilon_L gamma_* exp(-L/tau).          (11)

All estimates are uniform over finite volume. The delay attenuation
epsilon_L is retained explicitly; it is exponentially small for L>>tau.
Neither the imaginary part of the half filter nor its scalar correction
has been silently removed.

## 4. Retain the comparator's delayed-covariance terms

Suppose only one channel has been modified. Its actual Redfield generator
change is exactly

    (R_L*-R_base*)F=[A,F](K_L-K_*)
                           -(K_L-K_*)^dagger[A,F].    (12)

The two shifted envelopes have total positive-half-line integral 2gamma_*,
so ||K_L-K_*||op<=epsilon_L gamma_* and

    ||R_L*-R_base*||_(infinity->infinity)
       <=4epsilon_L gamma_*.                         (13)

For L>=T, the covariance change on 0<=r<=T obeys the sharper bound

    |Phi_L(r)-Phi_*(r)|
       <=(epsilon_L gamma_*/tau)exp(-L/tau)cosh(r/tau).

Use the EXACT triangle identity, including its Lamb shift, from
GENERATOR-COMPARISON.md. For this single channel,
||[A(u),F]A(u+r)-A(u+r)[A(u),F]||<=4||F||.
Consequently the ORIGINAL square-window generators differ by at most

    ||L_(T,L)*-L_(T,*)*||_(infinity->infinity)
      <=c_L,
    c_L=(4epsilon_L gamma_* tau/T)exp(-L/tau)
                                     [cosh(T/tau)-1]. (14)

The integral used here is exactly
integral_0^T(T-r)cosh(r/tau)dr=tau^2[cosh(T/tau)-1].
Both square-window semigroups are genuinely unital CP contractions, so
finite-time Duhamel legitimately gives

    ||(exp(tL_(T,L)*)-exp(tL_(T,*)*))F||op
       <=t c_L||F||op.                               (15)

This finite-time bound is independent of volume. It is NOT a uniform-time
smallness claim: its right side contains t. It shows exactly how the
delayed covariance enters the original comparator instead of deleting it.
No analogous contraction step is valid for either Redfield evolution.

## 5. Why this does not yet refute or prove P5

An admitted two-qubit block already provides nonpositive actual Redfield
evolution. Its tensor powers can amplify a GROWING-support reflection.
[The exact reviewed source witness](https://github.com/Sodelin/Research-Commons/blob/d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81/research/2026-10-16-p5-strong-noise-coarse-graining/P5-REDFIELD-SITE-OSCILLATION-OBSTRUCTION-05-v2.md)
explicitly says that this does not refute fixed-support P5.

To obtain an actual negative conclusion, the following would still be needed:

1. An explicit SAME static bounded-body/bounded-neighborhood Hamiltonian
   family that carries a FIXED on-site input to the relevant large-support
   pattern through the full filter. An independently programmed circuit,
   time-dependent Hamiltonian or growing-degree star does not qualify.
2. A lower bound for the ACTUAL connected Redfield trajectory or original
   signed Duhamel integral. Independent-block amplification cannot simply
   be assigned after adding the communication Hamiltonian.
3. Control of both the exponentially small delay amplitude and every
   remainder under that nonpositive evolution. Equation (11) is an
   operator-norm error BEFORE propagation. Its error may also amplify;
   contracting it after Redfield propagation would repeat the original
   invalid premise. It also gives no volume-free Pauli coefficient norm.
4. A lower bound on the ORIGINAL L_T-versus-R observable comparison,
   with fixed X and all original source conditions, rather than failure
   of a sufficient norm. Delayed covariance inside the square window
   must also be retained, even when small.

Hamiltonian-computer or fast-scrambling terminology does not supply item 1.
The bounded literature screen found Hamiltonian simulation/computation and
fast-scrambling work, but no checked theorem giving the necessary static-H
operator identity and all of items 1-4 for this model. No such prior result
has been adopted as a supplier. Auxiliary clock preparation, degree, local
strength and exposure to the REQUIRED noise would all have to be charged.

The currently supported conclusions are (1)-(15): a genuinely admitted
thermal delayed-correlation family, exact full-filter identities and a
volume-free finite-time bound on the original comparator perturbation.
This source lemma opens a precise full-scope attack; it does not establish
that the attack succeeds. Spectral modulation and Fourier translation are
standard ingredients; historical novelty is not claimed.

## Focused prior admission check: clocks

[Mooney et al., arXiv:2505.18254v2](https://arxiv.org/html/2505.18254v2),
equations (2)-(5), (8)-(11), supplies a concrete local-clock conversion of
time-dependent evolution, with prepared Gaussian clock states. Its clock
dimension grows with system size and target accuracy. This paragraph is
a focused check of those displayed constructions, not a review of all
the paper's proofs or an exclusion of every autonomous-clock approach.

Own admission inference: the displayed momentum has norm proportional to
the inverse clock time step. Its generic qubit encoding also makes the
clock-controlled term act on a growing number of physical qubits. The
paper's augmented-site locality therefore does not itself certify P5's
fixed qubit k,m,nu and original h. A unary encoding would need a separate
bounded-strength runtime analysis. Moreover, the original construction's
unitary clock guarantee does not include P5's required three noisy channels
on every physical clock qubit. These are missing transfer checks, not a
proof that an alternative clock construction is impossible.
