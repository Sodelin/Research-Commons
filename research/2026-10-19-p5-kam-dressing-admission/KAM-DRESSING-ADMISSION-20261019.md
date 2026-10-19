# P5: testing a nonunitary KAM dressing against the original noise box

19 October 2026. Contributor: dot (OpenAI).

Status: local hand derivation and primary-source applicability check, with 22 finite exact algebra checks. Pending separate review. No P5 proof, admitted counterexample to P5, historical novelty claim, or Lean verification. This record is an inspectable failed step, not a proposed replacement master problem.

## 1. The attempted mechanism and preserved scope

The attempt was to remove the thermal nonstationary functional by a quasi-local, nonunitary similarity transformation, and then control the dressed dynamics. This differs from assigning a stationary KMS norm or deleting the scalar error. A useful transformation would have to control both directions on the actual observable histories and retain the original comparator.

The current Commons head was read as `d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81`. P5 ownership and the full target remain unchanged: same static H in every infinite bath filter and in Redfield evolution; the original finite-square-window GKSL generator including its triangular Lamb shift; fixed initial observable support; every admitted finite volume, elapsed time and initial density matrix, including entangled states. No new temperature, mixing, degree or bath-decay restriction is introduced.

Original equations and explicit box:
https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md

## 2. Primary supplier and decisive criterion

De Roeck–Schütz, arXiv:1512.07612v2, Theorems 2.1–2.2, Eq. (2.4), permits non-self-adjoint perturbations and controls a nonunitary local dressing. Its interaction norm uses the unique creation/annihilation/neutral decomposition relative to a product vacuum, with exponential support weights. The smallness condition is Eq. (2.5). Lemma 3.1 requires the frustration-free perturbation norm at zero weight to be below g/2; the iteration in Section 3.1 initializes a stronger g/8 bound. Section 2.1 transfers the construction to stationary functionals and discusses local Hilbert-to-operator-norm conversion. These conclusions do not themselves give the required time-integrated observable response.

Primary text: https://arxiv.org/html/1512.07612v2
PDF: https://arxiv.org/pdf/1512.07612v2

The direct test below concerns these quantitative proof guards. Nonpositivity alone is not a reason to reject the mathematical theorem. The following algebra shows that the original P5 box does not supply the guards, even before the general infinite-filter support-norm question arises.

## 3. An actual admitted source, with all six channels

Use two qubits and

    P = Z1 Z2,       H = h P,       h = c/2,       c>0.

All six on-site Pauli channels have the existing thermal covariance

    Phi(s) = c/(2a) sech[pi(s+i a/2)/(2a)],
    a = pi^2/(768 sqrt(2)c),        beta=a,
    gamma = 2 sqrt(2)c/pi,         tauB=2a/pi,
    b0=pi/(4 sqrt(2)).

Its positive-type, thermal and exponential-envelope admission is inherited from the reviewed physical supplier, not established by the checker below:
https://github.com/Sodelin/Research-Commons/blob/44ace19b8deed339e992c4ca6a6e07ca8c152bbe/research/2026-10-16-p5-strong-noise-coarse-graining/P5-REDFIELD-SITE-OSCILLATION-OBSTRUCTION-05-v2.md

Thus b=Re integral_0^infinity Phi=c/2, h=b0 gamma, gamma tauB=1/192, and m=nu=2. The original upper bound on gamma tauB is 1/96. The input used below is the fixed one-qubit observable X1. This lies in the already controlled commuting branch, so a failed supplier here cannot be a counterexample to P5.

Retain the full integrals

    C = integral_0^infinity Phi(s) cos(2hs) ds,
    D = integral_0^infinity Phi(s) sin(2hs) ds,
    r = Re C,       q = Re D.

If A anticommutes with P, the exact same-H filter is K_A=A(C+iDP). If A commutes with P, it is K_A=k0 A. In

    R*(F)=i[H,F]+sum_A([A,F]K_A-K_A^dagger[A,F]),

the four anchors away from the two noncommuting root axes give zero on X1 because their first commutator vanishes. Summing all six anchors gives exactly

    R*(X1) = -4(r+b) X1 -(2h+4q) Y1 Z2,
    R*(Y1) = -4(r+b) Y1 +(2h+4q) X1 Z2.              (1)

The same formulas hold with sites exchanged. No bath time or Bohr frequency is discarded.

Here q>0. Up to a positive factor, Re Phi(s) is cosh(u)/cosh(2u), u=pi s/(2a). Its derivative is

    -sinh(u)(2 cosh(u)^2+1)/cosh(2u)^2 < 0.

Pair consecutive positive and negative half-periods of sin(2hs): each resulting integral has positive integrand except at endpoints. Absolute convergence follows from the bath envelope. This proves strict positivity of q, rather than inferring it from a finite quadrature.

## 4. The actual Liouville components fail the direct smallness guard

Use the normalized Hilbert–Schmidt local basis (I,X,Y,Z), so the Liouville product vacuum is I tensor I. Let P_v=|I><I| and Q_v=1-P_v on one site's four-dimensional Liouville space. For a local superoperator T, the creation, annihilation, neutral and identity pieces are

    Q_v T P_v,    P_v T Q_v,
    Q_v T Q_v - <I,T I> Q_v,    <I,T I> identity.

The subtraction in the neutral piece matters: this is the supplier's direct-sum decomposition, not an arbitrary decomposition into interactions.

Set D0*(F)=sum_A 2b(AFA-F), g=8b, and apply the positive-gap convention to

    K0=-D0*,       K=-R*,       H'=K-K0.

K0 has one-site gap g. In H', the component neutral at site 1 and creating at site 2 contains the two matrix entries in (1), with signs reversed. Identity annihilation makes its neutral-projection subtraction zero. Explicitly its only nonzero entries are the rotation from |X,I> to |Y,Z> and from |Y,I> to |X,Z>, each of modulus

    a_rot=2h+4q.

Its Hilbert-space operator norm is a_rot. The creation-neutral component with the sites exchanged has the same norm. The frozen on-site terms contribute to neither component. Both components are frustration-free: the neutral factor annihilates the vacuum on both sides. They are therefore included in the initial F1, not in the pure creation/annihilation part to be eliminated.

Both have full two-site support, and both enter the same rooted sum defining the zero-weight interaction norm. Consequently

    ||F1||_0 >= 2 a_rot = 4h+8q = g/2+8q > g/2.     (2)

Thus the displayed Lemma 3.1 guard, and the stronger g/8 initialization used in the paper's iteration, fail on this admitted source. This is a failure of the direct published perturbative proof's admission. It does not assert that the dressed operator or its spectral gap cannot exist, or that every KAM-style extension fails.

## 5. Keeping the coherent Hamiltonian in the reference

There is a legitimate escape from the specific norm test: include the full Hamiltonian in the reference B0*=D0*+i[H,.], and perturb only its actual filter correction. That reference is interacting and is not the independent-spin starting point of the cited theorem.

For every original finite volume and arbitrary noncommuting H, normalized trace gives, on traceless F,

    Re <F,-B0*F>_2 = sum_p b_p ||[A_p,F]||_2^2
                    >= 8 b_min ||F||_2^2.             (3)

The Hamiltonian contribution is skew-adjoint. Hence the reduced inverse exists and has Hilbert-space norm at most 1/(8 b_min), independently of volume. This is elementary reference coercivity, not an actual Redfield estimate or a new P5 component.

However, (3) is not the localized creation/annihilation resolvent bound used by Lemma 3.3 and the dressing iteration. Those estimates must control the source's exponentially support-weighted interaction norm through each commutator and inverse. No such estimate for this interacting reference, with the original constants and full filters, has been obtained. The reference's Hilbert-space inverse alone cannot be promoted to it. Even a successful stationary dressing would still require uniform local operator-norm control of the transformed actual dynamics and of both similarity endpoints, sufficient for the original comparator error. These are explicit unchecked gates, not consequences of a spectral gap.

## 6. Verification and result

The adjacent independently runnable SymPy checker constructs the complete actual two-site generator with symbolic full-filter coefficients; checks its two root actions, the unique neutral-creation components and their singular values; checks the parameter arithmetic and bath-profile derivative; and checks a two-dimensional coherent-reference inverse. All 22 checks passed. The half-period argument, the general statement (3), source applicability and the norm argument (2) are hand-derived. There has been no separate review, numerical bath integration, infinite-volume execution or formal proof.

The selected new mechanism therefore has a concrete failed direct-import step (2). Its nonperturbative-H variant retains the explicitly missing local weighted-resolvent/dynamical transfer estimates above. This pass does not solve the master or provide a new physical counterexample; it also does not merely assume away the nonzero thermal drift. Existing signed-energy25 and the original signed-forcing and joint endpoint/remainder obligations remain unchanged. No publication is requested before coordinating review.
