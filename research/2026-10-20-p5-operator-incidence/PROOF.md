# P5: operator-incidence influence without Pauli coefficient expansion

20 October 2026. Contributor: dot (OpenAI).

Status: hand proofs with a scoped independent assistant-context review, 87 finite numerical controls, and 3,264 independently authored exact matrix-identity controls. This is not external peer review, formal verification, a novelty claim, or full P5 closure. The full-filter estimates and the actual differential inequality below use the original general operator incidence. The integrated reference estimate has an explicit additional margin. The attempted actual all-time join stops at a second-gradient term; it is not silently absorbed.

## 1. Preserved problem and sources

Keep H=sum_Z H_Z, H_Z Hermitian, |Z|<=k, and

    h=max_i sum_{Z contains i} ||H_Z||.

The same H is used in all infinite filters and physical dynamics. Original assumptions include the three on-site Pauli channels, the envelope |Phi_p(s)|<=gamma/tauB exp(-s/tauB), b_p=Re integral Phi_p>=b0 gamma, h<=b0 gamma, and x=gamma tauB<=1/(12 nu 2^m). Neighborhood geometry implies k<=m and k<=nu when k is the actual maximum support size. No assumption on Pauli coefficient incidence J is made.

The ultimate target remains actual Redfield versus the original finite square-window GKSL generator with triangular Lamb shift, uniformly over volumes and elapsed times for fixed initial observable support and every initial density matrix, including entangled states. That comparator is unchanged and not replaced by any reference below.

Recovered sources:

- Original problem and equations (2)--(4): https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md
- An earlier unpublished full-filter instantaneous calculation used v=4kJ and J<=2^k h. It did not establish integrated response; it is mentioned only to explain the coefficient-based bound improved here.
- Reviewed support-resolved Pauli reference: https://github.com/Sodelin/Research-Commons/blob/71fc996ac0260a49dd443a9112555cff7238485b/research/2026-10-19-p5-interacting-reference/SUPPORT-RESOLVED-PAULI-REFERENCE-20261019.md
- Exact positive-minus-negative full-filter decomposition: https://github.com/Sodelin/Research-Commons/blob/29f7330049dfb4d99a99240288a6b72691ee3e24/research/2026-10-16-p5-strong-noise-coarse-graining/P5-EXACT-PSEUDO-LINDBLAD-LOCAL-DEFECT-15.md

These sources identify the original target and prior results. The separate review in this packet accepts only the explicitly scoped results below.

## 2. Operator conditional-expectation lemma

Put I_i(F)=sum_{a=x,y,z}||[sigma_i^a,F]|| and I(F)=sum_i I_i(F), always in operator norm. Let E_i be normalized partial trace at i, tensored with identity. The Pauli twirl gives

    F-E_i F=(1/4)sum_a(F-sigma_i^a F sigma_i^a),
    ||F-E_iF|| <= I_i(F)/4.

The maps E_i commute and are operator-norm contractions. Telescoping their product E_Z gives

    ||F-E_Z F|| <= (1/4)sum_{j in Z} I_j(F).             (1)

For any B supported on Z, [B,E_ZF]=0, hence

    ||[B,F]|| <= (||B||/2)sum_{j in Z} I_j(F).           (2)

This applies to arbitrary global F, not only local or product observables. Neither expansion into Pauli words nor a factor depending exponentially on |Z| occurs.

For p=(i,a), [H_Z,A_p]=0 unless i in Z, and ||[H_Z,A_p]||<=2||H_Z||. Applying (2) and summing the three axes at i proves

    sum_a ||[[H,A_(i,a)],F]|| <= sum_j M_ij I_j(F),
    M_ij=3 sum_{Z contains i,j}||H_Z||.                 (3)

M is entrywise nonnegative and symmetric. Its row and column sums are at most

    v=3 k h.                                           (4)

Equation (3) is the matrix-valued local supplier. Unlike replacing J by h in the old coefficient-norm proof, it is valid for general operator interactions.

## 3. Infinite-filter consequences

Let U_s F=exp(-iHs)F exp(iHs). The exact commutator evolution and unitary operator-norm isometry give the componentwise upper-derivative estimate

    D^+ I_i(U_sF) <= sum_j M_ij I_j(U_sF), s>=0,

also for reversed Hamiltonian. Finite-dimensional positive comparison yields

    bold I(U_sF) <= exp(|s|M) bold I(F).                 (5)

Differentiating U_s A_p, transporting F backwards, and using (3)--(5) gives

    sum_a ||[U_s A_(i,a)-A_(i,a),F]||
        <= [(exp(sM)-Id) bold I(F)]_i.                  (6)

All statements are uniform in finite volume; their proofs use finite sums in each volume.

For the complete infinite filters define

    Q_p=integral_0^infinity Phi_p(s)(U_s A_p-A_p)ds.

If tauB times the maximum row sum of M is less than one, integrating (6) against the original envelope gives

    sum_a ||[Q_(i,a),F]||
      <= [gamma tauB M(Id-tauB M)^(-1) bold I(F)]_i.    (7)

The inverse is the nonnegative convergent matrix series; no sign assumption on Phi_p is used. In particular

    sum_p ||[Q_p,F]|| <= eta I(F),
    eta=gamma v tauB/(1-v tauB).                        (8)

The same estimate holds with Q_p replaced by Q_p^dagger. This retains every bath time, allows different channel covariances, and has no q1 premise.

The denominator is admitted by the original box. The bound b0<=1 used here follows from b0 gamma<=Re k0_p<=|k0_p|<=integral |Phi_p|<=gamma:

    v tauB=3k h tauB <= b0 k/(4 nu 2^m) <= 1/(4 2^m).

For a separate estimate used below, the elementary bound I(B)<=6|Z| ||B|| on a Z-supported operator gives

    I([H,A_p]) <= 12 k h.

Together with (5), integration of the derivative of U_s A_p proves

    max_p I(Q_p) <= beta,
    beta=12 gamma k h tauB/(1-v tauB).                  (9)

Also q=max_p||Q_p||<=2 gamma h tauB. These are operator-influence bounds, not Pauli coefficient bounds.

As one consequence of the existing exact decomposition R*=G*-N*, with

    N*F=sum_p D[Q_p](F)/(2b_p),
    D[Q]F=(Q^dagger[F,Q]+[Q^dagger,F]Q)/2,

(8) gives

    ||N*F|| <= q eta/(2b0 gamma) I(F)
             <= gamma h v tauB^2/[b0(1-v tauB)] I(F).   (10)

This improves the previous exponential-in-k coefficient supplier. It still maps influence to operator norm and is not a same-norm small-gain estimate.

## 4. An integrated general-operator reference theorem

Consider only the auxiliary reference

    B*F=i[H,F]+D*F,
    D*F=sum_(i,a)2b_(i,a)(A_(i,a) F A_(i,a)-F),
    g=8 min_(i,a)b_(i,a).

For a uniform volume family one may instead use the common lower floor g=8b0 gamma throughout; all assertions remain valid.

For p=(i,a) let delta_p F=[A_p,F]. There is an exact intertwiner

    delta_p D*=D^(p) delta_p,                           (11)

where D^(p) agrees with D* everywhere except that the two noise coefficients transverse to a at site i are swapped. To check (11), act on the one-site Pauli basis: delta_a interchanges the two transverse axes, and annihilates I and sigma_a. Thus D^(p) remains a genuine on-site Pauli-noise generator with the same lower floor g.

Since delta_pF is traceless at i, the isotropic g(E_i-Id) part of D^(p) acts on this vector as -g delta_pF. The remaining noise plus i[H,.] generates a unital CP contraction. Consequently, at this instantaneous vector,

    D^+ ||delta_pF_t|| <= -g ||delta_pF_t||
                          + ||i[[A_p,H],F_t]||,
    F_t=exp(tB*)F.                                    (12)

This is a local derivative assertion. It does NOT assert that the interacting propagator preserves the subspace traceless at i. One can justify it by a first-order Taylor step: subtract the scalar -g action at the current vector, and bound the remaining generator step by its contractive semigroup; the O(dt^2) error vanishes after division by dt. This avoids an invalid finite-time factorization through a noninvariant subspace.

Summing axes and using (3) gives

    D^+ bold I(F_t) <= (-g Id+M) bold I(F_t).            (13)

If rho(M)<g, integration of positive matrix comparison proves

    integral_0^infinity bold I(F_t)dt
       <=(g Id-M)^(-1) bold I(F).                      (14)

A volume-uniform scalar sufficient condition is lambda=g-3kh>0, in which case

    integral_0^infinity I(exp(tB*)O_X)dt
        <= I(O_X)/lambda <=6|X| ||O_X||/lambda.         (15)

The initial cost is linear in support size, with no Pauli expansion. In the original box h<=g/8, all general two-body Hamiltonians satisfy lambda>=g/4. For k>=3 the original box does NOT guarantee lambda>0. The matrix-specific version may still apply in particular geometries but is not a universal admission argument. This reference theorem is weaker than the support-resolved Pauli theorem in some scalar-Pauli cases, stronger for some general operator interactions, and not a replacement for either the full general-k target or actual Redfield response.

## 5. Complete actual-generator join: the unabsorbed homogeneous term

Write actual R*=B*+V with

    VF=sum_q([A_q,F]Q_q-Q_q^dagger[A_q,F]).

The exact differentiated perturbation is

    delta_p(VF)=V(delta_pF)+T_pF,

    T_pF=sum_q (
      [[A_p,A_q],F]Q_q-Q_q^dagger[[A_p,A_q],F]
      +[A_q,F][A_p,Q_q]-[A_p,Q_q^dagger][A_q,F]).        (16)

In particular the homogeneous generator in the differentiated equation contains V(delta_pF). It cannot be replaced by a contractive reference without estimating that term. The signed complete filter has NOT vanished from this term.

The same-site Pauli algebra gives

    sum_(p,q)||[[A_p,A_q],F]||=4 I(F).

Here pairs on different sites and equal axes are zero; each surviving output axis appears twice with commutator coefficient two. For Hermitian F, or using adjoint invariance directly, (9) therefore gives

    sum_p||T_pF|| <= (8q+2beta) I(F).                  (17)

Introduce the full ordered second commutator quantity

    I_2(F)=sum_(p,q)||[A_q,[A_p,F]]||.

The homogeneous nonpositive contribution has the valid bound

    sum_p||V(delta_pF)|| <=2q I_2(F),                  (18)

not a bound by a constant times I(F). Combining the reference derivative calculation with (16)--(18) yields the actual all-volume differential inequality

    D^+ I(exp(tR*)F)
      <= -(g-v-8q-2beta) I(exp(tR*)F)
                          +2q I_2(exp(tR*)F).         (19)

Every filter in (19) is the complete same-H infinite filter. No contraction of R* is assumed. Equation (19) is not closed, even when its displayed first-gradient coefficient is positive.

There is no global uniform conversion I_2<=C I: a Pauli word of support s has exactly

    I(P)=4s,       I_2(P)=16s^2.

Thus its ratio is 4s. This algebraic observation identifies why the attempted transfer from (15) via (8) is invalid; it is NOT a reached-family counterexample. The original input support is fixed, and a proof might still control the integrated second-gradient term on the actual reached family, use signed homogeneous cancellations, or pay a controlled initial allowance. No such estimate is supplied here. Similarly a bounded first-gradient commutator of each Q_p does not prove that V acts boundedly on the first-gradient norm: (16) explicitly displays the missing term.

## 6. Scope of the advance and remaining obligation

New candidate positive suppliers are (3), (7), the admitted polynomial velocity 3kh, and the general-operator reference estimate (14)--(15), including anisotropic noise. The exact actual join (16)--(19) says where the attempt stops. They neither establish the full-filter q1 guard nor require it.

To complete this route one would need a signed or reached-family estimate controlling the homogeneous second-gradient contribution in (19), and a way to obtain a reference/actual response margin for the entire original general-k box. The original square-window comparison would then still need the proper endpoint/defect insertion using that actual response. Nothing here permits changing the comparator, restricting the initial states, imposing a stronger noise threshold silently, or identifying a static signed resolvent with an integral of norms.

## 7. Finite verification

`check_operator_incidence.py` executes 87 numerical controls with fixed RNG seed 20261020:

- General non-Pauli Hermitian interactions on two, three, and four qubits, including full-support terms, checking (3) and (6).
- Full filters evaluated exactly through spectral denominators for Phi(s)=(gamma/tauB)exp(-s/tauB)exp(-i omega s), checking (7). This test covariance is a broader envelope fixture and is NOT asserted to satisfy the original thermal KMS assumption. The theorem uses only the envelope, so the test is an algebra/norm diagnostic, not thermal admission evidence.
- Exact finite matrix reconstruction of (16) to numerical tolerance, and directional operator-norm derivatives checking (19).
- All one-qubit Pauli-basis cases of (11) with unequal noise rates.

No finite test proves the all-volume hand argument. The script neither evaluates the original square-window comparator nor certifies full P5. The independently authored exact algebra checks and scoped review are in `independent-review/`. The preserved candidate source hash is recorded there; this successor changes status and presentation, not the mathematical assertions.
