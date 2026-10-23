# P5 chains/rings: independent scoped hand review and comparator reconstruction

23 October 2026. Reviewer: dot (OpenAI), for Nolan.

**Verdict: scoped HAND PASS for the complete actual-Redfield response and original-comparator theorem stated below.** This is an independent coordinating AI hand review, not external peer review, an executed calculation, a Lean/kernel check, or a historical-priority determination. The reviewed boundary/filter proof is attributed to Codex, 21 October 2026, “Actual noncommuting Redfield comparison on chains and rings.” The comparator calculation in Section 5 below is the reviewer's independent reconstruction from retrieved, explicitly identified original definitions and accepted influence suppliers.

The author supplied a complete self-reviewed candidate. That report alone was not treated as acceptance. The exact supplied scientific text was read in full. Its named companions `P5-SCOPE.md` and `GENERATOR-COMPARISON.md` were not recovered or read. This review therefore does **not** certify their byte identity, their wording, or the identity of their numbered equations. Instead it spells out the actual hypotheses and generators used, and checks the complete mathematical implication with those definitions. Missing companion bytes do not constitute a mathematical gap in this explicit restatement.

## 1. Exact accepted scope

For every finite qubit graph of maximum degree two, allow arbitrary paths, rings and their disjoint unions. Let

    H = sum_Z H_Z,     H_Z = H_Z^dagger,
    h = max_i sum_(Z contains i) ||H_Z||op,

where every term is supported on one vertex or one edge. Interactions need not commute and need not themselves be Pauli words. Use the same H in the bath filters, Redfield generator and comparator. Keep the common geometry bounds k=2 and m=nu=3 even for small components.

At every site use exactly the three on-site Hermitian Pauli coupling operators A_p, with independent stationary bath channels. Their correlations obey

    Phi_p(-s) = conjugate(Phi_p(s)),
    |Phi_p(s)| <= (gamma/tauB) exp(-|s|/tauB),
    b_p := Re integral_0^infinity Phi_p(s) ds >= b0 gamma > 0.

Retain positive-type thermal/KMS admission, as in the original source definition. The estimates use the envelope and floor; positive type supplies the unchanged comparator's GKSL property. The theorem does not impose a new fixed-temperature limit. It applies to any admitted thermal family satisfying these inequalities, not to a claim that arbitrary physical materials do so.

The exact parameter box is

    h <= b0 gamma,      0 < x = gamma tauB <= 1/288,
    T = sqrt(tauB/gamma).

In particular gamma,tauB,b0 are positive. The floor and envelope imply b0<=1. Define U_s F=exp(-iHs) F exp(iHs), I(F)=sum_p ||[A_p,F]||op, and use normalized-trace Hermitian Pauli coefficients f_P. Put

    a(F)=sum_(P != I) |f_P|,
    w(F)=sum_(P != I) |supp P| |f_P|,
    c_X=sqrt(4^|X|-1).

For an observable O_X initially supported on a fixed finite set X, the accepted conclusions are

    integral_0^infinity I(exp(t R*)O_X) dt
      <= 8 c_X ||O_X||op / (b0 gamma),

and, for every finite volume and every t>=0,

    ||(exp(t L_T*) - exp(t R*))O_X||op
      <= 8 B(T) c_X ||O_X||op / (b0 gamma).

Here the independently verified valid constant is

    v=6h,
    B(T)=2gamma[(exp(vT)-1)/(vT)-1]
           +2gamma hT+2gamma tauB/T,

with the bracket interpreted continuously as zero at v=0. With j=h/gamma and z=6j sqrt(x), this gives exactly

    error <= (8 c_X/b0)[(6 exp(z)+2)j+2] sqrt(x) ||O_X||op.

The constants are independent of elapsed time, volume, channel-specific covariance within the stated common bounds, and initial density matrix. For Hermitian O_X the operator-norm estimate bounds all initial-state expectation differences, including entangled and volume-dependent states. No positivity or contractivity of actual Redfield evolution is assumed.

## 2. Actual generator and unchanged target

The following are the original equations (2)–(4) of the [16 October source](https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md). The source's original dynamical theorem was commuting; here only its explicitly defined generators and bath contract are imported. Noncommuting dynamics are supplied by the reviewed 21 October proof, not inferred from that older theorem.

Write A_p(-s)=U_s A_p. The Schrödinger-picture generator is

    R(rho)=-i[H,rho]+sum_p integral_0^infinity {
      Phi_p(s)[A_p(-s)rho,A_p]
      +Phi_p(-s)[A_p,rho A_p(-s)] } ds.

The comparator is L_T(rho)=-i[H+H_T,rho]+D_T(rho), where

    D_T(rho)=(1/T)sum_p integral_0^T ds integral_0^T ds'
      Phi_p(s'-s){A_p(-s')rho A_p(-s)
                 -(1/2){A_p(-s)A_p(-s'),rho}},

    H_T=(i/(2T))sum_p integral_0^T ds integral_0^s ds' {
      Phi_p(s'-s) A_p(-s)A_p(-s')
      -Phi_p(s-s') A_p(-s')A_p(-s)}.

Thus the finite square dissipator and the original ordered Lamb shift are both retained. There is no secularization, replacement by an auxiliary reference, filter cutoff, or change to the observation target. Positive-type covariance gives a positive finite-window correlation kernel; H_T is Hermitian. Consequently exp(t L_T*) is unital completely positive and operator-norm contractive.

Taking the adjoint of the displayed R directly gives, with Q_p=integral_0^infinity Phi_p(s)(U_sA_p-A_p)ds,

    R*F=i[H,F]+sum_p 2b_p(A_p F A_p-F)+VF,
    VF=sum_p([A_p,F]Q_p-Q_p^dagger[A_p,F]).

The order of the two products and the sign in V have been checked, rather than inferred from a norm bound. Freezing the filter at A_p gives 2 Re integral(Phi_p) times A_p F A_p-F. In particular R*I=0 and R* preserves Hermiticity. Trace preservation of R* is not assumed.

## 3. Independent check of the finite boundary/full-filter proof

For an interval J in a connected path/ring component C, let D_J=-i[H_J,.], where H_J includes exactly the terms supported inside J. The finite-dimensional variation-of-constants identity is

    U_t^C F=U_t^J F
      +integral_0^t U_(t-s)^C (D_C-D_J)U_s^J F ds

for F supported in J. Terms wholly outside J commute with it. There are at most two boundary edges, and the sum of the crossing commutator-map norm bounds is at most 4h. Every internal propagation remains an exact unitary isometry; it does not incur a factor proportional to the number of terms inside J.

After crossing an edge, choose the enlarged interval including its outside endpoint. This choice is legitimate even when a particular resulting operator has smaller actual support: the operator is still supported inside the enlarged interval. Hence every recursion enlarges the selected interval by one vertex. Ring closure and termination at C are exact. The finite expansion has depth at most |C|-1, not an infinite formal Dyson series.

At depth n the total operator-norm bound is (4ht)^n/n!, with each term supported on at most n+1 sites. This includes both boundary choices at each stage without double counting a separate volume factor. Pauli orthogonality gives ||F||P<=2^ell||F||op for support of size ell. Separating the depth-zero one-site orbit yields

    ||U_t A_p-A_p||P <=4ht+2(exp(8ht)-1).

The same argument holds for disconnected graphs because the component of p is invariant for this orbit. It is valid for arbitrary noncommuting edge interactions.

The bath envelope can now be integrated against this scalar bound. Since 8h tauB<=1/36,

    ||Q_p||P <= q1,
    q1=gamma h tauB[4+16/(1-8h tauB)],
    q1/(b0 gamma) <=179/2520.

The integral calculation was checked directly: its two terms are 4gamma h tauB and 16gamma h tauB/(1-8h tauB). This bounds the complete actual oscillatory filter uniformly; it neither assumes finite support of Q_p nor interchanges the failed absolute full-H Taylor majorant with an infinite bath integral.

## 4. Independent check of actual damping and response

For a two-site term, precisely twelve Pauli words are nonidentity at a specified site. Normalized Hilbert–Schmidt orthogonality and Cauchy–Schwarz therefore bound the coefficient sum incident to that site by sqrt(12)||H_Z||op. A one-site term has only three. Summing original labelled terms and then optionally merging coefficients gives

    J=max_i sum_(P nonidentity at i)|j_P| <=sqrt(12)h.

For an input Pauli word of weight ell, the frozen noise decays by at least 8b0 gamma ell. The Hamiltonian outgoing coefficient sum is at most 2J ell. Exactly two axes at every occupied site anticommute with the word; each commutator has Pauli norm two. Submultiplicativity and adjoint invariance of the full Pauli norm give ||VP||P<=8q1 ell.

Identity annihilation makes the nonconstant coefficient system autonomous. Its absolute-value upper derivative satisfies

    D^+ a(exp(tR*)F) <=-kappa w(exp(tR*)F),
    kappa=8b0 gamma-2J-8q1.

The arithmetic is correct:

    kappa/(b0 gamma) >=8-4sqrt(3)-179/315 >1/2.

The strict comparison reduces to 4367^2-48*630^2=19489>0, with positive quantities before squaring. Finite-horizon integration and monotone convergence then give integral w<=a(F)/kappa. Finally I(F)<=4w(F) and a(O_X)<=c_X||O_X||op prove the actual-response bound.

The scalar output is not dropped from the actual evolution: its derivative is bounded by 8q1 w(F_t), hence has finite total variation. It cannot feed back into the nonconstant system because R*I=0. This resolves the relevant nonunital/identity-row issue without attributing contraction or positivity to R*.

## 5. Independent original-comparator reconstruction

This section supplies a full comparison directly; it does not claim to reproduce the unread companion's bytes. It uses the original definitions in Section 2 and the [20 October operator-incidence proof, Sections 2–3](https://github.com/Sodelin/Research-Commons/blob/04c9808f1fc4ec3c1c57cdbca200e91e82d32d5d/research/2026-10-20-p5-operator-incidence/PROOF.md). The ordered-triangle algebra also agrees with the separately reviewed [19 October support-resolved proof, Section 6](https://github.com/Sodelin/Research-Commons/blob/71fc996ac0260a49dd443a9112555cff7238485b/research/2026-10-19-p5-interacting-reference/SUPPORT-RESOLVED-PAULI-REFERENCE-20261019.md).

### 5.1 Ordered-triangle identity, with signs checked

Define

    C_z(A,B)F=z[A,F]B-conjugate(z)B[A,F],
    M(u)F=sum_p C_(Phi_p(u))(A_p,U_u A_p)F.

The actual R* is i[H,.]+integral_0^infinity M(u)du. In the square window, set the earlier operator A=U_rA_p, the later one B=U_(r+u)A_p, and z=Phi_p(u). The two adjoint dissipator triangles sum to

    conjugate(z)(BFA-{BA,F}/2)+z(AFB-{AB,F}/2).

The original Lamb Hamiltonian integrand is (i/2)(conjugate(z)BA-zAB). Adding its adjoint commutator i[Htriangle,F] cancels precisely the unwanted halves, leaving C_z(A,B)F. Hence exactly

    L_T*-i[H,.]=(1/T)integral_0^T dr integral_0^(T-r)du
      sum_p C_(Phi_p(u))(U_rA_p,U_(r+u)A_p).

No A/B commutation is used.

### 5.2 General-operator influence movement

For completeness the imported supplier's actual assumptions were checked. The Pauli twirl and conditional expectations give, for B supported in Z,

    ||[B,F]|| <=(||B||/2)sum_(j in Z) I_j(F).

Thus, with M_ij=3 sum_(Z contains i,j)||H_Z||, the derivative source is bounded by M I(F). Its row/column sums are at most v=3kh=6h. Unitary commutator evolution and positive matrix comparison yield

    sum_p ||[U_rA_p-A_p,F]|| <=(exp(vr)-1)I(F).

This uses the general operator incidence h, not an invalid substitution of h for Pauli incidence J. Separately, unitary isometry and ||[H,A_p]||<=2h imply

    ||U_(r+u)A_p-U_uA_p||=||U_rA_p-A_p||<=2hr.

Both U_(r+u)A_p and U_uA_p have norm one.

### 5.3 Compare actual integrands, not frozen integrands

Expand the bilinear difference

    C_z(U_rA_p,U_(r+u)A_p)-C_z(A_p,U_uA_p)

by moving its first and then second operator. Summing the resulting norm bounds gives

    sum_p ||difference applied to F||
      <=2(gamma/tauB)exp(-u/tauB)
            [(exp(vr)-1)+2hr] I(F).

Here channel-dependent Phi_p are allowed because their common envelope is used termwise. Comparing directly with the actual u-dependent Redfield integrand avoids introducing a separate frozen-filter error.

The actual integrand itself satisfies ||M(u)F||<=2(gamma/tauB)exp(-u/tauB)I(F). The part omitted by the triangle, averaged over 0<=r<=T, is therefore at most

    (2gamma tauB/T)(1-exp(-T/tauB))I(F)
      <=2gamma tauB I(F)/T.

For the movement part, extend the positive u envelope integral to infinity and integrate r. The first summand gives 2gamma[(exp(vT)-1)/(vT)-1]; the second gives 2gamma hT. Consequently

    ||(L_T*-R*)F||op <=B(T)I(F)

with exactly B(T) in Section 1. This also covers h=0 by continuity (the actual movement is then zero).

### 5.4 Duhamel and the explicit window constant

Use finite-time Duhamel with exp((t-s)L_T*) outside and exp(sR*) inside. Only the former is contracted. Sections 3–4 then give

    error <=B(T) integral_0^t I(exp(sR*)O_X)ds
          <=4B(T)a(O_X)/kappa
          <=8B(T)c_X||O_X||op/(b0 gamma).

For z=vT>=0,

    (exp(z)-1)/z-1
      =integral_0^1(exp(zs)-1)ds <=(z/2)exp(z),

again interpreted continuously at zero. Substituting T=sqrt(tauB/gamma) and v=6h yields

    B(T)/gamma <=[(6exp(z)+2)j+2]sqrt(x),

which is the claimed explicit original-comparator estimate. No additional actual-response, locality, temperature, or positivity premise remains in this scoped chain.

## 6. Review coverage, attribution and remaining boundaries

Read and checked:

1. The entire user-supplied Codex 21 October manuscript, including the finite boundary expansion, full-filter integration, operator-to-Pauli incidence, actual coefficient/scalar equations and target comparison claim.
2. The explicitly pinned original generator and bath definitions cited in Section 2.
3. The 19 October support-resolved conditional argument and its [independent review](https://github.com/Sodelin/Research-Commons/blob/71fc996ac0260a49dd443a9112555cff7238485b/research/2026-10-19-p5-interacting-reference/SUPPORT-RESOLVED-INDEPENDENT-REVIEW.md), including the ordered-Lamb algebra and actual signed-filter implication.
4. The 20 October operator-incidence proof, especially the concrete bodies of Sections 2–3 supplying v=3kh. Its later unresolved general-geometry second-gradient join is not assumed or needed for this path/ring coefficient proof.

The substantive new input of the reviewed author manuscript is its finite interval-boundary full-filter bound and its correct general-two-qubit coefficient count. Existing conditional response and comparison mechanisms are reused with attribution. The independent review also supplies the direct-integrand B(T) reconstruction above. No claim is made that either mechanism is historically new.

The exact named companions remain **source-identity unverified**, not falsely claimed read. A public ordered-triangle formal source reportedly pins `GENERATOR-COMPARISON.md` to SHA256 `74e821c317819bbac9a42fed61630b7e23685d3d657d8b837bf910deb8f71034`; a hash without recovered bytes does not verify that document. The mathematical PASS here is for the full explicit model and formulas above.

The following are not accepted by this review:

- Arbitrary bounded-degree geometry, general k, or the full original P5 master. The finite interval argument depends on a uniformly bounded interval boundary, and cannot be silently transplanted to a growing-boundary graph.
- A weakened/noiseless floor, missing on-site channels, fixed h with arbitrarily weak gamma, or an enlarged box for small volumes.
- Microscopic system-plus-bath error, multi-time interventions, a global trace-distance theorem, computational efficiency, experimental validation, or a material-specific bath assertion.
- Compiler/API/kernel correctness, author-file byte identity, independent human peer review, or worldwide novelty.

No scientific runtime, numerical controls or formal elaboration was performed in this review. Previously accepted narrower/reference results remain intact; this verdict supplies a stronger restricted actual-source endpoint rather than reopening those proofs or declaring the general problem solved.
