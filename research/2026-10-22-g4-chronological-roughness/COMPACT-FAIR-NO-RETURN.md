# Cross-cap energy and positive-covector exclusion of compact fair dust

22 October 2026. dot (OpenAI-assisted research), prepared for Nolan.
Status: new hand-proof candidate, CONDITIONAL on acceptance of the full-operator identity (2) until its archived source evidence has been independently audited. No new runtime execution. The measure/product argument has received preliminary hand review, not unconditional theorem acceptance.

## 1. Claimed theorem

Fix a compact set K of (h,u,v) with 0<h_min<=h<=h_max<4 and H>0. There is epsilon_0(K,H)>0 such that NO nonempty finite serial word with cells

    X_i=2h_i epsilon^2-4u_i epsilon^3+8v_i epsilon^4,
    Y_i=2h_i epsilon^2+4u_i epsilon^3+8v_i epsilon^4,
    g_i=1/2,
    (h_i,u_i,v_i) in K,

and strictly positive ordinary connectors has COMPLETE forest kernel E_T through cap nine with 0<T<=H and epsilon<epsilon_0.

There is no bound on the finite cell count N and no small-total-bigon-expenditure assumption. The common auxiliary epsilon, compact normalized shapes, strictly positive h_min, exactly fair independent routing, serial grammar, and bounded total target time are essential scope restrictions. This is not a theorem for the broader fair-base g=1/2+epsilon w chart. It does not settle arbitrary multiscale or arbitrary admitted rival sources, or original G4.

## 2. Inputs and their provenance

Use the accepted Oct8 cap-nine 9/7/6/4 source representation, actual source estimates, and chronological Green identity, as in PROOF.md in this packet. Their constants extend from S=N epsilon^2<=1 to S<=S_max=2H/h_min, exactly as proved and reviewed there. Set

    alpha_i=h_i^3-12u_i^2,
    c_i=-log b2(B_i),
    s_i=ordinary suffix time + sum of later c_j,
    p_i=ordinary prefix time + sum of earlier c_j.

Then

    T=p_i+c_i+s_i, 0<=p_i,s_i<=H,
    c_i=O_K(epsilon^2), N epsilon^2<=S_max.                 (1)

For the complete cap-six source use its ordinary generator Q, singleton row v0, pair-normalized J=B exp(-cQ), and ell=P[:,14] from the accepted Oct21 positive-covector packet. Its exact full-forest source facts are

    J=I+epsilon^6 L3(k,A^2)+epsilon^8 L4(k,A^2)
          +epsilon^10 L5(k,A^2)+O_K(epsilon^12),
    L3=k^3 U3+A^2 V3,
    V3=-(3/4)U3,                                         (2)
    v0 Ad_p(L3)ell=v0 Ad_p(L4)ell=0,
    v0 Ad_p(L5(k,A^2))ell=k^2 A^2 exp(-9p).                (3)

Here k=h+4v epsilon^2 and A=-4u, which exactly reproduces the physical arms above. The expansion is uniform for the compact parameters and p in [0,H]. The identities in (3) are the accepted universal lower-space annihilation and grade-five covector identity, not finite sampled placements.

Important source check for (2): the archived Oct20 labelled-forest calculation checked V3+(3/4)U3=0 on complete singleton rows with 3,4,5,6 roots; normalized rows at 1,2 roots are identically zero. Every other forest row is obtained by grafting the existing opaque root subtrees into the corresponding singleton row. Consequently this is a full cap-six OPERATOR identity, not merely one scalar covector equation. The calculation uses, for each fixed fair routing, H=G_left+G_right and D=G_left-G_right, and the explicit formulas

    V3=(1/2) E[D^2]+Q/4,
    U3=(4/3) E[H^3]+Q^2/2-Q^3/6.

Thus the finite identity is independently specified by actual routing assignments and ordinary merger generators. It was recorded before this continuation; it has not been rerun here. The reviewed public covector packet alone did not state this entire matrix proportionality, so review must not infer it merely from the two scalar c0 identities.

Substitution in (2),(3), including the epsilon-dependent k, gives uniformly

    Ad_(p_i)(J_i-I)=epsilon^6 alpha_i Ad_(p_i)(U3)
                       +O_K,H(epsilon^8),                (4)
    v0 Ad_(p_i)(J_i-I)ell
      =16 epsilon^10 h_i^2 u_i^2 exp(-9p_i)
                       +O_K,H(epsilon^12).               (5)

Terms from varying k in L3 and L4 are killed by ell, since the annihilation in (3) holds on the whole source parameter neighborhood and at every position.

All matrix estimates may use the induced maximum absolute row-sum norm, which is submultiplicative, on the complete cap-six 20-orbit forest representation. Its states retain the full rooted tree shapes, not just block sizes. The underlying labelled construction precedes this exact exchangeable quotient. The full labelled source routes existing opaque subtrees as indivisible current roots; grafting these subtrees into every output of the corresponding singleton-root row proves the row identity for arbitrary incoming forests. Label permutation symmetry makes the orbit representation exact for this source. Fixed row/covector norms are absorbed into constants.

## 3. Cap-nine energy makes the normalized alpha measure weakly zero

For the suffix-normalized cap-nine representation put

    a_i=exp(15s_i)xbar_i,
    xbar_i=(alpha_i/15)epsilon^6+O_K(epsilon^8),
    F(x)=sum_i a_i sinh(6|x-s_i|), I=[-1,H+1].

The accepted energy estimate, with the bounded-S extension, gives

    ||F||_(H^1(I)) <= C N epsilon^8,
    F''-36F=12 sum_i a_i delta_(s_i).                      (6)

Define the finite signed measure

    mu_epsilon=(1/N)sum_i alpha_i delta_(s_i).

Its total variation is uniformly bounded because K is compact. Divide (6) by N epsilon^6 and test against chi(x)exp(-15x)phi(x), where chi is a fixed compact cutoff equal to one on [0,H]. For any fixed smooth phi this gives

    |integral phi d mu_epsilon| <= C_phi epsilon^2.         (7)

The uniform total-variation bound and density of smooth tests in continuous functions on [0,H] imply

    mu_epsilon -> 0 weakly as epsilon -> 0.                (8)

This assertion does not multiply weak limits of different source parameters. It controls precisely the signed alpha measure. The h-alpha correlation that survived the previous roughness proof remains free at this stage.

## 4. Complete cap-six equality and its count-uniform remainder

Let D_i=Ad_(p_i)(J_i-I). Actual chronological factorization gives

    W E_(-T)=product_(i=1)^N (I+D_i).

Because ||D_i||<=C epsilon^6 and N epsilon^2 is bounded, the sum of all products of at least three D_i has norm at most C N^3 epsilon^18. This follows from the exponential norm-product bound, not a fixed-count expansion. Replacing each factor in a pair by its leading term in (4) has total error O(N^2 epsilon^14).

Apply v0 and ell to exact complete cap-six equality. Equations (4),(5) yield

    0=16 epsilon^10 sum_i h_i^2 u_i^2 exp(-9p_i)
      +epsilon^12 sum_(i<j) alpha_i alpha_j K(p_i,p_j)
      +O(N epsilon^12+N^2 epsilon^14+N^3 epsilon^18),       (9)

where the fixed smooth kernel is

    K(p,q)=v0 Ad_p(U3) Ad_q(U3) ell.

Divide by N epsilon^10. The remainder tends to zero uniformly: its three terms are O(epsilon^2), O((N epsilon^2)epsilon^2), and O((N epsilon^2)^2 epsilon^4), respectively.

## 5. Weak alpha cancellation removes the leading ordered quadratic interaction

To handle the ordered sum without discarding chronology, pass to an arbitrary allegedly returning sequence epsilon->0 and then a subsequence with T->T_* in [0,H]. Since p_i=T-s_i-c_i, replacing p_i by T-s_i in K changes the normalized pair sum by O(epsilon^2), uniformly.

Define a symmetric continuous kernel on [0,H]^2 by

    L_T(s,t)=K(T-s,T-t) if s>t,
             K(T-t,T-s) if s<t,
             K(T-s,T-s) if s=t.

The two definitions agree on the diagonal, so L_T is continuous even if its first derivatives have a jump there. Dependence on T is uniform and continuous on the compact domain. The ordering s_i>s_j for i<j is exactly the original physical ordering.

One has the exact identity

    (1/N^2)sum_(i<j) alpha_i alpha_j K(T-s_i,T-s_j)
      =(1/2) integral L_T d(mu_epsilon tensor mu_epsilon)
        -(1/(2N^2))sum_i alpha_i^2 L_T(s_i,s_i).            (10)

By (8), bounded total variation, and approximation of a continuous two-variable kernel by finite sums f(s)g(t), the integral in (10) tends to zero. Uniform continuity permits replacing T by T_*. The diagonal correction is O(1/N). After multiplication by N epsilon^2, its contribution is O(epsilon^2), even if N does not tend to infinity. Hence the quadratic term in (9), divided by N epsilon^10, tends to zero.

This step uses the source identity L3=alpha U3. It would be invalid if other independent leading controls survived, or if one replaced an ordered kernel by a discontinuous approximation without checking its diagonal.

## 6. The local positive term cannot disappear

Exact D3 calibration gives

    (1/N)sum_i alpha_i=O_K(epsilon^2),
    (1/N)sum_i u_i^2=(1/12N)sum_i h_i^3+O_K(epsilon^2).

For sufficiently small epsilon this is at least h_min^3/24. Therefore

    (1/N)sum_i h_i^2 u_i^2 exp(-9p_i)
      >=exp(-9H)h_min^5/24>0.                              (11)

After dividing (9) by N epsilon^10, Sections4-5 make every term except the nonnegative local term tend to zero, whereas (11) bounds that term uniformly away from zero. This is the contradiction. A sequential contradiction proves the claimed existence of epsilon_0(K,H).

## 7. Source pins, attribution, and exact remaining master gap

Cap-nine source and Green energy:
https://github.com/Sodelin/Research-Commons/tree/efd8ed7a9d23be13eede73019618c4cd4b62c23e/research/2026-10-08-dot-g4-fair-energy-hazard-1220z

Cap-six complete quotient and lower-space annihilation:
https://github.com/Sodelin/Research-Commons/tree/08001e2b298d461cade7bdcd2eda4079b5cd82c3/research/2026-10-21-g4-graded-quotient

Positive cap-six covector and transport identities:
https://github.com/Sodelin/Research-Commons/blob/6b876e4a138ad8d9c37ad78a6a95bd4fbf5744d8/research/2026-10-21-g4-positive-base-obstruction/ADDENDUM.md

The full-operator proportionality in Section2 is an additional explicitly identified archived finite source input, not an inference from rank. Its archived files are probe_leading.py and probe_leading.log dated Oct20. The mathematical formulas are stated above so review does not rely on implementation names alone. No new independent execution is claimed.

This is a proposed cross-result strengthening for exactly fair compact parabolic sources. It does not exclude shape escape h_min->0, unbounded normalized asymmetry, arbitrary unequal scales, non-weak cells, genuinely biased coins, nonserial sources, or a fixed-target all-panel rival construction using those possibilities. The original COMMON-certificate finite-panel alternative is likewise unresolved. No separately chosen cap targets, external mixtures, signed physical edges, or additive overlapping charges are introduced. The prior diagonal-only and cap4/cap5 complete returns remain valid.
