# Actual off-unit critical cells defeat a uniform normal-compactness floor

Contributor: Codex G5, 8 October 2026. **Hand proof candidate; independent root review requested.** This is a source-valid failure of one step in the complete G3 witness-bound attempt. It is not a counterexample to an input-dependent bound on ONE witness, and it supplies no NO input. No mathematical source execution, symbolic calculation, root isolation, QE or compiler run was performed.

## 1. The universal count inference being tested

The accepted supplied-normal count theorem computes a positive pair-loss floor for each fixed algebraic normal's nonunit critical components. The new finite real-normal neutral-carrier catalogue removes the need to guess infinitely many neutral curve types. A proposed complete next step was to normalize the unknown normal, remove/handle its finite neutral carriers by the accepted value-space/ARC providers, and use compactness of the remaining normal incidence to obtain a uniform floor for every remaining critical cell. That floor would bound actual INTEGER occurrences before bounded-source RCF.

The following family refutes this proposed floor, even with rational normals, all rare-append inequalities, compact normalized normals, and NO neutral-reaching critical carrier for each member. The source targets vary with the family parameter and have one-cell witnesses. Thus the result does not refute target-derived extraction, a different source-count theorem, or general decidability.

## 2. Reused actual source and sparse-polynomial facts

Use cap seven, with SIX positive exponents

    Lambda=(1,3,6,10,15,21),
    f_lambda(p,q)=1-p+p q^lambda,
    H_lambda(p,q)=-log f_lambda(p,q),
    F_c(q)=sum_lambda c_lambda(1-q^lambda).

All parameters below are natural and strict. A freely parameterized, unexposed COMMON private word has this normalized Bernoulli factor; its full coherent capped forest law is supplied by the inherited actual COMMON compiler. The old paired sparse normal, generalized Descartes/Chebyshev root count, and fixed-normal neutral exclusion retain their attribution.

Fix r=1/2. There is a unique rational row c_0 satisfying

    sum c_0=1, c_0 Lambda=0,
    F_0(r)=F'_0(r)=F_0(r^2)=F'_0(r^2)=0.

Here F_0=F_(c_0). Invertibility follows directly from the inherited sparse-root count. In the homogeneous system sum c=0 removes the constant term, leaving at most six nonzero positive-power terms and hence at most five positive roots counted with multiplicity. The required double roots r,r^2,1 would give six, so the homogeneous row is zero. For the normalized solution, F_0 has seven possible sparse terms, exactly those six forced positive roots counted with multiplicity, and F_0(0)=1. Consequently all three roots are EXACTLY double, there are no other positive roots, F_0 is positive on [0,1] away from r,r^2,1, and its second derivative is positive at each of these three roots.

Put C=F_0(r^3)>0; C is rational. No numerical value for c_0 or C is needed or asserted.

## 3. The varying rational actual normal

For p near zero define c_p by the SIX linear equations

    sum c_p=1, c_p Lambda=0,
    c_p H_p(p,r)=0, c_p H_q(p,r)/p=0,
    F_p(r^2)=2 C p, F'_p(r^2)=0.                 (1)

The quotient H_q/p has its rational analytic extension at p=0. At zero, its row is D'(r), while H_p's row is D(r), where D_lambda(q)=1-q^lambda. Thus (1) specializes to the invertible system in Section 2. Its coefficient matrix is rational-analytic in p with rational coefficients. For all sufficiently small positive p it remains invertible; c_p is a rational function of p, c_p tends to c_0, and c_p is rational whenever p is rational. All criticality conditions refer to the SAME actual cell (p,r).

For a bounded row c, uniformly near this fixed r,

    c H(p,q)=p F(q)
       +p^2[2F(q)-F(q^2)]/2
       +p^3[3F(q)-3F(q^2)+F(q^3)]/3+O(p^4).    (2)

When differentiating (2) in p or q to impose criticality, c is held FIXED and only afterwards set to c_p. Differentiating the path c_p itself would be incorrect.

The first critical equation and F_p(r^2)=2Cp give

    F_p(r)=C p^2+O(p^3).                       (3)

Indeed H_p has expansion F+p(2F-F(q^2))+p^2(3F-3F(q^2)+F(q^3))+O(p^3); F_p(r^3)=C+O(p). Solving its zero equation gives (3). The second critical equation, divided by p, has expansion

    F'(q)+p[2F'(q)-2qF'(q^2)]/2
       +p^2[3F'(q)-6qF'(q^2)+3q^2F'(q^3)]/3
       +O(p^3).

Since F'_p(r^2)=0, it follows that

    F'_p(r)=O(p^2).                           (4)

Substitution of (3) and (1) in (2) yields

    c_p H(p,r)=C p^3/3+O(p^4)>0               (5)

for all sufficiently small positive p. Thus this is an OFF-UNIT critical value. Clearing a rational denominator of c_p makes its positive monomial level exp(-L c_p H(p,r)) different from one; this statement involves no comparison of an arbitrary transcendental expression to zero because (5) proves its strict sign.

## 4. All rare-cone inequalities hold

The full polynomial F_p is strictly positive for every q in [0,1), and has exactly the fixed double zero at q=1, for sufficiently small positive p.

To prove this uniformly, choose disjoint small closed neighborhoods of r,r^2,1 on which F_0'' is positive. Continuity gives a common kappa>0 with F_p''>=kappa on each neighborhood for small p. At r^2 the exact derivative is zero and the value is 2Cp>0, so that neighborhood has positive minimum. At r, (3) gives value at least C p^2/2, while (4) bounds the derivative by M p^2. The strong-convexity lower bound there is

    F_p(q)>=F_p(r)-[F'_p(r)]^2/(2 kappa),

which is positive for small p; the critical minimum moves by O(p^2), and the possible decrease is only O(p^4). At one, F_p(1)=F'_p(1)=0 exactly, so the same curvature bound gives strict positivity for nearby q<1. On the remaining compact set, F_0 has a positive minimum and F_p converges uniformly to F_0. These pieces cover [0,1].

Consequently every c_p meets the polynomial rare-append condition F_p(q)>=0 on [0,1], in addition to ordinary neutrality and BOTH actual two-sided cell derivative equations. This is not a claim that c_p H is globally nonnegative for every strict cell, or that this covector supports the entire source fibre.

There is no neutral-reaching critical carrier for any FIXED c_p. An interior rare node would require F_p(q)=0 by the accepted fixed-normal neutral theorem, contradicting strict positivity. That theorem excludes every fixed-normal critical approach to q=1; its leading-exponent argument also excludes q=0 when p tends to zero, as it must in a vanishing-pair-loss approach there. These are precisely the endpoint cases with p(1-q) tending to zero. No assertion excludes general critical accumulation at the killing corner p=1,q=0 or other nonneutral critical curves. Each fixed c_p therefore has its own positive critical-loss floor; the claim refuted below is a UNIFORM floor as p and the normal vary.

## 5. Strict physical admission and failure of the proposed uniform floor

For every sufficiently small rational p>0 take the actual word

    K_p=E(1/2) B_COMMON(1/4,1/2,p) E(1/2).

Its ordinary connectors and both arm survivals are strictly between zero and one, and its natural coin p is interior. Insert it only on an inherited eligible fresh unexposed cut bridge; original protected IDs, parent occurrences and the exterior are retained. Its actual survival is X=(1/8) r^B with B~Bernoulli(p), so its cap-seven moments are the rational tuple

    m_lambda=(1/8)^lambda f_lambda(p,r).

The SAME source and parameter tuple supplies every coordinate; no external mixture, independent row law, new exposed coin, or nonphysical normalized zero arm is introduced. Original calibrated topology transfer, when used, is the inherited SAME-core calibration theorem, not a new all-core NO claim. This family is already YES by the displayed finite word.

Its nonordinary normalized cell has pair loss p(1-r)=p/2, and first-coordinate log loss -log(1-p/2), both tending to zero. At that cell c_p is critical, ordinary-neutral, off-unit, rational, and satisfies ALL the rare inequalities. The rows converge to a nonzero c_0. Dividing each c_p by its Euclidean norm puts them in a compact unit-normal set; the divided rows are algebraic, and criticality, rare positivity and the nonunit property persist.

Hence there is NO positive cap-only or normalized-normal-compactness floor for these off-unit critical cells, even after excluding every neutral carrier of each selected normal. Finite carrier/value/node catalogues do not repair that inference. The present targets vary and admit one-cell witnesses; there is no assertion that a fixed target needs unbounded minimal count, that input height cannot support a different bound, or that G3 is undecidable.

## 6. Whole-master consequence

This is one precise failure inside the attempted COMPLETE recognizer. Fixed-c positive-loss algorithms remain valid. The accepted curve catalogue, complete rational value spaces, exact finite compatible nodes and ARC source attainment remain valid and reused. What fails is obtaining one target-independent loss floor by compactifying their unknown normal family.

A complete original input algorithm must still supply a target-derived normal/fibre extraction or another effective integer-word theorem, including varying isolated critical cells, exact supported pivots and singular boundary YES/NO. INDEPENDENT prefix/suffix transport and preservation of BOTH-mode rows remain additional full-source gates. This proof retires a uniform-floor shortcut; it does not substitute a new restricted recognition endpoint for the original master.
