# Differential normal form and local exclusion at every finite equal-arm target

Contributor: Codex, delegated general-algebra lane, 13 October 2026. **Hand-proof candidate for independent challenge.** This extends an inherited local mechanism; it is not a general G4 closure, an independently accepted theorem, or a Lean proof. No new all-core observer is assumed.

## 1. Claimed advance and exact remaining master gap

The candidate below gives local arbitrary-count weak-insertion exclusion around **every finite strict equal-arm private BOTH target**, including mixed fair/biased coins and repeated cell parameters. It does not require a supplied upper bound on the number of inserted cells. Its new hinge is a differential version of the inherited ordered cohort normal form. If accepted, this discharges the finite-body local step across the whole equal-arm private class. It does **not** prove that arbitrary fitting rivals enter such a neighborhood; countably persistent limits and the legal original-core observer transfer remain open.

The inherited one-biased-cell and all-fair local theorems are retained with their existing attribution. The new claim is a common first-order mechanism covering a mixed finite body. The full source generator identity, cohort extraction, Kingman entrance/Dirichlet description, and source polynomial compiler are reused.

Fix

    T = E_(a_0) B(t_1,p_1) E_(a_1) ... B(t_L,p_L) E_(a_L),

where all durations a_j,t_i are positive, B(t,p)=B(t,t,g), p=g(1-g) in (0,1/4], and E_a is the pair-rate-one ordinary passage of duration a. Each p represents the arm-exchange orbit. The physical source and tuple are shared across all rows; the natural COMMON duration is H=sum a_j+sum t_i. Work at the inherited private full-forest interface and its proved legal completions. A calibrated original-taxon adapter may be composed only under its own exact premises.

## 2. Differential normal-form lemma

Let K(theta) be the projective full INDEPENDENT forest kernel of the fixed L-cell body. Derivatives in p are valid at fairness because equal-arm full forest entries are symmetric polynomials in g and hence polynomials in p. Suppose a real tangent v satisfies

    D K_m(theta_T)[v] = 0 for every finite cap m.

The proposed exact kernel is:

- at every biased cell i, v_(a_(i-1))=v_(t_i)=v_(p_i)=0;
- at every fair cell i, for some real r_i,

      v_(a_(i-1))=4 r_i,  v_(t_i)=-8 r_i,  v_(p_i)=r_i;

- v_(a_L)=0.

Consequently

    D H[v] = -4 sum_(i fair) r_i.                    (DN)

On the physical tangent cone r_i<=0 at every fair target coin, every all-law null tangent has D H[v]>=0. If also D H[v]=0, it is zero.

### 2.1 The fair null directions are exact full-forest identities

The accepted all-cap generator identity is

    Q * B = (1/g) B_tx + (1/(1-g)) B_ty
                            + g(1-g)/2 B_gg.

At equal arms and g=1/2, arm symmetry gives B_tx=B_ty and B_t=B_tx+B_ty. Since p=1/4-(g-1/2)^2, B_gg=-2 B_p at fairness. Therefore

    Q * B = 2 B_t - B_p/4.                          (WF)

This is an identity of complete labelled forest operators, including chronological shape entries. It is not inferred from the diagonal fair identity. Inserting (WF) at any cell proves that the displayed r_i direction lies in the all-cap kernel.

### 2.2 First-cell necessity from the two-root mass atoms

Cancel the positive leading E_(a_0) in each finite capped operator. This is algebraic cancellation, not a negative physical population. Writing U for the tail beginning with E_(a_1), the resulting derivative identity is

    v_a Q*B*U + v_t B_t*U + v_p B_p*U + B*D U = 0.   (A)

At a biased cell choose g>1/2 locally, so v_p B_p=v_g B_g with v_g=v_p/(1-2g). Use the full source identity to replace Q*B by first arm-time derivatives and (p/2)B_gg.

For a B-first source with positive arm durations, consider the finite measure on (0,1) that puts one unit at the frequency of each output root on the event that there are exactly two output roots. The inherited cohort theorem says its only atoms are g and 1-g, with positive weights. More explicitly, conditional on the positive finite arm root counts and the later mass-blind merger history, each output root mass is

    X = g A + (1-g) C,

where A and C are independent sums of coordinates of conditional Dirichlet arm frequency vectors. Each sum is a Beta variable, or the constant 0 or 1. The atom at g comes from (A,C)=(1,0); its positive coefficient is independent of the first coin g. The symmetric atom comes from (0,1). Every other term is atomless. Later cell parameters alter mixture weights/history probabilities, not these first-cohort mass locations.

Differentiating in first g therefore represents the k-th derivative, for k<=2, as D_x^k of a finite signed pushforward measure, plus lower-order such derivatives if weights also vary. Its highest-order atomic coefficient at g for k=2 is positive. Arm-time and tail derivatives have order zero; B_g has order one.

Localize at g with a smooth test f_epsilon(x)=epsilon^2 f((x-g)/epsilon), supported away from 1-g. Its second derivative is uniformly bounded, while its first and zeroth derivatives have norms O(epsilon), O(epsilon^2). The D^2 delta_g term has a nonzero fixed limit for a choice f''(0)!=0. The D^2 of every atomless finite measure tends to zero, since its mass in a shrinking neighborhood tends to zero. All lower distributional orders tend to zero. Applying this to (A) gives v_a=0. Now use epsilon f((x-g)/epsilon) to isolate the first derivative atom and conclude v_g=0, hence v_p=0.

At fairness replace B_p by 8B_t-4Q*B using (WF). Equation (A) becomes

    (v_a-4v_p) Q*B*U + (v_t+8v_p) B_t*U + B*D U=0.

The symmetric two-root measure has one positive atom at 1/2. The Q*B term contains a nonzero second derivative atom by the same generator identity. Neither remaining term does. The same shrinking test gives v_a-4v_p=0. This removes the coin variation entirely, leaving only a modified time variation v_t+8v_p and the tail derivative.

### 2.3 Justifying passage from finite rows to the mass distribution derivatives

This is a proof obligation explicitly exposed for review. It is intended to avoid an unlicensed interchange of an infinite-sample limit and differentiation.

For n sampled labels, use the bounded finite-forest statistic that is zero unless exactly two output roots remain and otherwise sums f(k/n) over their two leaf counts. Conditional on the full positive root mass vector M=(M_1,...,M_N), its expectation is

    sum_(i<j) sum_(k=1)^(n-1) binom(n,k) M_i^k M_j^(n-k)
                                  [f(k/n)+f(1-k/n)].     (B)

This depends only on finite legal forest rows. For first-coin g in a compact subinterval of (0,1), every M_i=g A_i+(1-g) C_i and |dM_i/dg|<=C M_i. For a pair i,j put s=M_i+M_j. Because sum_i dM_i/dg=0, also |ds/dg|<=C(1-s). If N>2, s<1, and the contribution and its first two g derivatives tend to zero. Terms from derivatives of s^n are bounded by constants times [n(1-s)]^r s^(n-r), r<=2, which are bounded uniformly in n,s and tend to zero for fixed s<1. Conditional Bernstein-polynomial derivatives in the relative frequency M_i/s are uniformly bounded by finitely many derivatives of a smooth f. If N=2, s=1 identically and the usual C^2 convergence of the Bernstein polynomials gives the derivatives of f(M_1)+f(M_2). Endpoint corrections also converge with their first two derivatives for positive M_i.

There are at most N^2 pair terms. Positive arm times in a fixed neighborhood give uniformly finite moments of every order of N. Explicitly, for the Kingman entrance count and T_M=sum_(k>M) Exp(k(k-1)/2), exponential Markov with theta=M/4 gives Pr(N_t>M)<=exp(1-Mt/4): use sum_(k>M) 1/binom(k,2)=2/M and -log(1-u)<=2u for u<=1/2. This is uniform for t bounded below by a positive constant. Thus dominated convergence yields the required C^2 convergence in the first coin. Mixed terms of lower derivative order are covered by the same bound.

For arm-time and tail parameters, condition at an earlier fixed positive arm time. Their subsequent genealogical evolution has total jump rate bounded by a polynomial in the finite root count. This count has moments of every order. The ordinary Markov generator therefore differentiates its probability law as a finite signed measure in total variation; the first two derivatives needed after converting a fair tail p to g are bounded by higher count moments. Current-root routing derivatives are finite polynomials whose total variations are bounded by powers of the finite root count. Composition preserves these bounds. The same dominated argument handles the derivatives of (B) with respect to those mixture/history parameters.

Accordingly the zero finite-row derivative identity (A) passes to the stated distributional mass identity. No mass atom is claimed to be a finite legal observable; it is a law-level tool for proving differential necessity.

### 2.4 Peeling after the first coin variation disappears

After the preceding step, the remaining identity has the first coin fixed. Positive arm-time and tail variations then define a finite signed derivative of the full countable hierarchy law in total variation, by the finite-root generator bounds just described. Its finite cylinder values are exactly the finite forest derivatives. If those all vanish, cylinder uniqueness for finite signed measures makes the entire signed hierarchy derivative zero. The inherited cohort extractor at the **fixed** g is one measurable map valid throughout this fixed-g parameter neighborhood. For g=1/2 use its independent fair orientation bit. Differentiation commutes with this fixed pushforward.

The differentiated extracted joint no-merger coordinates satisfy

    d_11 = s_2(U),   d_20 = exp(-t) s_2(U).

Both their derivatives vanish. Since s_2(U)>0, this forces the remaining first-arm time variation to be zero. The extracted complete first-cohort law is E_t*U. Its derivative, with t fixed to first order, is E_t*D U=0, and positive triangular cancellation gives D U=0 at every cap. Repeat down the finite chain. The final ordinary parameter is fixed by its pair diagonal. This proves the proposed necessity and (DN).

## 3. A finite one-sided Lipschitz inverse for the fixed body

Augment the full body response by H. On the unit physical tangent cone (p-variations at fair cells nonpositive), (DN) says the derivative never vanishes. Compactness of this finite-dimensional unit cone and a finite-subcover argument select finitely many complete response coordinates, hence some cap m_0, and c>0 such that

    ||D K_(m_0)[v]|| + |D H[v]| >= c ||v||

on that cone. Smoothness of the fixed finite body map gives, throughout a sufficiently small physical neighborhood,

    ||theta-theta_T|| <= C( ||K_(m_0)(theta)-K_(m_0)(T)||
                                           + |H(theta)-H(T)| ).  (LIP)

Thus the argument needs no unproved immersion in the unrestricted signed p tangent space. The exact fair singularities are included and their physical one-sided sign is essential.

## 4. Local arbitrary-count weak-insertion exclusion

Select L cells of a rival in their original order. Replace every unselected cell by an ordinary passage of its **same physical duration** and combine the gaps. Denote the resulting selected-body parameters by theta. Assume theta tends to theta_T and the actual rival has the same natural COMMON H and matches increasingly many full INDEPENDENT caps.

For every unselected cell let t>0, p>0, and

    w=p(exp(t)-1),   S=sum_extra w.

The exact pair diagonal gives S->0, because its log contribution is log(1+2w), while w is bounded above by (exp(H)-1)/4. If S=0 there are no strict extras. Suppose S>0 along the sequence.

At any fixed cap, source analyticity on the closed compact (t,p) rectangle gives ||B(t,p)-E_t||<=C_m w. Stochastic telescoping gives ||K_m(theta)-K_m(T)||<=C_m S under exact rival matching. Since H(theta)=H(T), (LIP) implies ||theta-theta_T||<=C S. Pass to a subsequence with

    (theta-theta_T)/S -> alpha,

where alpha is in the physical tangent cone and D H[alpha]=0.

Each extra occupies an interval [r,r+t] in one of the selected body's collapsed ordinary gaps. Use the probability measure assigning mass w/S to its gap index, position r and duration t. These locations lie in a fixed compact set; after transporting the convergent gap lengths to a fixed domain, take a weak limit mu.

The normalized first-order insertion direction at positive t is

    V(t) = partial_p B(t,0)/(exp(t)-1),

inserted in place of E_t in that same gap. At t=0 the continuous extension is -2Q. Indeed B(t,p)=I+(1-2p)tQ+O_m(t^2), whereas E_t=I+tQ+O_m(t^2). The quotient (B-E_t)/w has this same t=0 limit uniformly over p in [0,1/4]. As max w<=S->0, its difference from V(t) tends uniformly to zero: any compactness countersequence has either p->0 or t->0. Product expansion and stochastic telescoping bound cross terms by O_m(S^2). Thus exact full-cap equality yields, at every fixed cap,

    D K_T[alpha] + integral V_(gap,r,t) dmu = 0.     (W)

No actual inverse or negative-time factor is used; these are first variations of strict physical words.

The normalized diagonal projection of (W) is

    sum_i D phi_n(t_i,p_i)[alpha] + integral D_n(exp(t)) dmu=0,
    D_n(y)=n(1+y+...+y^(n-2)).                       (D)

Every target first derivative has O(n^2) growth; this also holds at fairness by the exact fair identity. If mu gives positive mass to t>0, some t>=epsilon has positive mass and its D_n contribution grows exponentially, contradicting (D). Therefore mu is supported on t=0.

Inside an ordinary gap Q commutes with its ordinary factors. Consequently (W) reduces to

    D K_T[v]=0,
    v=alpha-2 sum_j mu(gap=j) e_(a_j).

Its fair p-components retain the physical nonpositive signs, but

    D H[v]=0-2=-2.

This contradicts (DN). Hence no such increasingly accurate local rival sequence exists.

Equivalently there are a finite cap N and a target neighborhood such that any actual finite strict rival on the same COMMON clock, having L selected cells with collapsed same-duration body in that neighborhood and matching T through N, has no unselected cells. The inherited bounded-shape finder, or (LIP) on the exact fibre, then fixes the selected body to T. This is an existential local finite certificate uniform in the number of extras.

## 5. What is inherited, new, and still unproved

Inherited: exact compiler; full WF identity; strict source positivity; Kingman Dirichlet/entrance description; measurable cohort extraction and ordered finite-chain normal form; fixed-shape finite-prefix principle; compact weak-cell direction method and one-biased/all-fair local providers.

Proposed addition: the all-copy derivative-kernel classification (DN), its physical cone clock sign, and the resulting mixed-target local theorem via the weak-direction limit. The shrinking-test proof and the C^2 Bernstein convergence are submitted for independent scrutiny. No historical novelty assertion is made.

Not discharged: global neighborhood entry for arbitrary fitting rivals, exclusion of infinitely persistent mixed arrays, legal extraction across arbitrary original retained cores, INDEPENDENT-only forcing, effective all-rival stopping, or a fixed-target exact negative construction. No infinite carrier is treated as an admitted rival.

Primary applicability search also rechecked that nilpotent signatures, equivariant algebraic closure, and positive splitting do not give the missing global implication; the exact earlier audits are reused rather than re-presented as new no-go results.

## Providers

- Full source generator: `../../2026-10-04-dot-g3-recovered-local-components-1812z/critical/source-generator/INDEPENDENT-BIGON-GENERATOR-IDENTITY.md`.
- Ordered cohort normal form: `../../2026-10-01-sol61-g4-allcopy-2237z/PASSIVE-CHAIN-NORMAL-FORM.md` and its accepted review.
- One-cell local separator: `../../2026-10-09-dot-local-forcing-and-coverage-review-1627z/g4-local/LOCAL-WEAK-INSERTION-EXCLUSION.md`.
- All-fair local theorem: `../../2026-10-10-dot-g4-all-fair-local-forcing-1220z/ALL-FAIR-HIGHER-JET-LOCAL-EXCLUSION.md`.
- Original source/observer: `../../2026-10-01-g4-admitted-testers-0819z/PROOF.md`.

Primary background directly checked in this pass: Bertoin and Le Gall, *Stochastic flows associated to coalescent processes*, [author PDF](https://www.imo.universite-paris-saclay.fr/~jean-francois.le-gall/Flow1.pdf), Example 1, pp. 11–12 in the PDF, gives the Kingman pure-death block count and conditional uniform-Dirichlet block frequencies. This is the reused probabilistic input, not a finite-forcing or differentiability theorem. Its full proof was not newly audited.

An exact cap-four polynomial transcription check is recorded separately. It cannot establish the hierarchy differentiation, derivative-kernel classification, or arbitrary-count compactness argument. No Lean verification is claimed.
