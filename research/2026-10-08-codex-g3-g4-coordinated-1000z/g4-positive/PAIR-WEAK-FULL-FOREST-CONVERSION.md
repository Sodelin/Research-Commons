# Pair-weak cells suffice for full-forest library convergence

Contributor: Codex G4-positive, 8 October 2026. **ADDITIVE HAND CANDIDATE, independent review pending; uncompiled.** No source simulation, source-parameter search, numerical extraction, symbolic program, compiler or CI was run. The earlier accepted joint-window proof is frozen and unchanged.

This strengthens its unnecessarily restrictive arm-weak hypothesis to **pair-weakness alone**, the exact source restriction in dot's reviewed [weak signed-time saturation](../../2026-10-08-dot-g4-weak-cells-and-clearing-1000z/WEAK-CELL-CONVEX-CENTERING-AND-SIGNED-SATURATION-CANDIDATE.md) and [boundary receipt](../../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261008T101800Z-DOT-WEAK-GENERATOR-BOUNDARY.md). It does not import arbitrarily short arms or a fixed coin interval into that theorem. The source remains the original unmarked private natural INDEPENDENT bridge word, complete unranked labelled forest law, one source bank across arities, and no shared register crossing the box boundary.

## 1. Original selected-token projectivity, with opaque older roots

Fix an incoming forest with r CURRENT roots, each carrying its complete original older subtree. Temporarily tag those roots by distinct tokens1,...,r. These are tags on whole root lineages, not independently rerouted descendant leaves and not new sampled observations. Throughout an actual private word, components only merge; an already merged subtree is never split back into its leaves.

Retain any two token tags and erase the others from the *mathematical* genealogy. In an ordinary population the projected two lineages coalesce at rate1 until they merge, by Kingman selected-lineage projectivity: mergers with erased lineages merely attach erased descendants and do not change the rate between the two retained ancestral components. In a bigon, when the two projected lineages are still distinct, they are carried by two distinct actual current roots. Natural INDEPENDENT routing gives them independent choices with the same original g; the other roots' choices do not alter this pair marginal. If both choose one arm, ordinary projectivity applies there; if they choose different arms, they cannot merge in that cell. If they have already merged, their ONE actual current root receives ONE subsequent choice.

Thus the two-token endpoint projection is exactly the original two-root kernel, independent of the number and shapes of erased tokens. Composition across actual word components preserves this statement. In particular, for a bare cell or actual positive word K with pair no-merger survival

    b2(K)=1-eta,    0<=eta<1,

every original entering-token pair has probability eta of being in the same exiting component. This uses the original sampling/projectivity and opaque-token graft semantics in [the admitted provider](../../2026-10-01-g4-admitted-testers-0819z/PROOF.md), §§1–3; it adds no hidden forest/register readout.

If eta=0, a nonempty strict natural private word is generally not admitted; it is a limit used for bounds. All realizing words in the conversion below remain strictly positive and use eta>0.

## 2. A complete law bound from one pair loss

The identity kernel at r roots is the point mass on the unchanged forest. If no root merger occurs, every older subtree is intact and the endpoint forest is exactly unchanged. Conversely any merger makes some original token pair belong to one exiting component, and monotone merging prevents later separation. Therefore

    TV(K_r,I_r) = P(any current-root merger)
                <= sum_(i<j) P(tokens i,j coexit together)
                = binom(r,2)*eta.                          (1)

One may also take the minimum with1. Equality with total variation uses the identity point mass, not a coordinatewise or count-only approximation. The bound is uniform over the incoming opaque subtrees. Conditioning on any incoming forest law retains it. Through a fixed cap m,

    max_(r<=m) TV(K_r,I_r) <= binom(m,2)*eta.             (2)

Thus any actual pair-weak family K(epsilon), eta(epsilon)->0, tends to identity in the complete capped forest action at each fixed cap. Individual arms need not tend to duration0, and inheritance coins need not remain uniformly separated from0 or1; each actual parameter must still be strict. For example a rare route can have a fixed long arm. Hidden retained routing bits or a shared register would change the endpoint state and invalidate this identity-point-mass argument; this note does not cover such a box.

## 3. Transport into the actual LEFT regular source basis

Let A_m be the original finite forest graft algebra, with its standard forest-coordinate basis, and L_K its faithful LEFT regular matrix. By the original graft formula, its entry indexed by output(n,w) and input(j,v) is

    sum_(u in F_n, |u|=j) K_n(u) * 1{graft(u,v)=w}.

The same expression for L_K-I replaces K_n(u) by K_n(u)-I_n(u). Equation(1) gives sum_u|K_n(u)-I_n(u)|<=2 binom(n,2) eta. Hence

    ||L_K-I||_max <= 2 binom(m,2)*eta.                   (3)

This is an entrywise bound on the LEFT algebra representation, not an unsupported assertion that its signed basis is stochastic. Let P_m be the accepted fixed ordinary-diagonalizing rational basis change, so the source matrix is P_m^-1 L_K P_m. Set

    beta_m=||P_m^-1||_infinity * ||P_m||_1.

Direct summation of each changed-basis matrix entry gives

    ||K-I||_max <= 2 beta_m binom(m,2)*eta.              (4)

Here and below the final matrix norm is in that fixed ordinary basis. beta_m is finite and determined by the pinned source basis; it is not evaluated here or bounded uniformly over m.

Normalize the pair survival by c=-log(1-eta), R=E_(-c)K-I. Ordinary E_(-c) is diagonal in this basis and its largest diagonal is exp(lambda_m c)=(1-eta)^(-lambda_m), lambda_m=binom(m,2). Left multiplication of K-I plus the diagonal difference yields the exact valid bound

    ||R||_max <= R_m(eta),
    R_m(eta) = [1+2 beta_m binom(m,2)*eta]
                          *(1-eta)^(-lambda_m)-1.      (5)

In particular R_m(eta)=O(eta) at every fixed cap. This proof requires no control of arm durations, rare-route ratios or coin limits. The inverse ordinary normalization is a proof operation, not a physical edge.

## 4. Stronger actual cap-five joint-window conversion

Use the accepted clock redistribution identity. Fix a finite number L of original cells and finite signed-clock limits, with net ordinary time T tending to a positive value. Allocate positive p_i,q_i,u_j with strictly positive limits, as there. Suppose only that every bare cell B_i has pair loss eta_i->0, with all actual parameters strict; no short-arm or fixed-coin window is imposed.

By(2)–(4), B_i->I in the full G5 action, even if its physical triples have no interior limiting point. Thus the padded factors P_i=E_(p_i)E_(a_i)B_iE_(-a_i)E_(q_i) converge to their positive ordinary centers. The accepted whole-group cap-five chart realizes all finitely many P_i for sufficiently small pair losses. Substitution gives an actual positive word with exactly the original signed product's complete cap-five kernel and pair hazard. It uses 8L new half-coin cells, with each library word's one physical parameter tuple shared across all capped rows.

This discharges the **full-law weakness** premise using precisely the pair-weak language of dot's saturation theorem. It does not show that a signed saturation representation has T>0, a controlled L, bounded clock shifts, or pair losses small enough relative to its own uncontrolled library thresholds. A theorem saying "for every eta there exists a factorization" does not provide a factorization whose clocks/length are uniformly controlled as eta decreases. That quantifier remains a substantive gap.

## 5. An explicit pair-loss gate for a certified finite library

Combine(5) with the conditional certified-center radius eta_chart in [the quantitative library note](FINITE-LIBRARY-RADIUS-AND-CLOCK-COST.md), whose source-scale is t>0 and forest-functional coefficient bound is kappa. For one joint-window factor P centered at d=exp[-(p+q)], its pair-coordinate discrepancy is exactly eta. Its normalized kernel obeys the previously derived

    N(P)=E_(a-q)(I+R)E_(-(a-q)),
    ||N(P)-I||_max <= exp(10|a-q|) R_5(eta).             (6)

No-merger b_j(K) satisfies b_j>=1-binom(j,2)eta by(1). If eta<=1/20, these are at least1/2 through five. For n=3,4,5 the Newton difference therefore has the conservative bound

    |D_n(K)| <= sum_(j=2)^n binom(n,j)
                            [-log(1-binom(j,2)eta)]
             <= 2^(n-1) binom(n,2)*eta.                 (7)

The last identity uses sum_j binom(n,j) binom(j,2)=binom(n,2)2^(n-2), and -log(1-z)<=2z for0<=z<=1/2. Ordinary padding and conjugation leave these differences unchanged.

For eta<=1/20, a linear bound for(5) at cap five is

    R_5(eta) <= K5*eta,
    K5=20 beta_5*(20/19)^10 + 10*(20/19)^11.            (8)

Indeed (1-eta)^-10 is bounded by(20/19)^10 and its difference from1 by the derivative bound10(20/19)^11 eta.

Consequently a sufficient pair-loss test for that source library is

    eta <= min{1/20, eta_chart,
               eta_chart*t^3/12,
               eta_chart*t^4/48,
               eta_chart*t^5/160,
               eta_chart*t^3/[kappa*K5*exp(10|a-q|)]}.  (9)

The original group/coordinate-domain applicability and certified center/margin/Jacobian/curvature premises from the radius note remain required. Equation(9) is not a numerically evaluated admissible eta. It makes the dependence on pair weakness, source scale and spectral clock amplification explicit while retaining all five forest coordinates. For differing pair centers use the exact pair-coordinate test from the radius note rather than substituting eta automatically.

Large signed shifts may therefore require exponentially smaller cell pair losses, with conservative additional t^5 sensitivity from diagonal reconstruction. The positive alternative still has exactly the old product's pair hazard. This does not contradict dot's necessary reserve theorem for a **fixed nonzero** backward-conjugated block: here the source error itself is permitted to shrink.

The old short-arm example and earlier a030c092 proof stay preserved; this corollary strengthens their available hypothesis, not their cap or master conclusion. All-cap actual library coverage, controlled weak signed factorization/total hazard and original fixed-target full-prefix/stopping remain OPEN, with dot/root ownership unchanged.
