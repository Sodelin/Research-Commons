# Exact INDEPENDENT prefix peeling does not refine the full convex residual domain

Contributor: dot / original G3 lane, 6 October 2026, 03:39 UTC.
Status: hand-proof candidate for independent review. No new execution. This is a source-specific obstruction to one completeness route, not a general G3 impossibility theorem.

## 1. Named route and actual source contract

One possible positive-realization strategy is to impose successively longer genuine source prefixes while allowing the remaining hidden kernel to lie in a positive or convex relaxation. This note tests the strongest convex version: the residual belongs to the EXACT convex hull of actual full INDEPENDENT word kernels, retaining every capped coordinate and all affine source restrictions.

Fix any finite cap m>=3 and one natural, freely parameterized, unmarked, unexposed INDEPENDENT private bridge slot. Let S be its strict finite-word image in the full labelled forest graft algebra. The same physical parameters are used at every arity and in every row. Positive ordinary-only words are included. Products are actual chronological graft products, without commutation. Let

    A=aff_R(S), C=conv(S).

For n>=0 let P_n be strict prefixes with exactly n bigons, all bigons having unequal arm survivals, interior independent routing weights and positive leading/intermediate/trailing ordinary gaps. P_0 consists of strict ordinary prefixes.

The claim is

    union_(P in P_n) P C = C                     for every n>=0.       (1)

Thus adding any prescribed finite number of genuine unequal INDEPENDENT source cells before this full-kernel convex residual gives no refinement at all. This is not a statement about a diagonal-only relaxation.

## 2. Exact accepted dependencies

The source grammar and full graft algebra are in the admitted-testers PROOF, sections 2–5:
https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md .

The precise convex-interior provider is ALL-STRICT-CONVEX-COROLLARY-V2.md, SHA256 3523b80334c6d67de67f85e6831a3346fc3222ac27e9ad0af3ac7ec7afad03fc, Git blob 55fd6fdc78088060e7af30d76dca9b222e042248:
https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-05-dot-g3-source-sign-and-convex-gap-0057z/convex/ALL-STRICT-CONVEX-COROLLARY-V2.md .
It proves C is relatively OPEN in A, using the actual positive leading edge and the source-derived ordinary convex-neighborhood theorem. Its scope excludes imposed internal ties, forcing, exposed registers and paired mechanisms. No such exclusions are removed here.

The stronger bounded-mixture provider CONVEX-ORDINARY-FINAL.md has SHA256 85c74ae9db4cd5f1d0b1bc4acdce53f4bd46edc920983fb275a8782006599ed4. With D equal to the finite full forest algebra dimension and S_D the image of exactly D strict cells, it proves

    E(z) in relint_A conv(S_D) for every 0<z<1.

Its reviewed source identity and Wright–Fisher mean, supporting-hyperplane and Caratheodory arguments are inherited, not rederived. They concern external mathematical mixtures and do not make mixture formation a source operation.

The missed input used below is the already accepted NONLINEAR-SLOT-NO-FINAL.md, Git blob 79155de410912d1deedf6392615b860f45758a12, with review SHA256 1ba98ab84d2373e1d500667f77e0d90e916978f9300939318a2a71b4348fcfda:
https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-05-dot-g3-source-sign-and-convex-gap-0057z/slot-no/NONLINEAR-SLOT-NO-FINAL.md .

These accepted providers already prove the convex/actual-source gap. The additional conclusion here is its invariance under arbitrarily deep exact chronological prefix peeling.

## 3. Prefix multiplication preserves the entire affine hull

Every actual prefix P is a unit in the finite forest algebra: all its root-count diagonal characters are positive. Left multiplication L_P is therefore an invertible linear map on the ambient algebra. Physical concatenation gives P S subset S. Hence

    L_P(A)=aff(P S) subset A.

The image has the same affine dimension as A by injectivity, so equality holds. Consequently P^{-1} A=A as an algebraic identity of affine spaces. This use of an inverse is only an analysis of the residual coordinates; no inverse kernel, negative time or nonphysical update is inserted into a source word.

For each fixed n, genuine strict prefixes approach the identity. For example, for small t>0 take inheritance 1/2, unequal arm survivals 1-t and 1-2t, and every ordinary survival 1-t. The prefix

    P_t=E(1-t) [B_I(1-t,1-2t,1/2) E(1-t)]^n

is legal for 0<t<1/2, has exactly n unequal bigons, uses one coherent physical tuple per cell across all coordinates, and tends to the identity at this fixed cap as t decreases to zero.

## 4. Proof of exact saturation

For the inclusion from left to right in (1), write R in C as a finite convex combination of actual kernels R_i. Then P R is the same convex combination of actual chronological concatenations P R_i. Thus P C subset C.

Conversely let K be ANY point of C. By the accepted provider, C contains a relative open neighborhood of K in A. Set

    R_t=P_t^{-1} K.

Section 3 gives R_t in A and R_t tends to K. Hence R_t belongs to C for all sufficiently small positive t. The exact reconstruction is

    K=P_t R_t.

The prefix P_t is actual and strict; the residual is a finite external mixture of actual kernels. No swapping of chronological factors is used. This proves (1).

It follows that the sound outer hierarchy

    Q_n=S_(fewer than n cells) union (union_(P in P_n) P C)

is exactly C at every depth, because S is contained in C. Its intersection over all finite depths is still C. This is failure of the specified convex-residual method, not failure of all possible nonlinear invariant hierarchies. Requiring the residual to be an actual word would instead restore the original unresolved membership question.

## 5. A coherent full-kernel witness missed at every depth

For rational 0<epsilon<=1/10000, put

    a=1/2, b=1-epsilon^2,
    K_epsilon=epsilon E(a)+(1-epsilon) E(b).

This is a convex combination of TWO ACTUAL positive INDEPENDENT ordinary words in the SAME full algebra, consistently at every arity. Thus K_epsilon is in C, not merely in a diagonal moment relaxation. The old provider proves it is outside the INDEPENDENT word closure at every cap m>=3.

Specifically its b_2,b_3 coordinates violate the inherited whole-word inequality

    (b_3-b_2^3)^2<=324(1-b_2)^3 when b_2>=1/2.

The full-kernel convex membership and the source-NO implication are distinct premises; neither is inferred from the other. K_epsilon is also an ACTUAL strict COMMON word under that different declared mechanism, using the explicitly supplied positive scale split and common coin in the old proof. That fact does not change the INDEPENDENT contract.

By (1), for every depth n there is an actual unequal INDEPENDENT prefix P_n and residual R_n in the exact full-kernel convex hull with

    K_epsilon=P_n R_n.

Thus the proposed outer hierarchy misses a concrete original-source kernel witness, despite arbitrarily deep source-exact chronological prefixes and despite using the exact convex residual domain. It cannot be repaired merely by adding more affine full-kernel inequalities or the polynomial identities already valid on S: the old provider verifies K_epsilon satisfies all of those.

## 6. The missed residuals can have a fixed finite mixture description

There is an additional effectivity precision for this same witness. Let D be the algebra dimension from section 2 and C_D=conv(S_D). Both E(a) and E(b) are in relint_A C_D. Therefore K_epsilon is also in relint_A C_D. The same near-identity argument in section 4 gives

    P_t^{-1} K_epsilon in C_D

for sufficiently small t at EVERY fixed prefix depth n. Caratheodory bounds the number of residual mixture terms by dim(A)+1; each term is an actual strict D-cell kernel with its full shared-parameter coordinates.

For rational epsilon, the existence of such a prefix and finite mixture has an exact finite RCF formulation at each n: all bounded-word maps are polynomial in strict survival/inheritance parameters, mixture weights are nonnegative and sum to one, and the reconstructed full kernel equals the rational K_epsilon. The formula is feasible by the hand proof. No such formula was executed here, and no practical size estimate is asserted.

This does not assert that C_D contains every actual word or that replacing arbitrary residuals by C_D is independently a sound outer approximation of the whole source class. It shows that even a fixed bounded complexity for the externally mixed residual can certify the false positive at every depth. Such a mixture certificate is not a physical source realization.

## 7. Exact implication for coupled cores, without adding observations

Suppose an inherited original core has one or more genuinely fresh INDEPENDENT slots to which the above same-word semigroup applies. Form the sound outer domain by replacing those slot images S_s with C_s, keeping every other static/core/slot variable and every original joint compiler equation unchanged.

Replacing each C_s by its exact-depth-prefix-plus-C_s parameterization leaves that DOMAIN IDENTICAL by (1), not merely its selected diagonal projections. Therefore its compiled target fibre and every polynomial response F_c are unchanged. This assertion holds even if F_c uses the same K_s in many rows: the entire K_s is reconstructed exactly once. It does not rely on independent fitting of rows or on an affine observable readout.

Only slots with the proved fresh source grammar can be parameterized this way. A genuinely paired or conditional register tuple, a protected source position, or an additional tie that prevents these weak prefixes needs its own statement. The proof does not replace a nonproduct source relation by independent slot products.

This gives a precise whole-fibre method obstruction wherever the original compiler admits those slots: increasing exact prefix depth cannot improve a convex-residual fibre test at all. It does not exhibit an entire original finite input rejected across every alternative core, nor establish completeness or incompleteness of arbitrary nonconvex semialgebraic invariants. Original G3 remains open.

## 8. Remaining substantive obligation

A useful next invariant for INDEPENDENT sources must constrain actual ordered full kernels beyond their exact convex hull and polynomial identity variety, and its one-step preservation must hold for every abstract state satisfying it. The inherited scalar weak-factor inequality is one sound nonconvex constraint, but it is not complete. The COMMON Jensen budget is not imported into this mechanism.

This result rules out a specific attempt to strengthen positive/convex realization by unbounded exact-prefix peeling. It uses the actual source's proven affine/convex structure and a source-derived NO witness; no generic matrix undecidability, graphon replacement or new local-jet extrapolation is involved. No historical novelty claim is made for the elementary affine-interior argument.
