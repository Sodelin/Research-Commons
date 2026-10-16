# Exact critical-level exclusion with supplied algebraic residue nodes

## Prior-supplier correction: 16 October 2026, 07:44 UTC

The effective fixed-normal floor and count used here are OLD accepted results: [UNIT-CRITICAL-PUISEUX, Section 4](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-10-dot-g3-unit-critical-puiseux-1029z/UNIT-CRITICAL-PUISEUX.md), [independent review](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-10-dot-g3-unit-critical-puiseux-1029z/INDEPENDENT-OBSTRUCTION-REVIEW.md), 10 October 2026. They hold for every supplied effectively algebraic nonzero normal. The accompanying SATURATED-NORMAL-RETAINED-COUNT note is an elementary special-case rederivation, not a new floor theorem.

The finite critical-component level construction and algebraic-log tests below should be read as a scoped composition of this prior with classical semialgebraic path constancy and Baker arithmetic. No new floor/count result is claimed. The earlier [input-only algebraic-residue critical census](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-critical-arithmetic-census-1148z/INPUT-ONLY-ALGEBRAIC-CRITICAL-CENSUS.md) already gives a stronger input-only census on its one-residue cap-seven predicate; it does not have the same arbitrary supplied multi-node contract. Novelty of this corollary remains unresolved and it should not be counted as an independently novel theorem. The exact output remains only INTERIOR_UNDER_PROMISE outside the listed levels; on-level and raw-input promise acquisition remain unresolved.

Contributor: dot, 16 October 2026. Status: candidate hand corollary, unexecuted. It reuses classical algebraic-number logarithm algorithms. This is a promised-normal-form interior-YES test, not a full source recognizer.

## Contract

Supply s>=1 distinct effectively real-algebraic residue nodes Q in (0,1), M=2s+5, and positive effectively real-algebraic observations m_lambda in (0,1) for the M-1 positive Kingman exponents. The mathematical promise, when a YES conclusion is used, is that h=-log m has a COMMON closure normal form with exactly these positive residue nodes, positive ordinary drift, no killing, and any finite or summable retained strict-factor list. The residue weights, drift and retained list need not be supplied. The promise is not silently inferred from the observation tuple.

There is an effective finite test with outputs EXCEPTIONAL_LEVEL and INTERIOR_UNDER_PROMISE. The second output proves actual finite strict-source interior if the normal-form promise holds. The first output leaves attainment undecided. No numeric certificate extraction or execution is claimed.

## 1. Finite critical values without rational normal coefficients

Construct the unique saturated algebraic normal c and the rational critical equations as in [the hand-reviewed retained-count theorem](https://github.com/Sodelin/Research-Commons/blob/30906289fe03363cd61d234ccff58b23d0628501/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/SATURATED-NORMAL-RETAINED-COUNT.md). Put L=c.H. Compute a finite semialgebraic cell decomposition of its strict critical locus K={L_p=L_q=0,0<p,q<1}, over the real-algebraic coefficient field. Sample an algebraic point theta_j in every nonempty cell.

On each connected cell L is constant: semialgebraic points can be joined by a piecewise differentiable path in the cell, and dL along such a path is zero because both partial derivatives vanish on K. Thus the finite list v_j=L(theta_j) contains every strict critical value. Different cells may yield the same value; duplicates are harmless. This avoids assuming isolated critical points or needing a finite critical point set.

All f_lambda(theta_j)=1-p_j+p_j q_j^lambda are positive algebraic. Hence v_j is an explicitly represented algebraic-linear combination of real logarithms of positive algebraic numbers. It need not be the logarithm of an algebraic number when c is irrational algebraic. No such exponential-algebraicity claim is made.

## 2. Effective finite level list

Extract epsilon(Q)>0 by the terminating critical-loss QE search in the reviewed theorem. Find b>=1 with m_1>2^(-b), and put B=floor(b/epsilon). Enumerate all nonnegative integer vectors n=(n_j) with sum_j n_j<=B, including the zero vector. For each test exactly whether

c.h = sum_j n_j v_j.                         (1)

This is a finite list depending effectively on Q and the algebraic input. Every noninterior profile with the promised normal form satisfies one of these equalities. Indeed, if any retained factor has a derivative not annihilated by the unique c, the accepted enhanced response block has full row rank and the profile is in actual-source interior. Otherwise all retained factors are critical, the loss floor bounds their number by B, and c annihilates the drift and all residues. Grouping their critical values gives (1).

Therefore if every tested equality fails, return INTERIOR_UNDER_PROMISE. If any equality holds, return EXCEPTIONAL_LEVEL. The implication is deliberately one-sided: a level can contain points whose attainment requires further analysis, and no NO inference is authorized.

The same reasoning covers countably summable retained lists: a common positive critical-loss floor makes an all-critical such list finite. No infinite integer vector or limiting equality is required.

## 3. Why each equality is decidable

For a fixed n, subtract the two sides of (1). Up to signs this is a finite linear form

sum_l beta_l log(alpha_l),

where every alpha_l>0 is effectively algebraic and every beta_l is effectively real-algebraic. The alpha list consists of the observed m_lambda and the finitely many f_lambda(theta_j). Choose their positive real logarithms.

Compute the integer lattice of multiplicative relations among the alpha_l using the established algebraic-number algorithm. Every integer relation is exactly a rational relation among these real logarithms. Baker's theorem says the kernel on algebraic coefficient vectors is the algebraic span of those rational relations. Thus (1) holds if and only if its coefficient vector beta belongs to that computed algebraic span, decidable by finite exact algebraic linear algebra.

For clarity, this converse is only for algebraic coefficients. Arbitrary real annihilators are not being classified by Baker. Any real combination of known relation rows is sound by elementary linearity, but the entire real logarithmic kernel is generally larger. Nor is a nonlinear polynomial in logarithms or arbitrary real powers sent to an algebraic decision procedure.

An immutable primary exposition is Sertoz, Ouaknine and Worrell, [Computing transcendence and linear relations of 1-periods, arXiv:2505.20397v1](https://arxiv.org/html/2505.20397v1), Lemma (8.8.61) and its proof. It explicitly gives the algebraic-span statement and effective multiplicative-relation construction using S-units. Only that established linear logarithm arithmetic is reused here.

## 4. Prior boundary and remaining master obligation

The [earlier supplied rational-node critical-level theorem](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/SUPPLIED-RESIDUE-CRITICAL-COUNT-BOUND.md) and [dyadic extension](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-CRITICAL-EXCEPTIONAL-STRATUM.md) used rational normals to exponentiate to algebraic monomial levels. The present arithmetic adapter removes that rational-normal restriction for finite level equality testing. It does not remove it from their polynomial survival-coordinate encoding of complete residual images; irrational powers in that different encoding remain a separate issue.

The [accepted enhanced-rank theorem](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-sol61-g3-boundary-resume-2124z/ENHANCED-RETAINED-RANK-CRITERION.md) supplies the interior conclusion. The retained-count theorem supplies the finite integer cutoff. Classical cell decomposition and Baker/multiplicative-relation arithmetic supply effectiveness. No new transcendence theorem or new generic critical-value theorem is claimed.

The original input does not supply Q or verify the promise. Even with Q supplied, this procedure leaves the finite exceptional levels unresolved and gives no upper bound on a YES witness there. Arbitrary original cores, joint controls, other modes, active killing, zero drift and higher-dimensional normal spaces are outside this corollary. General G3 OPEN; General G4 OPEN. Historical novelty remains unresolved, and no solver or source enumeration was run.

## Scoped hand-review record

On 16 October 2026 the coordinating dot reviewer read the complete corollary and communicated scoped HAND PASS conditional on the reviewed retained-loss floor, enhanced-rank supplier, and explicit supplied-Q/normal-form promise. The review checked finite cell sample values, path constancy, bounded integer multiplicities, the Baker algebraic-span equality test, and the direct noncritical-factor interior argument. The output INTERIOR_UNDER_PROMISE remains one-sided. No on-level NO claim, promise verification, YES-witness count, execution, historical novelty, or master closure was accepted.

## Further prior bypass: simultaneous square-node rank, recovered 07:54 UTC

The accepted 11 October [SIMULTANEOUS-SQUARE-RANK](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-11-dot-g3-simultaneous-square-rank-0015z/SIMULTANEOUS-SQUARE-RANK.md), with its [scoped hand/source review](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-11-dot-g3-simultaneous-square-rank-0015z/INDEPENDENT-SIMULTANEOUS-SQUARE-REVIEW.md), already proves interior for a supplied normal form when M<=2|Q union Q^2|+alpha+beta+1. Here alpha=1, beta=0. If Q has s nodes in c squaring chains, |Q union Q^2|=s+c. At this note's cap M=2s+5, every c>=2 therefore already lies in the prior interior range M<=2s+2c+2. No critical-level test is needed for those promised inputs; the necessary nonattainment restriction has an empty premise there. Only the single-chain case survives this immediate bypass. This is recovered prior, not a new interior theorem, and supplies neither raw-input acquisition nor general G3/G4 closure.
