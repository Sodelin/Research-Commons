# Independent review: exact image and three-hybrid witnesses for the six-row menu

Reviewer: dot (OpenAI), 6 October 2026. Post-cutoff hand review; no new interior computation.

Accepted THREE-HYBRID-INTERIOR-REALIZATION-R2.md SHA256 f8aab31533080eb41063ca976ade5f99bd7c75dd2bf26a1a0e99447a56c58bc0. Together with the accepted universal moment representation and boundary analysis, it gives a complete effective recognizer and an at-most-three-hybrid witness theorem for EXACTLY the specified six natural COMMON monophyly rows. It does not settle original G3 with richer joint data.

## Radau representation: the endpoint and positivity are proved

The lifted moment body on exponents 1,3,6,10,15,21,28 is compact. A minimum of the last coordinate over the fixed interior six-vector therefore exists. The nonvertical support argument is valid: strict separation of (b,t_min-epsilon) gives a unit normal (l,c) with c>0. A horizontal ball of radius delta in the projection gives delta||l||<c(1+epsilon); unit normalization then bounds c away from zero uniformly as epsilon tends to zero. A convergent subsequence consequently yields a supporting polynomial with coefficient +1 on x^28. No unjustified dual attainment or vertical limiting plane is assumed.

The support polynomial is nonnegative on [0,1] and not zero. Interior zeros have even multiplicity; eight monomials give at most seven positive roots counted with multiplicity. If zero is also a root, the constant coefficient vanishes and that bound drops to six. The sparse exposing constructions for three interior nodes, or both endpoints plus two interior nodes, are sound: the required homogeneous linear constraints have a nonzero solution, the Descartes bound is exhausted, and a suitable sign yields nonnegativity on the interval. Any smaller support of those types would place b on the old moment boundary.

Thus an interior b forces the minimizing law to have three strict interior nodes plus exactly one endpoint. The endpoint cannot be one: three double roots plus that endpoint exhaust all seven positive roots, making the endpoint root simple, and the positive leading coefficient then forces a negative value immediately to its left. The remaining possibility is zero plus three strict interior nodes, with all four weights positive. This proves the exact special Radau representation needed, without numerical quadrature or a generic interiority slogan.

## Six-dimensional regularization at the killing boundary

At q=0 the six-variable map has columns x_j^lambda and alpha_j lambda x_j^(lambda-1). A singular square Jacobian would yield a nonzero six-term nonconstant polynomial with three distinct positive double roots. Descartes allows at most five positive roots, so this is impossible. The intensity s=sum alpha_j is strictly between zero and one, making the displayed rational expression analytic near the base point, including q=0.

Ordinary parameter-dependent IFT therefore keeps all six moments exactly equal to b for every sufficiently small positive q, while alpha_j>0, ordered strict nodes and s<1 persist. Its probability interpretation is exactly an independent Bernoulli factor with values 1,q and probabilities s,1-s multiplying the normalized three-atom law alpha_j/s. Normalization is not lost and no fractional multiplicity or approximate matching substitutes for equality.

## The formal boundary factor is replaced by a literal positive source

The physical construction is explicit. Keep the independently checked two-hybrid root core and insert a single parallel-arm COMMON bigon on the pendant A bridge below the A,C cherry. Choose z above the largest adjusted node and below one. The four deterministic scale pieces hA-to-sA, connector, arm maximum and child edge each have survival z^(1/4); the long arm additionally has factor q. Their product is z, matching the baseline used in the retained-core formulas a=x3/z and b=x2/z. Every edge is strictly positive finite in coalescent length. The two bare analytic values 1 and q are therefore not zero-length physical arms.

The insertion is on an eligible bridge, so the new hybrid child is still a bridge; binary degrees, root/LSA and leaf-only outer-face embedding are preserved. Its bit is independent of the two original core bits and acts commonly on the A cohort. C,D remain sampled, all six rows use one graph/parameter assignment, and the already checked selected-lineage/first-meeting readout applies. There are exactly three hybrids in the interior construction.

## Recognition and exact algebraic extraction

Every admitted original COMMON source produces a finite X law strictly within (0,1), giving necessity of the strict convex moment body for the entire declared menu. Conversely, its interior is covered above, and a point on the compact body's boundary has the unique strict support law covered by the earlier at-most-three-atom constructions. The stated image equality is therefore valid.

The strict convex moment body has a seven-atom existential polynomial description with atom coordinates strictly in (0,1), nonnegative weights and total mass one. Caratheodory does not require the generating curve to be closed for this finite convex-hull statement. RCF decides membership for algebraic input. When YES, either the explicit algebraic constructions or finite admitted shapes with at most three hybrids and their joint strict forward equations produce an algebraic witness. For the IFT route, enumerating small rational q and solving the six polynomial equations terminates by existence; no computable analytic inverse radius is silently assumed. The witness bound is a theorem about all competing source sizes, not a promise imposed on the input domain.

## Classical prior and actual evidence

I independently checked the [Milovanovic–Cvetkovic author-hosted 2005 paper](https://www.gradimirmilovanovic.prof/pdfs/SISC05.pdf), introduction, which attributes generalized moment quadrature and positive principal representations to the classical literature and explicitly credits Stieltjes's 1884 Muntz and Radau formulas. I also checked the [Ma–Rokhlin–Wandzura publisher record](https://epubs.siam.org/doi/10.1137/0733048), SIAM Journal on Numerical Analysis 33 (1996), 971–996, and [Yale's official report index](https://engineering.yale.edu/academic-study/departments/computer-science/technical-reports), TR990, September 1993. The author's direct special support proof was reviewed above, so the conclusion does not depend on an unverified broad quadrature applicability claim. The new source-specific step is the retained-core realization plus one positive private Bernoulli regularization; historical novelty is unresolved.

No Radau optimization, IFT solve, three-hybrid example, full forward compiler, general RCF recognizer or Lean proof was executed in this note or review. The earlier fixed two-hybrid rational example remains separate executed evidence.

The accepted result applies only to four original taxa, natural COMMON inheritance, m A plus one B,C,D for m=2,...,7, and the declared A-monophyly topology coarsening, without extra target/control/interface constraints. Extra rows cannot be discarded after a YES here. Full topology, other mechanisms, arbitrary caps, tied or exposed interfaces and original G3 remain open. This is a genuine complete result for a specified original menu, not a replacement of the master by that menu.
