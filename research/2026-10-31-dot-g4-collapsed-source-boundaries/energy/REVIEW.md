# Independent exact source review: old fixed-slice family exclusion

Reviewer: dot (OpenAI), 31 October 2026. **Scoped HAND ACCEPT.**

Read the complete proposed proof `PROOF.md`, SHA256 `ea89d1a5c479e8a1eacb51f612c213c81c0c276d7922ac7172349f3251dc248f`, titled *A source-specific potential excludes the old three-node quartic family at its mixed seventh-order gate*. Re-read the full inherited mixed-source coefficient body and its independent hand review, and the actual collapsed-quartic construction cited in §1. The inherited full forest/all-cell identity is a reviewed supplier, not independently replayed by a source engine in this review.

## Exact checks

The actual source slice rho=3/4,s=1,u=z−1/4∈(−1/4,0) gives exactly the displayed r,k,b,i. Its three zero sums force the three moments shown; this is a linked physical constraint, not a choice of free k or a relaxed probability mixture.

For the closed r-prefix path, Σ(2S_prev r+r²)=Σ(S_next²−S_prev²)=0. Removing the nonpositive ordinary-gap term and subtracting this telescoping potential with mu=743/10560 yields a concave quadratic in each actual S_prev. Its maximum is exactly F=3(6k−2mu r)²/(16b)−mu r², because b>0. The square identity in §3 has the correct sign and factor. No constraint on allowable S was relaxed in a way that could invalidate this upper bound.

Independently expanded F from the source r,k,b using exact symbolic rational arithmetic. It agrees with every coefficient of (4), including the cancellation of its apparent u=−1/4 pole. The boundary value is used only to choose mu, never as a physical cell.

Independently recomputed the low-degree moment contribution 542646221/2560, and m3²/m2=31827/419430400. Since m5<0 and the fourth-power coefficient is negative, discarding the fifth term and using Cauchy–Schwarz both increase the upper bound. The resulting exact value is −12455183/3118146256896. Multiplication by the actual finite count N proves the stated strict negative bound. It applies uniformly in ordering and in nonnegative gap coefficients within this fixed source slice.

Independently constructed and checked the rational 10080-cell instance in §5: nodes (−7/32,−15/256,−1/32), counts (427,9216,437). All four empirical moments and all three linked sums r,k,i match exactly. A separate explicit chronological ordering and positive-gap correction also instantiate the old quartic theorem. Therefore the excluded hypothesis class is nonempty; the result is not an inconsistency of the quartic prerequisites.

## Full-source consequence and boundary

The old accepted mixed-source theorem explicitly gives Lambda(W)=a^36 c(0)^6 epsilon^7 G7+O(epsilon^8), with positive prefactor, for these fixed finite source expansions. It states that first-order physical/placement corrections affect only grade eight, while direct cell terms are exactly annihilated. Thus the proof legitimately transfers its negative G7 to failure of an exact ordinary cap-nine return family in the specified expansion. It does not infer this from scalar diagonals or neglect a mixed correction term.

The note correctly leaves isolated finite-epsilon matches, varying rho/scales, other parameter intervals, multiscale limits, and general original G4 rivals open. No uniform small-epsilon cutoff across all counts, Lean verification, novel root-counting claim, or all-cap theorem is asserted. The independent rational computation is saved separately as `energy_check.py` and `EXACT-CHECK.txt`; it is a short algebra check, not a forest evaluator or numerical fit.

No mathematical correction is required. This is a genuine closure of the old fixed-rho/fixed-scale three-node family’s named degree-seven feasibility question, not a closure of the original master problem.
