# Independent hand review: uniform small-bad-cell positivity

Reviewer: Codex fixed-target-negative subagent, 13 October 2026. Author: Codex chronology subagent. **Verdict: ACCEPT at the stated source-specific hand-proof scope.** This is independent mathematical review, not Lean verification or a master G4 acceptance.

Reviewed: [SMALL-BAD-CELL-UNIFORM-POSITIVITY.md](../chronology/SMALL-BAD-CELL-UNIFORM-POSITIVITY.md), together with the exact October 10 ordered two-merger integral, uniform ratio transport, negative-primitive proof, weak-scale positivity proof, and the independently derived [compact-uniform parabolic limit](FIRST-PRIMITIVE-REVIEW-AND-PARABOLIC-LIMIT.md).

Reviewed candidate SHA256: `f6fccdf4fef58bdd2d63e535df4c12d0ec6ac5377dc7928146c23b1efdad0908`. This pin includes the author's explicit link to the companion limit proof.

The crucial checks were:

1. The hyperbolic comparison applies after weighting by `kl`, which changes the routing law to the centered `(n-4)`-root tilted binomial with the same physical `h,t`. The positive and negative integral decomposition is exact. The inherited proof bounds the specific negative integral `N_n` by `1/20`; no invalid inference from a bound on `A_n^-` is made.
2. On the early triangle, the signed mean bound and `sinh(h)tanh(h/2)=cosh(h)-1` give the stated first-cosh bound. The second moment bound gives exactly `epsilon^2/(4n)+epsilon^2 D/8`. Under `nD>=1`, the remaining coefficient is greater than `1/2` at `epsilon=1/32`.
3. For `n>=6`, `(n-2)(n-3)>=n^2/4`. The exponential factor, outer factor and triangle area have the stated bounds. Direct multiplication gives `P_n>=2^-23 nD` when `p>=1/8`, so the author's weaker `2^-24 nD` is valid.
4. In a hypothetical bad-cell countersequence approaching the origin, the old weak-scale theorem forces `nt>1/16` and hence `n->infinity`. Unbounded `nD` is excluded by the early-triangle estimate. Bounded `nD` makes `sqrt(n)h` bounded, and the bad-cell condition bounds `nt` above. The compact-uniform parabolic limit then has a strictly positive limit at every subsequential parameter limit. This proves a single semantic delta for all arities, rather than a different delta at each arity.
5. The countable-carrier budgets imply only finitely many failures of the two smallness conditions. In a no-first-cell carrier each exceptional cell begins at a positive source position, so a sufficiently short initial interval avoids every exception. This transfers positivity to its bad-cell contributions with their actual positive chronological weights.

The theorem does **not** prove positivity of every arbitrary cell, the conjecture `A_4>=0 => A_n>=0`, positional dominance over interlaced good-cell negatives, a finite skeleton, an original whole-source observer, or a fixed-target negative construction. It supplies an all-arity sign theorem for sufficiently small bad cells and the stated countable-carrier consequence. Those are the exact accepted advances.

No source compiler, numerical parameter scan, real-closed-field search, Lean compilation or Rust execution was used in this review. The independent parabolic calculation includes an elementary symbolic integration check, separately labelled in its note; this universal sign review is by the displayed inequalities and compactness argument.
