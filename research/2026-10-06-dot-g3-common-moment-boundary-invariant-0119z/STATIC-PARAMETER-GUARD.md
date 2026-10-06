# Static-parameter guard: a precise uniform-family transfer lemma

6 October 2026. Working supplement to COMPARISON-WORKING.md; elementary invariant logic, not a completeness assertion.

The accepted source state is q=(theta,K). Every legal append preserves theta exactly; all protected parameter ties and finite register assignments remain in this static coordinate or in the genuinely joint K carrier as required by the compiler.

Target states whose theta lies outside the admitted static domain D_c are excluded by the invariant theta in D_c itself, since initialization requires D_c and every append preserves theta. Thus the point-separator premise below is required only on admitted static fibres.

Fix theta0 in the admitted static domain. Suppose J(K) is an inductive semialgebraic invariant for the ACTUAL source transition relation specialized to theta=theta0, containing every legal initialization at theta0. Then

    I_theta0(theta,K) := [theta != theta0] OR J(K)

is an invariant for the entire static-parameter family. Here theta!=theta0 means that at least one coordinate differs, a finite semialgebraic disjunction. At other theta the assertion is automatically true. At theta0, initiation and consecution are exactly those of J. Since transitions never change theta, these two cases cannot leak into one another.

Consequently, if J excludes a hidden kernel tuple K0 at theta0, I_theta0 excludes the complete joint state (theta0,K0). The proof does not average parameter assignments, choose different parameters for different observed rows, or loosen a protected tie: the response target is still evaluated at that same theta0 and K0. J must use the entire required joint K/register carrier, not independently fitted marginal slots.

Suppose a source-specific point-separation theorem supplied such J for every target state of a negative original fibre, with one finite bound on its Boolean syntax and polynomial degree, uniform over theta0 and K0 in that fibre. The guard above adds only a fixed finite number of linear equality tests determined by dim(theta). Therefore all the lifted invariants fit a finite global template budget. The invariant-hull construction in COMPARISON-WORKING.md then produces one semialgebraic invariant excluding the entire target fibre by RCF quantifier elimination.

No continuous, algebraic or computable choice of the coefficients of J as a function of theta0,K0 is required. Coefficients and theta0 range as real variables in the uniform template quantifiers. The final hull has an effective real-algebraic formula because the original compilation/input coefficients do. The necessary UNPROVED premise is uniform finite syntax/degree of source-valid point separators across the negative fibre; existence of separately unbounded-complexity separators is insufficient.

This distinguishes two issues often conflated in a transfer from fixed-system invariant priors: arbitrary variation of numerical separator coefficients can be handled exactly, whereas lack of a uniform finite template family remains the substantive obstacle. It supplies no original-source point-separation theorem on its own.
