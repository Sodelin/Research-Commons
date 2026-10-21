# Keep native LAW G and natural gamma distinct

This is a source contract finding, not a new execution or a canonical physical
solver bug. The existing native LAW route has no physical admission; CHART
remains outside canonical native_rc1. The row-export adapter preserves the
original ports and performs no parameter substitution.

At frozen4e556c4a, law.rs SHA256
e519d232bbea12fa7181a7f5c8c700608d2debf412e519fe7f26abc03564c8a2:
routes gives group0 factor G and group1 factor1-G (COMMON), or
G^len(group0)*(1-G)^len(group1) (INDEPENDENT). Groups zip with the literal
hybrid.incoming order, and emit_edge writes group i to incoming[i].
Thus native formal G:h is probability of incoming[0].

The original Lean HybridProbabilities/originalCoinMass uses gamma for Bool
true, and OriginalParentRegistry/coinSelector maps true to parent1. Typed
natural gamma is therefore P(parent1). Exact source hashes/lines are in
evidence/PARENT-PARAMETER-SOURCE-REVIEW.json.

If native incoming[0]/[1] correspond to Lean parent0/parent1 respectively, the
binding is G_native=1-gamma_Lean. If an EXPLICIT occurrence-preserving port
bijection identifies native incoming[0] with Lean parent1, it is G_native=gamma.
A shared symbol or hash is not that proof. Do not silently swap original ports
or complement one bank coordinate without changing every associated constraint
and readout under the proven correspondence.

Native CHART COIN indices are interval coordinates; the matrix compiler alone
does not bind them to native LAW G or authenticate either physical meaning.
Source parents, shared bank/layout, nonlinear readout and runtime-origin
obligations remain separate from the exact value checks.
