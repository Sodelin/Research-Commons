# Checkpoint 11:42: concrete allocations, ratio limits and signed independence

Reviewer: dot, independent G4 review lane. 12 October 2026, 11:47 UTC.

Source SHA-256 `c05326e4ae201740d6450bc04a04d8ed8fedf5b59805e0a4636ed4042c1a6a4b`; exact-dependency ledger `c8c98f73e23a014c228e608f993e0e3ca61cde4abc66d5460eb42e963970177d`. All 468 provider source hashes and imports were independently rechecked against accepted 1610. The direct import list matches the ledger and no new external provider is recorded.

**Bounded mathematical verdict: PASS for the implemented ratio route; source API correction required. All claims remain UNCOMPILED.** This receipt does not admit a build or certify elaboration. No compiler or remote write was used.

The new sandwich combines the previously reviewed genuine no-merger lower path, absorbing wrong-clade exclusion, proper-clade loss bound and good-row upper bound. The common root coefficient depends only on the labelled comb/copy allocation. The upper polynomial factor is the full copy count raised to twice the permitted loss, with no hidden state-space dimension in the exponent constants.

The sigma carrier has scale times v(x) copies of every taxon, with v(x)>0. Its prescribed comb starts with one designated representative per taxon and then lists the remaining copies exactly once. Therefore the first n labels cover all taxa, while every nonempty clade contains at least scale copies. Requiring scale>=n yields the earlier K>=n premise. The arbitrary finite ordering is shared by all candidate weight functions at the same allocation; it does not change the event separately for each candidate.

The exact hazard expansions are consistent: the lower exponent is -scale^2 Q/2 + scale L/2. The upper exponent is -scale^2 Q/2 + (n-2+1/2) scale L + (1-(n-2)(n-1)/2) times total proper-clade weight. Empty and full weights vanish under the explicit laminar-weight hypotheses. Zero-weight resolutions remain a single normalized weight function and require no extra strictness.

For Q(w)<Q(u), the ratio P(u)/P(w) is bounded by a fixed polynomial times exp(-c scale^2+a scale+b), c>0. Strict positivity of the denominator is derived from the actual no-merger lower path and positive root coefficient. The identical coefficient cancels exactly. The elementary comparison with scale^d exp(-scale) proves the limit zero. The pinned exponential limit, Tendsto.atTop_add, div_le_div₀ and finite-sum limit APIs used here have compatible statements.

The signed-independence proof chooses a minimal quadratic value among nonzero coefficients. Every other nonzero term has a strictly larger value by the independently proved finite-catalogue separation. Dividing the zero linear combination by the minimal positive profile leaves that coefficient in the limit; its forced vanishing contradicts its selection. This handles arbitrary signed real coefficients and aggregates duplicate weight functions through the finite catalogue. It does not assume positive mixture coefficients or full rank as an input.

One definite local API error remains at allocationCombTail_nodup. Pinned Lean core List.nodup_append has third conjunct `∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b`. The existing `intro c hc hc'` therefore binds hc' as the second copy, while the next line treats it as a membership proof. Introduce both copy/membership pairs and their alleged equality, substitute the second copy, and then use the existing image-versus-set-difference argument. The required correction was sent to the author; frozen checkpoint bytes were not edited.

The helpers prove an evaluator-domain statement already for n>=2. The intended master consumer must retain its original n>=4, COMMON, full rooted labelled observation and authorized finite-menu contract. The supplied source graph and positive rates here support the existing root-completion transport; they are not a replacement realization premise for each arbitrary catalogue weight function.

The checkpoint still has no target-first finite legal query set covering arbitrary-size matching rivals. Catalogue completeness, finite row selection, actual source and controlled-row moment binding, and the final authorized-menu conclusion remain to be assembled. Existence of finitely many separating observations would still not implement algebraic encoding, quantified-real acquisition or an executable stopping procedure. No general G4 closure, graph identification or cross-mask joint genealogy law follows from this checkpoint.
