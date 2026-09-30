# Independent proof audit: dynamical transfer at every step

Reviewer: /root/current_sparse_scope_audit. Date: 2026-09-30 UTC. Review of the root's announced theorem contract; no machine certificate, scientific bridge validation, or historical novelty claim.

## 0. Verdict

The exact quotient-factor theorem and the approximate all-horizon recurrence are sound with the domains and global error assumptions below. They apply to arbitrary state sets and nonlinear maps. They establish a positive mathematical transfer criterion; “similar shapes” or an unforced dynamical analogy alone do not establish causal or cross-field correspondence.

## Exact theorem: complete iff, not a finite check

Let T:X→X, h:X→Z, and Z_0=h(X). Then a map S:Z_0→Z_0 satisfying h∘T=S∘h exists iff

    h(x)=h(x') ⇒ h(Tx)=h(Tx')   for every x,x'∈X.

Necessity follows immediately from applying S to the equal h-values. For sufficiency, define S(z) as the unique value h(Tx) for any preimage h(x)=z. The condition makes this well-defined; T maps back into X, so the value belongs to Z_0. The map is unique on attained codes. The construction uses uniqueness rather than choosing representatives.

Induction gives h(T^n x)=S^n(hx) for every x and every integer n≥0: the base case is the identity, and the next case applies the one-step commutation to T^n x and the induction hypothesis. Thus the whole orbit representation is preserved at every horizon, with no finite-level restriction. This is classical semiconjugacy/factor dynamics, not automatically an established self-similarity law for a scientific system.

For a family of controlled or interventional maps T_a:X→X and a declared action correspondence σ, exact preservation for every finite action sequence requires

    h∘T_a=S_(σ(a))∘h  for every admitted a.

Induction then preserves all finite input words, including words selected from represented histories. If several source actions share the same σ(a), their induced h-transitions must agree as well. A commuting unforced map does not certify these extra intervention identities.

## Approximate theorem and sharpness

Take a metric space Z_0 with S:Z_0→Z_0. Suppose S is L-Lipschitz, L≥0, and the defect bound

    d(h(Tx),S(hx))≤η

holds for every admitted x (or explicitly for every state reachable in the stated horizon). Start with z_0∈Z_0 and d(hx_0,z_0)≤ε; define x_n=T^n x_0 and z_n=S^n z_0. The triangle inequality gives

    e_(n+1)≤η+L e_n,    e_n=d(hx_n,z_n).

Induction therefore gives, for every n≥0,

    e_n≤L^n ε+η Σ_(j=0)^(n-1)L^j,

where the empty sum is zero and L^0=1, including L=0. No linearity of T or h is used.

This bound is sharp over the declared class: on real states, h is identity, T(x)=Lx+η, S(z)=Lz, x_0=ε and z_0=0 attain equality for L,η,ε≥0. The root's L=1 drift example is also valid: T is identity, S(z)=z+η, h is identity, x_0=0 and z_0=ε give error ε+nη while the global one-step defect is η.

For 0≤L<1 the bound is at most max{ε,η/(1-L)} uniformly in n. Contractivity is sufficient, not necessary: exact commutation and exact initialization preserve the orbit for every L, and an isometry with zero defect preserves an initial error. For L=1 and positive permitted defect, the assumptions alone do not promise small uniform-horizon error; the drift example rules that out. Claims of approximate preservation over every future step therefore need an explicit horizon, tolerance/stability argument, or additional model structure.

## Positive nonlinear example and limits

For every real a, let X=R, h(x)=x², T(x)=a x, and S(z)=a²z on Z_0=[0,∞). Then h(Tx)=a²x²=S(hx), hence h(T^n x)=a^(2n)x² for every real x and every n. This is genuine exact nonlinear representation transfer that deliberately merges x and -x. It preserves magnitude-squared trajectories but cannot recover the sign question. It is an illustration of the general iff, not the proof of it and not a new result.

A downstream answer f=g∘h transfers exactly through the represented orbit. Approximate representation accuracy yields a quantitative answer bound only with an output regularity condition: if g is C-Lipschitz, answer error is at most C e_n. A discontinuous decoder can turn arbitrarily small representation errors into a full answer error. Targets that are not invariant on h-fibers fail even under exact orbit commutation.

A semiconjugacy can be many-to-one; it need not imply an invertible conjugacy, full-state reconstruction, reciprocal transfer, causal equivalence, equality of mechanisms, or shared physical units. Two scientific domains need a justified state/action/observation correspondence. Naming h a “shadow” or “self-similarity” does not verify those premises. The controlled-map condition states exactly which additional identities a causal transfer claim would need.

## 11. Process integrity

Checked the universal iff in both directions, map-domain closure, uniqueness, arbitrary-horizon induction, nonlinear scope, controlled-family extension, error recursion, sharpness and horizon limitations. This is a mathematical contract review, not a systematic empirical review. The final root manuscript was not yet present when this review was written; it must retain these assumptions for this verdict to apply.

## 12. Robustness

The positive theorem survives nonlinear systems and arbitrary state cardinality. Its substantive limits are model/representation validity, target invariance, action alignment and error stability. A noninvariant h-fiber refutes exact factor existence. A violated global defect or undeclared intervention breaks the corresponding guarantee. A similar visual pattern without these relationships provides no theorem-level transfer assurance.


## Actual-manuscript follow-up receipt

Read the completed root-authored dynamics.md on 2026-09-30 UTC after the initial contract review. The actual manuscript retains the all-set fiber-invariance iff, unique quotient dynamics, induction over every finite horizon, prescribed-target and clock-scale distinctions, matched intervention and output requirements, globally trajectory-valid defect assumption, Lipschitz recurrence, downstream decoder regularity, and sufficient-but-not-necessary contractivity qualification. Its sharp drift example is valid. No fatal mathematical gap found. Its approximate S is defined on all metric Z, so approximate initial codes outside h(X) are explicitly covered. This actual-file reading resolves the initial manuscript-availability limitation; scientific validity and historical novelty remain separate.

Reviewed dynamics.md SHA-256: 56a90def1544caaef50713a141cd0af3366bfc0583d978dda093dc4add943ff5
