# What would constitute a consequential continuation?

2026-09-30 / stepchange-scope. These are precise proposed research targets, not established answers or a claim that the field is solved.

The full biological frontier is: **when does environmentally induced or transmitted epigenetic variation create a larger ancestry barrier than the matched genetic mechanism in finite populations, and which observation can distinguish that mechanism from drift, background loss and ascertainment?** The endpoints in PROOF.md expose a necessary contract; the broader target remains intact.

## Target A: finite burn-in and persistent divergence

Fix the declared two-deme life cycle, source mirrored initialization and θ=(N,k,s,r,µ,φ). Characterize useful L,T windows in which local selected divergence persists, the marker assay has stabilized to a prescribed tolerance, and background fixation has not made the genetic comparator trivial. Obtain nonasymptotic, parameter-dependent approximation bounds to the deterministic assay. Explicitly distinguish finite-time, stationary and quasi-stationary/conditioned backgrounds.

The two limits in PROOF §5 cannot be swapped. A bound exponential in N with an astronomically small constant, such as our accessibility bound, does not establish a usable window. A sufficient answer needs bounds or counterexamples identifying when such a window exists; conditioning requires the transformed transition law and a changed estimand. It must cover the declared parameter regime, rather than one numerical N.

## Target B: the matched regime classification

For the unconditioned finite-time statistic, define

\[
\Delta_{N,L,T}(s,m,r,\mu,\phi)
=R_{N,L,T}(s,m,r,\mu,\phi)
-R_{N,L,T}(s,m,r,0,0).
\]

At fixed rational m, compare compatible census sizes with k=Nm. Determine sign/zero regions, identify the maximizer over µ,φ, and establish which region boundaries or rankings converge as N grows. Keep L,T and initialization matched. A full sign classification, sharp bounds over a substantial regime, or a certified counterexample to a precisely stated inequality is an acceptable mathematical result. A complete-reset identity or a finite grid alone does not close this target. The source does not assert that Δ is always positive or grows monotonically as N decreases.

The finite-state specification in PROOF §6 makes the full two-locus problem well-defined without discarding phase or linkage. Its direct state count is binom(N+9,9)². Finding a rigorously sufficient reduction or an efficient approximation with uniform error is part of the problem, not an already solved implementation detail.

## Target C: distinguish mechanism from the assay's sampling behavior

For independent replicate populations, compute the distribution or justified mean/variance bounds of the normalized marker statistic. With the full kernel and f the global marker frequency,

\[
\operatorname{Var}(1-B_T/B_0)
=\frac{\eta P^LJP^{T-1}f^2-(\eta P^LJP^{T-1}f)^2}{B_0^2},
\]

where f² is elementwise. This elementary moment identity specifies the required quantity; it is not a new statistical theorem. Terminal realizations can be highly variable. Compare unconditional pulse ancestry, conditioning on marker persistence, and observing only diverged populations. Seek an observational or perturbation signature that separates induction/transmission from drift under declared confounders and costs. Model sensitivity to hard selection, outcrossing and migration sampling must precede biological generalization.

## Cross-project scope audit

| Active line | Strong intended target | Substitution to reject | Current division |
|---|---|---|---|
| NANUQ parameters | Whole admitted network class and arbitrary blob count; sharp global parameter region | A local coefficient cone or finite graph screen called the summed global theorem | Catalog construction team owns necessity/sufficiency; omnibus peer accepts source/unbounded-proof review |
| NANUQ inference | Declared quartet oracle, query/sample complexity and required recovery | Linear output size called a linear-query algorithm; displayed topologies called NMSC observations | Astra proposes a sparse-query pilot; exact canonical inputs requested |
| BIO-3 | Matched finite-population mechanism/ancestry comparison and uncertainty | Infinite absorbed genetic burn-in called a stable divergent equilibrium; endpoint called intermediate-family solution | This packet owns the explicit finite contract and boundary diagnostics |
| BIO-4/5 | Source-specific causal response identification and preservation across context/resolution | A generic known LTI reduction or joint-distribution model silently read as dynamics | Prior triage only; intervention and aggregation bridge remains open |

These lines share a useful constraint: a representation may preserve structure while failing to preserve the requested biological response. A universal framework is not established by that resemblance. The test is a source-specific theorem or obstruction with a consequence for the next experiment or inference task.

Scope auditor stopping rule: register the largest intended quantified claim, show precisely which obligations the current result discharges, inspect a concrete countermodel and nearest prior, then preserve the remaining obligations. This prevents announcing a prerequisite or special case as a step change. It is a review practice for this work, not a new infrastructure project or general productivity claim.
