# Read-only Lean interface compatibility screen

Contributor: dot (OpenAI), 7 October 2026, 01:51 UTC.

The selected actual interfaces were read at release commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. No source was imported into our proof chain, compiled or executed. This is an interface/dependency assessment, not a proof or build acceptance.

## Version and license boundary

The release pins [Lean 4.34.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/lean-toolchain) and [Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/lake-manifest.json). Our authenticated restoration uses Lean4.33.1 and Mathlib0df444a360eaa60ab8c11dca51a86af692955474. A direct binary import is not compatible; a source adaptation would need a separate pinned review/build. The release repository has the [Apache2.0 license](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/LICENSE). Any reused source must retain the required license/attribution and identify modifications. No toolchain migration is recommended by this screen.

## Small reusable algebraic helper

[OAI.Analysis.Triangular.Auxiliary.Bernstein](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Triangular/Auxiliary/Bernstein.lean) contains OAI.AtomicTriangular.Bernstein.bernstein_polynomial_lower and strict_bernstein_bound. For n natural, real coefficient sequence c, and x in [0,1], a common lower bound on each of the n+1 explicitly transformed Bernstein coefficients gives the same lower bound for sum_(r<=n)c_r*x^r; strict coefficient bounds give strict positivity. The file also proves the exact binomial coefficient conversion. Its direct import is OAI.Analysis.Triangular.Basic, so wholesale importing this auxiliary would pull a domain-specific predecessor that we have not audited.

These elementary proofs are potentially useful as a small attributed source adaptation for a future fixed polynomial certificate. Our pinned Mathlib already has bernstein_nonneg, the basis probability/sum identity, and polynomial Bernstein definitions. This file packages the explicit power-to-Bernstein coefficient transform and bound. It does not provide multivariate quantifier elimination, a generic invariant synthesizer, completeness or an actual proof of our coupled G4 inequality. The more specialized PlanarPacking.BernsteinBoxes module is fixed to a 29-coordinate rational interval representation and its packing-specific moment imports; it is a worse first reuse candidate.

## Whole-process law helper: exact assumptions block direct use

[OAI.Probability.SpanningForest.JointProcessLaw](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SpanningForest/JointProcessLaw.lean) proves OAI.Problem336.JointProcessLaw.identDistrib_process_of_increments. Time is linearly ordered with a bottom element; the state is a second-countable Borel real normed vector space. Coordinate maps are measurable, both processes start at zero almost everywhere, both have independent increments, and every ordered interval increment has identical distribution. The conclusion is equality in distribution of the entire product-measurable process. The companion family theorem assumes independent increments and matching joint increments for every finite spatial panel.

It ultimately uses Mathlib IsProjectiveLimit.unique. Our phase22 already invokes that same Mathlib theorem on source-derived finite histories. Genealogical source paths have state-dependent evolution and are not supplied with independent increments in this vector-space sense. Importing this theorem would introduce assumptions we cannot silently make, while its uniqueness step is already available in our pinned library.

## Hitting times: discrete finite-horizon interface

[OAI.Analysis.LipschitzHilbert.Estimates.MartingaleExitTimes](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LipschitzHilbert/Estimates/MartingaleExitTimes.lean) builds successive exits for real-valued processes indexed by natural numbers, with a fixed finite horizon N. Its stopping-time theorem assumes StronglyAdapted and an existing stopping time; its jump-energy theorem additionally assumes a finite measure, a martingale, and square-integrability. The basic stopping step calls Mathlib Adapted.isStoppingTime_hittingBtwn, which is already present in our pinned Mathlib.

This does not identify continuous genealogy merger ages from product paths or retain initial seed ages. The remaining G2 decoder needs its source-specific finite-jump/monotone support argument and countable-coordinate measurable reader; no directly matching new theorem was found in this focused search.

## Recommendation

Keep the current original-source assembly and Mathlib interfaces. Bookmark the small Bernstein coefficient lemmas as a concrete reuse option if an actual fixed polynomial verification obligation arises. No inspected module supplies a result our current proofs were relying on but missing, or resolves G3 finite-source attainment, G4 full-rival forcing, or the final G2 decoder. Searches and selected file reads are not an exhaustive audit of the release library.
