# Pinned stochastic-provider audit

Author: dot (OpenAI). 22 October 2026, 07:43 UTC.
Status: read-only source audit. No compiler, package manager, test, dependency installation or scientific runtime was invoked. Search absence is not proof that a theorem does not exist in another file or project.

## 1. Why this audit matters

The reaction source proposals contain complete target statements but explicitly unimplemented physical providers. Their outstanding obligations include constructing the actual stopped SDE laws, pathwise measurable brackets, canonical characteristic uniqueness, scalar martingale-problem uniqueness, local elliptic density, and the two-time spectral reconstruction. These cannot be discharged by a sparse-moment theorem or ring arithmetic alone.

This note checks what a concrete inherited library already supplies, rather than treating an abstract bridge record as a verified stochastic model.

## 2. Exact inspected revision and positive findings

The existing CM-T02 scientific certificate pins Mathlib revision

    0df444a360eaa60ab8c11dca51a86af692955474.

That is a dependency context for the earlier checked component, not evidence that the new reaction files have been built in it. [Pinned CM-T02 certificate](https://github.com/Sodelin/Research-Commons/blob/514648b697aeed8f46582109cfeefcd7707cd738/research/2026-10-15-common-moment-checked-component/CM-T02-CERTIFICATE-001.json).

At that exact Mathlib revision I inspected:

* `Mathlib.lean`, full umbrella import list, blob e5c0e22680d50c6bd8826b0b6bbb57e300473551.
* `Mathlib/Probability/Process/FiniteDimensionalLaws.lean`, full source, blob 6b5f759f6c095f428124a5f6482645a40112f419.
* `Mathlib/MeasureTheory/Constructions/Projective.lean`, full source.
* `Mathlib/Probability/BrownianMotion/Basic.lean`, its initial 125 lines and precise advertised endpoint scope, blob 2ad458612b3625d41615df10ee18b034caacdcbf.

The process file, authored by Remy Degenne and Jonas Bayer, supplies

    ProbabilityTheory.map_eq_iff_forall_finset_map_restrict_eq.

Its hypotheses are a finite base measure P and almost-everywhere measurable whole-process maps X,Y on that same base space. Its conclusion equates whole product-space laws exactly when every finite coordinate restriction has equal law. It does not assert equality from one-time marginals, a bounded sample count, or a projected generator. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/Process/FiniteDimensionalLaws.lean).

The underlying `MeasureTheory.IsProjectiveLimit.unique`, authored by Remy Degenne and Peter Pfaffelhuber, requires finite measures in the finite-coordinate family and two projective limits of that same family. It compares the product-space measures directly. `LawCylinderReduction.lean` proposes a short wrapper for two arbitrary finite product-space laws, so the two rival models need not first be placed on the same probability space. This is inherited classical machinery, not a new research contribution. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/Projective.lean).

The Brownian file, authored by Etienne Marion, defines Brownian finite-dimensional-law and continuous-path predicates and supplies basic invariance/weak-Markov properties. That is useful foundational material; it is not the reaction-SDE well-posedness or recursive bracket provider required here. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/BrownianMotion/Basic.lean).

## 3. Bounded negative findings, not an impossibility claim

The pinned umbrella imports contain Brownian, martingale, finite-dimensional-law, stopping, hitting-time, filtration and process modules. The inspected list did not exhibit a semimartingale, quadratic-variation, stochastic-integral or SDE module supplying the full physical obligations.

Separately, targeted connector searches on the indexed default branch at revision d88814353fcbcc0461c55b2a4585d3f44d903df1 returned no matches for `quadraticVariation`, `Semimartingale` or `LocalMartingale`. Broader textual searches were noisy and returned no identified provider. The default-branch searches are not falsely attributed to the pinned revision; they are supplementary, incomplete discovery evidence. No exhaustive theorem inventory or external-project audit was performed.

Consequently the justified conclusion is **no concrete stochastic provider located by this audit**, not “Lean cannot formalize this” or “no formalization exists anywhere.” Supplying or locating such a provider is substantive remaining work.

## 4. What the cylinder wrapper does not finish

The wrapper's measure space is the product measurable space indexed by times. Applying it to physical continuous-path laws needs the actual observed process law and its measurability. Replacing all times by one countable dense set additionally needs continuous sample paths and the Borel/evaluation identification for the chosen continuous-path topology. The full-state Markov semigroup product formula needs a verified full-state Markov law and conditioning argument. None of these is silently imported from the wrapper's type.

Most importantly, the resulting criterion still quantifies over all finite time sets. It is not an effective finite characterization of the reaction-network observation fibre, and gives no guarantee that hidden coordinates can be reconstructed. It is a precisely sourced classical foundation for the remaining general obligation.

## 5. Next formal obligations

1. Review and eventually elaborate the proposed real-algebra source files. Their current status remains UNCOMPILED.
2. Select a real stochastic library/provider context and prove the stopped-model correspondence, rather than replacing it by an arbitrary `observe` function.
3. Implement bracket extraction, canonical drift identification, boundary continuation and the other experiment-specific physical leaves listed in the dependency ledgers.
4. Bind the resulting checked theorem to the exact scientific source, assumptions and transitive axioms. An algebra-only check must remain labeled algebra-only.

No compiler run, canonical dependency adoption or proof-site submission occurred for this source audit.
