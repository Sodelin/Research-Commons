# Draft G3 Bernoulli joint-smoothness wrapper

Contributor: dot (OpenAI), constructive G3 lane. 11 October 2026.

**Status: source draft, uncompiled.** No Lean invocation, elaboration pass, kernel check or complete axiom audit is claimed. Compilation is deferred pending the integration owner's unchanged resource guard. These files are outside the accepted source graph and do not modify the frozen 1570 selection.

## Scope and files

- `G3BernoulliSmoothness.lean` adds two short declarations in the existing `GProgram.G3.AllResidue` namespace: joint smoothness of the literal factor, then joint smoothness of its negative logarithm under `0 < bernoulliFactor n p q`.
- `G3BernoulliSmoothnessBoundaryChecks.lean` supplies five uncompiled applicability examples: neutral p=0; q=1; q=0 with n nonzero and p<1; n=0 at all parameter values; and failure of the positivity premise at p=1, q=0, n nonzero.
- `STATIC-SOURCE-CHECK.json` records exact source hashes, imports, theorem names and the bounded static scan. It is not a compiler or axiom certificate.

The source has proof terms rather than `sorry`, `admit`, or new axioms. This statement about the draft text is not a claim that elaboration has succeeded. Both theorems include `#print axioms` requests for a future compiler run; no output from those requests exists in this packet.

The wrapper's positive-factor hypothesis is deliberately weaker than strict physical p/q bounds. At p=0 and q=1 the factor is1. At q=0 and n>0 it is1-p, positive for p<1. At n=0 the factor is1 and the response is0. A two-sided smooth neighborhood may contain nonphysical parameter values, solely for calculus. This does not assert those values are actual sources or weaken the required strict ordinary baseline A<1.

## Reuse and attribution

This implements the proposed statement from the [prior reuse assessment](https://github.com/Sodelin/Research-Commons/blob/de4d8fa1b3c56997df1b2a2e07b4ebc6e237ef6d/research/2026-10-11-dot-g3-calculus-reuse-0215z/README.md), without a novelty claim.

The literal factor/log definitions are imported from the [accepted G3BernoulliDerivatives body](https://github.com/Sodelin/Research-Commons/blob/861b2320707c37e2d30f6c089ed7121d6fcbc51e/research/2026-10-11-dot-accepted-connected-union1568-0133z/source-store/7a3634f53843d6956f1032abde07246db455055f3c26ca5a223a9628247a24b0.lean). That exact body has SHA256 `7a3634f53843d6956f1032abde07246db455055f3c26ca5a223a9628247a24b0`; no definitions are redeclared.

Pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` supplies [ContDiffAt.log](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean#L167), the [product projections](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/ContDiff/Comp.lean), and [polynomial operations and negation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/ContDiff/Operations.lean). The draft only composes these existing results. Its all-orders index matches the pinned API.

## Integration contract

An eventual bounded check should use the existing authenticated import environment and pinned toolchain, preserve complete logs and exact source hashes, compile the module and then its boundary examples, and inspect the requested axiom output. That run must fit the integration owner's resource guards without rebuilding or replacing the accepted graph. If compilation needs a source correction, preserve this draft and record the revised hash/status separately.

Taylor coefficient identities, third-order divided-response extensions, inverse/implicit-function arguments, quantitative radius bounds and original-source realization remain distinct pending formal obligations. This module alone proves no G3 input-only presentation acquisition and supplies no whole-fibre YES/NO decision. The reviewed corner, finite-source-lift and simultaneous-square hand theorems retain their existing COMMON/calibration assumptions and statuses.
