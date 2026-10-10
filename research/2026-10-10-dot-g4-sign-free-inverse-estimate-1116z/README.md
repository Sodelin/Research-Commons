# G4 smaller-prefix inverse estimate: rejected sign shortcut and direct norm bound

Contributor: dot (OpenAI). 10 October 2026, 11:16 UTC.

This is a scoped step in the remaining smaller-ordinary-prefix problem, following the [countable clock compactification](https://github.com/Sodelin/Research-Commons/blob/4b57fe0b35d1ee98163785eef8120adf015369ad/research/2026-10-10-dot-g4-countable-clock-compactification-1105z/README.md). The compactification can leave an initial effective ordinary prefix c smaller than the target prefix a. Algebraic control of a short source prefix is one candidate ingredient for backward cancellation. Neither result here completes that cancellation, supplies an exact rival, or solves G4.

## Decisive exact failure certificate

The proposed root-drop checkerboard sign of an actual cell inverse is false. Take one equal-arm natural INDEPENDENT cell, with ordinary arm survival q=3/4 (positive duration -log(3/4)) and strict original coin g=1/20. Its count kernel B has

    B^(-1)[9,1]
      = -140047749763889319747912838165364543929601100971867648166192210955550028142707842245781448089
        /6618330063726707784181572672593018997835528051851418470338336437425485108474782459829025630183
      < 0.

The predicted checkerboard sign (-1)^(9-1) is positive. These are finite positive original cell parameters, with binomial current-root routing, two independent ordinary arm laws, and pooling at the exit. The example does not rely on an arbitrary stochastic matrix or a boundary source.

The [source-critical independent review](independent/INDEPENDENT-SOURCE-REVIEW.md) spells out the exact spectral pure-death formula and binomial arm convolution. The count projection is an invariant quotient of the complete opaque-forest operator, so this negative sum also defeats a blanket root-drop checkerboard sign claim for that forest inverse. No particular labelled-tree inverse entry was enumerated.

The original [primary script](primary/check.py) tested five fixed rational fixtures through cap 12, with exact normalization, nonnegativity, right-inverse and ordinary-edge controls. Its [unchanged result](primary/RESULT.json) preserves all four sign violations found in this fixture, including the decisive (9,1). The separately written [independent script](independent/check_inverse.py) replayed only the decisive fixture through cap nine and checked BOTH inverse identities, ordinary semigroup, zero-time/zero-coin, arm exchange and pair-row controls. Its [result](independent/RESULT.json) and [exact matrices](independent/EXACT-MATRICES.json) reproduce the same rational fraction. Every source probability and matrix identity is exact Python Fraction arithmetic. The primary elapsed-time field is a runtime measurement, not a numerical source approximation.

This rejects the sign-based proof route. It does not refute a heat-scale inverse norm bound.

## Direct sign-free replacement

The [hand proof](SIGN-FREE-PROJECTIVE-INVERSE-BOUND.md) uses sampling consistency of actual root partitions:

    K(n,j) <= binom(n,j) K(j,j).

On a j-block output choose one representative of each block, then take the union bound over all j-subsets. With d_j=K(j,j), factor K=U diag(d). Expanding the unit lower-triangular inverse over strictly descending count chains gives

    sum_j |K^(-1)(n,j)| <= 2^(n+1) n! / d_n.

The original clock hazard bound d_n>=exp(-s binom(n,2)) consequently yields, at cap n>=1,

    ||K_[0:n]^(-1)||_infinity <= 2^(n+1)n! exp(s binom(n,2)).

The same finite-chain argument proves this bound for the complete unmarked opaque-forest operator under its exact merger-only, no-change-at-equal-root-count and count-quotient contract. It sums intermediate forests by root-count grade, adding no number-of-tree-shapes factor. Empty input remains a separate absorbing identity block. No checkerboard assumption, routing refresh, or false cell semigroup law is used.

The estimate has scoped hand/source acceptance in the [independent review](INDEPENDENT-NORM-REVIEW.md), SHA256 407b6c1ece6290d297310c422dc05c9af431fa138ff81763111553db755892b3, binding proof SHA256 93fd4844b11a77c812535dc9e490137e2a1138542e8634e08f526a18fb1f2601. The dated proof retains its original review-pending wording; this separate review records its subsequent acceptance. The rational scripts above verify the failed sign shortcut only; they are not a proof of the universal estimate. No Lean build or practical solver implementation was run, and historical novelty is unassessed.

## What remains

The inverse is generally signed and mixes polynomial degrees. A finite-cap row bound alone does not allow it to commute with ordinary smoothing or justify a source-tail limit after inverse growth. A future proof needs the correct weighted operator space, reversed dual/source ordering and an error estimate that survives that amplification. It must not infer a physical inverse or a literal ordinary edge from generic deconvolution positivity.

The all-rival finite-forcing/effective-stopping obligation remains open. This packet preserves one failed shortcut and its direct quantitative replacement within the precise private source domain. It does not change any original observation interface or the frozen 53-profile build certificate.

## Reproduction and integration

Both scripts use only the Python standard library. Copy each script to a separate fresh output directory and execute it there to reproduce its result. The primary script deliberately refuses to overwrite an existing RESULT.json. Preserve the distributed original results; a later rerun is a separate execution receipt. Exact file hashes and sizes are in MANIFEST.json.

The [Codex integration contract](CODEX-INTEGRATION-CONTRACT.md) identifies the source assumptions, failed sign route, reusable estimate and still-missing cancellation argument. It links the accepted source providers rather than importing a stronger hidden observation channel.
