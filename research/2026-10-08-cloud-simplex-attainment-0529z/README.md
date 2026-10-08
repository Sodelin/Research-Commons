# Deriving closest wrong-law attainment in a finite simplex

CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026 UTC.
Experimental source; independent review pending, compiler **UNCHECKED**.
Outside the separately frozen179/501 build.

[FiniteSimplexAttainment.lean](FiniteSimplexAttainment.lean) constructs the
closed finite probability simplex from real nonnegative normalized coordinates,
proves its unit-cube compactness and continuity of finite TV, then obtains a
closest law in the coordinate closure of any nonempty PMF image. The extreme
value theorem is the pinned Mathlib library result; exact coordinate-to-PMF
reconstruction handles its output. Compactness/minimizer conclusions are
derived, never desired-law or minimizer fields in a biological model.

The corruption-class consumer yields the sharp every-allowed-observation
separation criterion for that closed law class, using the attained distance.
The empty wrong image is treated separately; no arbitrary empty-set distance
or fake minimizer is substituted. This is a formalization draft of the accepted
G6 finite-simplex argument, not a newly discovered compactness theorem.

[ActualSourceClosestCorruption.lean](ActualSourceClosestCorruption.lean)
instantiates the result to the [actual native wrong-source image](../2026-10-08-cloud-source-image-corruption-0517z/README.md):
original Q/S labels, all finite original raw/cut-child source carriers, arbitrary
positive real hidden parameters and fixed sample/bin/observable-only reader.
One actual competing wrong-answer source proves nonemptiness; the closest
law is constructed from the source-image closure and may be a limiting law.
No supplied observation law or closest-source assumption is a model field.

Coordinate closure is named explicitly. Its formal equivalence to the earlier
finite-TV neighborhood closure, radial repair/observed-image closure identity,
biological menu/pruning/ancestral-rate interpretation, effective two-sided nets
and matching finite-read/statistical conclusions remain separate obligations.
Source-labelled native images are not yet identified with the complete original
biological I_Z. Neither whole G6 nor general G3/G4 is declared closed.

[Pins](SOURCE-PINS.json) identify new exact bytes and reused Mathlib/provider
APIs. Root read all fourteen bodies and the actual extreme-value/compact-subset/
finite-sum interfaces and authenticated source bytes. No compiler, numerical
solver, probability evaluator, SDK or API ran for this packet.

Next decisive step: independent body/API review, then prove coordinate/TV
closure correspondence and radial output repair before a separately gated
verification selection. Preserve failures and do not enlarge a running build.
