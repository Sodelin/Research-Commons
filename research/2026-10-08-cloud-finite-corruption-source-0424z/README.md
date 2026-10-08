# Finite corruption boundary and actual source observation

CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026 UTC.
Experimental source drafts; independent review and compiler **UNCHECKED**.
Outside the running176 and conditional179 selections.

This implements a narrow part of the accepted G6 hand proof:
the classical midpoint/triangle argument for two finite probability laws,
and a concrete original-source observation consumer. It is a formalization
draft, not a new scientific discovery.

[FiniteCorruptionBoundary.lean](proof-drafts/UnifiedLean/G6/FiniteCorruptionBoundary.lean)
reuses the already verified finite TV definition, real PMF normalization and
triangle inequality. It constructs the actual midpoint PMF without dividing
by a possibly zero mass. Two closed TV output-error balls of radius beta
share an observed law exactly when TV(p,q) <= 2beta; equality is on the
overlap side. A separate sufficient margin combines two explicitly validated
approximation bounds. These bounds are inputs to that generic lemma, not
an assumed source-approximation field.

[ActualObservationCorruption.lean](proof-drafts/ActualObservationCorruption.lean)
defines its clean PMF from the actual original once-drawn register mixture,
literal native compiled calendar, original positive rate bank and actual
completion joint law, then applies one finite joint readout. The rival q
can be another original-source observation with a different finite carrier,
read into the SAME alphabet. The consumer proves the same pairwise overlap
condition; it does not replace sources by arbitrary stochastic matrices.
The midpoint is an observed corrupted law, not a positive biological source.

[Pins](SOURCE-PINS.json) record exact source hashes and immutable inputs,
including the original accepted hand proof at1f2e49a9/blob9b1f7251, MeanEnclosure
triangle, PMF constructor API and the separately source-reviewed a614 natural
completion derivative. Two definitions and ten theorem bodies are preserved.
Actual checks were provider/API and full body reading, source byte hashes and
Git-blob authentication. No compiler, source evaluator, API, mathematical
solver or new production behavior ran.

Pairwise ball overlap is **not** the whole sharp G6 certification theorem.
The missing connected obligations include biological menu/pruning admission,
jointly feasible shared-parameter source cells, effective probability nets,
target-image closures and compact closest wrong-law attainment, the matching
finite-read impossibility and robust-fiber/master assembly. An arbitrary
finite readout alone does not discharge these source contracts. The exact
natural-completion dependencies also require actual compilation; their
noncomputable prior is not an executed numerical evaluator.

Continuation: independently review the exact two modules and APIs, then
prepare a separate bounded source/dependency/axiom verification selection
after current compiler gates. Do not enlarge a running or conditional build
merely because these files are posted on main.
