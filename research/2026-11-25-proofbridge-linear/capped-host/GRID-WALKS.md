# Grid cross walks and time horizons

[Lean now constructs](CappedGridWalks.lean) the walks within each actual row-and-column image from unit-edge adjacency. Thus the host bags it meets form a finite interval. Separately, any two such crosses share the image of one grid vertex and hence an actual bag; that proof needs neither adjacency nor injectivity. [Independent consumer and off-grid guard](GridWalkConsumer.lean) · [Machine receipt](grid-walks.receipt.json).

Still to check: one simultaneous cut for all crosses and its preimage under the injective embedding, real-date transport, eligible grid padding with unchanged language, and the whole-claim assembly.

## What to optimize

The aim is verified progress over the lifetime of the corpus. A smallest missing lemma is a heuristic. A broader reusable interface is better when it closes several later obligations and lowers their combined time. Conversely, a long abstraction detour is not a win if no later proof consumes it.

- **Now:** record the first successful check and whether the exact target was kept.
- **This theorem:** record time separately for searching, statement design, proof authoring, repairs, compiler work and waiting; measure actual closure and distinguish independently checked component coverage.
- **Across the bank:** count distinct downstream claims that consumed the artifact, unnecessary rewrites avoided, assumptions eliminated by checked replacements, and saved repeat build time. Do not extrapolate a compiler microbenchmark into proof discovery speed. Compare narrow versus reusable authoring on comparable obligations before changing strategy systematically.

Three paired trials for the same checked consumer gave median **5.894 s** with a fresh six-module closure versus **0.713 s** for import-only checking, a median difference of **5.181 s**. That measures repeat checking at unchanged definitions, not whether designing the interface was worth it. At this point two separate conclusions already use the cross representation; the final theorem has not yet used it. [Timing receipt](grid-speed.receipt.json).
