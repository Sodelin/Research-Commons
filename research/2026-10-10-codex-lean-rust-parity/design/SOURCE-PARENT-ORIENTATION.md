# Original-source parent probability correspondence

Contributor: Codex solver_design role, 10 October 2026. This records a source-binding obligation found while reviewing the next boundary consumer. Existing formal LAW parity remains valid; source admission remains false. Frozen wire definitions and implementations are unchanged.

The actual original source and LAW use opposite probability coordinates when their supplied parent orders agree:

| Carrier | Parent convention | Probability coordinate |
|---|---|---|
| [Original hybrid parents](../../2026-10-04-dot-complete-original-g1-1549z/src/G2LiveLineageRouting.lean) | `H.parent false = H.parent0`; `H.parent true = H.parent1` | This file's earlier rational illustrative `bitWeight` is a separate convention. |
| [Actual source coin measure](../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceForestPulseMeasure.lean) and [natural initialization](../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceNaturalInitialization.lean) | True chooses original parent1; the register is drawn once and reused by COMMON. | `gamma_original = P(true) = P(parent1)`; nonhybrid register bits are inert false in natural initialization. |
| [Original initialization polynomial](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7OriginalInitializationPolynomial.lean) | A true register contributes `X`; false contributes `1-X`. | The inherited polynomial evaluates `X` at `gamma_original`. |
| [Frozen LAW v1](LAW-CONTRACT.md) | Supplied incoming occurrence zero has factor `G`; occurrence one has `1-G`. | `G_LAW = P(occurrence zero)`. |

With wire occurrence zero mapped to `H.parent0` and one to `H.parent1`, the bridge must use **`G_LAW = 1-gamma_original`**. An explicit parent-order swap and register-bit relabelling is another possible transport, but every original edge occurrence and shared register must move consistently. Parallel edges remain distinct. Variable names alone do not establish this equality. A typed CHART coin interpreted as the inherited bank's `HybridProbabilities.gamma` also requires this complement before use in LAW under the same parent order; dynamic chart/source correspondence still has its own gate.

The next decisive fixture uses `gamma_original=1/3`, hence `G_LAW=2/3`, and reads the full original edge/register destinations. For two current roots at one hybrid, natural COMMON has all roots at parent0 with weight `2/3`, or all at parent1 with `1/3`. Conditional INDEPENDENT has routing-pattern weights `4/9, 2/9, 2/9, 1/9` in parent0/parent1 lexicographic order, while preserving the entering register. Include an opaque previously merged subtree so its copied leaves route together as one current root. Keep asymmetric original edge coordinates or the full labelled population view; fair probabilities and symmetric terminal observations can conceal an orientation error.

For fixed-register source rows, COMMON is deterministic: read the actual stored hybrid bit. LAW's marginal two-route mixture cannot replace that conditional row. Reuse the already-proved [original unranked boundary row independence](../../2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedActualBoundary.lean); the remaining obligations are native carrier/action correspondence, the explicit parent-probability transport, once-drawn initialization and original calendar/program integration. No actual boundary fixture comparison or universal source-law refinement is claimed here.
