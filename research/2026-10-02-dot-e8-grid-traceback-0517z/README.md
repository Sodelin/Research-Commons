# E8 finite-grid traceback-to-observable Lean bridge

Attribution: dot (OpenAI), research assistance for Nolan.
Conversation checkpoint: 2026-10-02 05:17 UTC. Execution-host clocks in raw receipts differ; source hashes and immutable attempt identities determine the compiled versions.

## Result and scope

Seven new proof modules and one aggregate import audit passed Lean 4.33.1 (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) with mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Two previously compiled strict-prefix/uniform-law prerequisites are included unchanged. The seven new modules print 29 theorem axiom audits, all limited to `propext`, `Classical.choice`, and `Quot.sound`; the aggregate independently imports the composed model and prints nine selected endpoints.

**This is a checked finite mathematical model bridge, not end-to-end PRISM executable correctness, not biological validation, not a new general sampling principle, and not an efficient arbitrary-class aggregation algorithm.**

Actual composition now checked:

1. Strict prefix selection has exact interval fibers and continuous-uniform branch probability `weight/total`.
2. A fixed arbitrary observable aggregates every branch in its fiber, including repeated labels.
3. Under uniform counting on the `N` exact midpoint grid points, a branch count is the difference of two ceiling cutoffs. Each branch error is at most `1/N`; branch-table total variation is at most `(b-1)/(2N)`.
4. Exact production contributions `factor × childPartition` induce the same continuous law, and their grid-selector fiber counts form a normalized finite branch table.
5. Finite-depth conditional products telescope to normalized derivation weights. A literal bijection from derivations to structures removes multiplicity and yields the weighted structure/class law.
6. Nonnegative normalized local kernels with local TV at most `epsilon` have depth-`d` trace TV and arbitrary observable-event error at most `d × epsilon`.
7. These components are composed, giving class-law bias at most `d × (b-1)/(2N)` for exact-real midpoint traceback within the explicit finite grammar model. At `N=2^52` this is `d × (b-1)/2^53`.

The last formula assumes uniform independent conditional grid draws, exact arithmetic, a common state/continuation graph, the given finite depth and production bound, exact contribution matching, and a literal source bijection/weight agreement. It does not independently establish those assumptions for the executable.

## Per-module prior-work and integration contracts

| Module | Established closest contract | What this implementation checks | Named source integration obligation |
|---|---|---|---|
| E8StrictPrefixSelector | Classical inverse-CDF sampling and finite cumulative weights; PRISM §2.1 stochastic traceback | Least **strict** crossing, nonzero selected weight, exact interval fiber | Match every executed categorical scan's term order and boundary convention |
| E8UniformPrefixLaw | Continuous-uniform inverse-CDF interval-length law; mathlib Lebesgue measure | Actual `volume.restrict [0,1)` branch probability | The executable has finite-grid input, so this is the ideal local law only |
| E8ObservablePrefixLaw | Standard measurable pushforward and finite disjoint-fiber summation | Measurability and class probability as the sum of all matching branch weights | Match the frozen executable observable, including label collisions |
| E8MidpointGridLaw | Elementary uniform-grid counting and floor/ceiling arithmetic, using mathlib's checked ceiling facts | Exact midpoint count formula and `1/N` branch error | Match `uniform_open52`'s exact-real idealization; admit/verify uniform engine words and floating calculations separately |
| E8MidpointGridTV | Classical finite total variation and cumulative-boundary accounting | `(b-1)/(2N)` local TV, including strict ties and zero weights | Establish the maximum executed production count and separate numerical local-kernel bias |
| E8FiniteTracebackLaw | PRISM §2.1/Ding–Lawrence partition-weight cancellation; CParty unambiguous weighted decomposition | Partitions are defined from productions; finite path products telescope; explicit source bijection yields class law | Encode actual reachable continuation stacks, prove exhaustive disjoint productions and exact Boltzmann factors |
| E8TracebackErrorComposition | Standard stochastic-kernel perturbation/data-processing argument | Local TV accumulates by finite depth; every arbitrary event gets the same error bound | Prove independent conditional inputs, common reachable states, and a genuine depth bound; certify numerical local errors |
| E8MidpointProductionKernel | Composition of the inverse-CDF and weighted-production contracts | Actual selector fibers give normalized production kernels with the grid TV bound | Identify each C++ production contribution with `factor × childPartition` |
| E8GridTracebackBridge | Composition of the preceding established contracts | Complete finite-model grid-to-weighted-class error theorem | Discharge the actual PRISM carrier, weights, classifier, numerical and RNG assumptions |
| E8SamplerBridgeAudit | Standard exact-source import/axiom audit | Nine composed endpoints import and print only standard axioms | This is an integration audit, not another domain theorem |

No exhaustive historical novelty search is implied by this table. Elementary arithmetic and generic pushforward/weighted grammar machinery are expressly treated as established. The value added here is exact compiler-checkable contracts and their composition for the source-specific implementation obligations.

## Primary sources

- [PRISM, WABI 2026 article 30](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30), §2.1: partition-contribution stochastic traceback and cancellation; §5: adaptive confidence and selected-class mass directions.
- [Ding and Lawrence, 2003](https://doi.org/10.1093/nar/gkg938): established RNA partition-function sampling architecture.
- [CParty, 2025](https://pmc.ncbi.nlm.nih.gov/articles/PMC11709253/): fixed-scaffold hierarchical density-2 partition function with ambiguity removal. Duplicate derivations cannot silently count as distinct structures when summing mass.
- [Voß, Giegerich and Rehmsmeier, 2006](https://pmc.ncbi.nlm.nih.gov/articles/PMC1479382/): existing exact shape-class mass machinery. The arbitrary observable aggregation theorem here does not establish the compositional inverse-image language needed by a fast selected-class grammar.
- [RapidShapes, 2010](https://pmc.ncbi.nlm.nih.gov/articles/PMC2828121/): established selected-shape matcher and residual-mass architecture. This batch supplies an upstream sampler/error model, not a new residual-mass principle or a density-2/L6 matcher implementation.
- [Pinned mathlib natural ceiling facts](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Floor/Ring.lean) and [Lebesgue interval measure](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean).

## Concrete implementation boundary

The checked PRISM source version motivating this work is commit `87a88715282d279fc361eb56de27153a321359be`. A separate local research adapter uses explicit seed handling, midpoint grid input, strict positive selection and a numerical recurrence-sum guard. **No private adapter code is included in this public batch.**

Next actual-source proof obligations:

- Model reachable `Sample_*` calls and their pending continuations. Nested grammar subcalls are represented by a continuation stack, not by pretending each C++ call is a one-child production.
- Prove termination/depth and production-count bounds on that carrier, including band states and all boundary cases.
- Prove emitted pairs/structures are exactly the fixed-sequence, fixed-scaffold admissible ensemble, with one derivation per structure and matching source energy/scaling conventions.
- Prove every forward contribution equals its corresponding traceback contribution; a tolerance guard passing is not that theorem.
- Prove the frozen L5/L6 classifier matches the mathematical observable. No automatic classifier-compositionality premise is adopted.
- Admit or independently justify the conditional random input law. A fixed pseudorandom seed is deterministic and does not itself give independent uniform draws.
- Bound floating normalization, exponentiation, subtraction and scanning errors. The exact midpoint theorem alone does not cover IEEE/long-double behavior.
- Combine the resulting law-error bound with an actually proved/admitted concentration event and certified confidence numerics. The downstream deterministic top-k/residual lemmas alone do not establish coverage.

## Replaying and auditing

`SOURCE-AND-COMPILE-MANIFEST.json` contains complete successful receipt records and exact SHA256 pins. Each `.lean`, `.log`, and `-receipt.json` triple is copied from its successful immutable attempt. The seven new sources plus both prerequisites form the replay set; compile them in the order listed above with their objects in `LEAN_PATH`, the pinned mathlib/dependency objects available, and `lean -j1 -M4096`. Then compile `E8SamplerBridgeAudit.lean`. No broad `import Mathlib` or costly certificate replay is needed.

The raw compiler receipts include the exact commands, bounded budgets, compile times, source/log/object hashes, direct project-import object hashes and stable-dependency checks. Receipt PASS statements apply to the precise source bytes, not arbitrary future edits.
