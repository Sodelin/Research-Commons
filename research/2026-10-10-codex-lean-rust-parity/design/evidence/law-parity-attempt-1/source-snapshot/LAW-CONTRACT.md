# Additive RC1 LAW contract

Contributor: Codex solver design role, 10 October 2026. Status: frozen executable contract; scientific source/physical-image admission remains gated. AFFINE/COUNT and CHART remain unchanged. Full obligations remain in [TRACEABILITY.md](TRACEABILITY.md).

This operation ports the actual supplied-source full joint terminal genealogy compiler in `research/2026-10-01-g7-continuous-design/law_compiler.py`. It maintains the entire correlated frontier distribution, performs original hybrid routing, composes exact ordinary-population forest kernels and completes the ancestral root. The output is the full joint rooted genealogy polynomial table and its root-suppressed unrooted split pushforward. It is a step toward fixed-source observation-law fitting; it does not recognize all sources, recover G5 targets from M3 calendar laws or compile the full joint calendar/bin law.

The inherited Python compiler is an attributed replay baseline. The new effective Lean implementation is the executable specification for Rust parity. The inherited G7/G6 theorems identify the intended source semantics, but their `Classical.choose` epoch tables and abstract `SelectedIndex` enumeration are not being extracted merely by translating their names. Effective frontier/carrier, source-program, observation-reader and physical-bank correspondences retain separate proof obligations.

## Request and carriers

Canonical ASCII/LF, exact natural/rational rules and the 65,536-byte request limit from [CONTRACT.md](CONTRACT.md) apply.

```text
RC1 LAW v e l h s stateCap termCap historyCap
MECHANISM COMMON
ROOT rootVertex
EDGE 0 sourceVertex targetVertex
... exactly e EDGE records ...
LEAF 0 vertex
... exactly l LEAF records ...
HYBRID 0 vertex incomingEdge0 incomingEdge1
... exactly h HYBRID records ...
SAMPLE 0 taxonId
... exactly s SAMPLE records ...
```

The other mechanism token is `INDEPENDENT`. It applies to every original hybrid in this request; a forced-route input is not part of v1. EDGE/LEAF/HYBRID structure and supplied incoming occurrence order use the same finite `RootedBinary` predicate and original IDs as CHART. There is no hidden planarity, cut-child or galledness restriction. Counts obey CHART graph limits, including `v+e+1+h≤32`; `1≤s≤4`. Sample records are ordered `0..s−1`, each attached to an original taxon ID `0..l−1`. Multiple distinct copied labels may attach to one taxon; declared taxa may be unsampled. Labels denote ordinary observed copied tips, not population or route labels.

Budgets are natural tokens: `stateCap≤4096`, `termCap≤65536`, `historyCap≤4096`. Zero caps are permitted and can yield UNKNOWN. The caps are conservative pre-generation work bounds defined below, rather than promises that a stored sparse table attains that size. No partial law is returned on exhaustion.

Trees are leaves `0..s−1`, or `(a,b)`. Every node orders its children by their distinct least copied-leaf ID. A forest is the list of its trees in increasing least-leaf order. Internally an empty forest is permitted on an unused edge. Canonical tree serialization has no spaces; for example `(0,(1,2))`. Every terminal rooted tree contains every copied label once. Canonical tables order tree strings by ascending ASCII bytes. Internal frontier states are vectors of exactly e forests, one per original edge ID, including empty forests. States compare lexicographically by their sequence of canonical forest strings (`[]`, `[0,(1,2)]`, and so on).

Polynomials have variable order `X:0,...,X:e−1,G:0,...,G:h−1`. A monomial is a vector of e+h natural exponents. Sparse terms combine equal exponent vectors by exact rational addition, delete exact zero coefficients and sort exponent vectors in ascending lexicographic order. Negative coefficients are legal. No floating approximation, tolerance deletion, factorization or proportional-row normalization enters serialization.

`X:eid` is the formal survival variable for the entire original edge occurrence. `G:hid` is the one shared original hybrid probability for its supplied incoming occurrence zero. Under physical evaluation, `X:eid=exp(−pairRate[eid]·(age[source]−age[target]))`; `G:hid=gamma[hid]`. There are no independent rowwise or per-locus copies. A formal polynomial table does not establish that arbitrary rational X probes lie on this correlated natural physical image. The ancestral rate cancels in infinite root completion, so no ancestral X variable is introduced.

## Exact compiler

1. Compute forward Kahn topological order, choosing the smallest ready vertex each time and updating each outgoing original edge occurrence in increasing edge ID. Process the resulting vertex list in reverse.
2. Begin with one empty frontier of polynomial weight 1. At a vertex, process input states in canonical state order. Collect copied labels sampled there and forests from its outgoing edge IDs, remove those frontier edges and canonicalize the collected live forest.
3. At an ordinary nonroot vertex, route this entire forest into its unique incoming original edge. At a hybrid, use its supplied incoming occurrence pair. COMMON has two routes, in order: all current roots to occurrence zero with factor G, then all to occurrence one with factor 1−G. The empty-forest COMMON routes still both occur and subsequently combine exactly. INDEPENDENT enumerates current-root bit vectors lexicographically, 0 before 1; its factor is `G^(number zero)·(1−G)^(number one)`. A previously merged tree is one current lineage; copied labels are not routed independently inside that tree.
4. For each routed population, compose the full ordinary forest kernel. For a starting forest with k current roots and an ending forest with j roots, count every ordered pair-merger history producing the ending forest. Its polynomial is that integer history count times

   `Σ[r=j..k] X^choose(r,2) / Π[t=j..k,t≠r](choose(t,2)−choose(r,2))`.

   An empty or one-root group has the identity kernel. Merge levels aggregate exact integer counts for identical canonical forests. At each level, unordered current-root pairs are enumerated by ascending pair of forest positions. Edge-kernel output forests are sorted canonically. Process hybrid incoming occurrence zero before one, and Cartesian kernel outputs lexicographically.
5. Multiply the incoming state polynomial, route polynomial and each edge-kernel polynomial; add contributions on identical new frontier states, normalize exactly and drop zero states. Kernel histories are reusable, but memoization cannot bypass a semantic budget check.
6. At the root, require that every other frontier edge has been consumed. Complete the live forest with the exact ancestral kernel: the probability of each completed tree is its ordered merger-history count divided by `Π[k=2..enteringRoots] choose(k,2)`. Add and normalize all rooted tree contributions.
7. Push the complete rooted table to root-suppressed unrooted nontrivial split signatures. For every rooted tree cluster D, retain the unordered cut `{D,allCopiedLabels\D}` only when both sides have at least two copied labels; deduplicate cuts. Order each side's copied labels numerically, order the two side vectors lexicographically, then order distinct cuts lexicographically. The wire key is `[]` for no cuts or `[[0,1]|[2,3];...]`. Add all trees with the same signature before normalization.

This is a joint frontier algorithm. Products of independently computed pair/triple marginals are not an alternative implementation. The route polynomial uses the original hybrid coordinate throughout the whole compilation. Infinite ancestral completion consumes the actual entering forest, rather than replacing it by independent pair completion events.

## Pre-generation budget order

At each vertex, first prepare its route/edge/root kernel branches in the canonical order above. This small preparation may stop on HISTORY before any polynomial expansion of the new frontier.

- HISTORY: before generating a merger level from F distinct forests with k>1 roots, require `F·choose(k,2)≤historyCap`. This is the raw next-level pair-merger contribution count before identical forests aggregate. Apply the same rule to edge kernels and root completion. Empty/one-root identity kernels require no merger level.
- STATE: once the kernels are prepared, compute the sum, over input states and routes, of the product of their edge-kernel output counts (at root, the root completion output count). Require this raw new-frontier/tree contribution count to be at most stateCap before constructing the new state table. It is not the smaller count after duplicates combine.
- TERM: for each such contribution, multiply the nonzero monomial counts of the incoming state polynomial, route polynomial and kernel polynomials. Sum these raw Cartesian monomial counts across contributions and require the result to be at most termCap before multiplying or adding their expanded polynomials. Root coefficients count as one nonzero term. Cancellation does not retroactively avoid this conservative cap.

HISTORY is checked first, then STATE, then TERM. Stop at the first failing condition. Every check uses arbitrary-precision natural counts and exact sparse term counts. A cache must apply the same semantic checks as an uncached execution. The signature pushforward only adds already-computed rooted polynomials; its raw input term count is at most the root-stage TERM work bound and adds no separate budget.

## Result

```text
RC1 RESULT LAW
BEGIN_REQUEST
<exact complete canonical LAW request bytes>
END_REQUEST
VARIABLES d X:0 ... X:e-1 G:0 ... G:h-1
GATE SOURCE_ADMISSION_NOT_ESTABLISHED
STATUS TABLE
ROOTED r
TREE canonicalTree termCount
TERM coefficient exponent0 ... exponent(d-1)
... each tree's nonzero terms ...
... exactly r TREE blocks ...
UNROOTED u
SPLIT canonicalSignature termCount
TERM coefficient exponent0 ... exponent(d-1)
... exactly u SPLIT blocks ...
END
```

Every polynomial is fully expanded and canonical. Output includes every nonzero rooted tree polynomial and every nonzero unrooted pushforward polynomial; there is no requested-subset table. Both full polynomial sums must equal constant 1 identically, and the unrooted table must equal the indicated rooted pushforward. Those identities are independent acceptance checks, not extra assumed source data.

A budget-limited result uses the same echo/VARIABLES/GATE prefix, then `STATUS UNKNOWN`, `LIMIT HISTORY|STATE|TERM vertexId required cap`, and `END`. It contains no partial law. If the **complete canonical TABLE response**, including request echo, VARIABLES/GATE, all tables and END, exceeds the shared 4 MiB result cap, use `LIMIT OUTPUT rootVertex requiredBytes 4194304` instead of publishing a truncated table. TABLE exits 0, UNKNOWN exits 2, and invalid/unsupported requests exit 1 with exact `RC1 ERROR INVALID_REQUEST` plus LF. Process failure is execution failure, not a mathematical NO.

The output establishes a finite computation of a formal supplied-source terminal genealogy table. It never promotes dynamic graph refinement, original source/class admission, chronological active-word coverage, natural physical survival image, whole-source census completeness, statistical confidence or biological accuracy. A symbolic table is not an admitted source fitting an observation vector.

## Acceptance and continuation

Actual Lean/Rust byte execution is required, including canonical coefficients/table/readout, both mechanisms, multiple copies at one taxon, unsampled taxa, original parallel edge occurrences and all budget branches. Normalize and relabel the inherited Python compiler's output before comparing every polynomial coefficient; Python repr order is not this wire convention. Include the known three-taxon species-tree formula `1−2X_internal/3` versus `X_internal/3,X_internal/3`, formal normalization, unrooted pushforward and ordinary kernel differential-equation identities. Preserve all prior binary/attempt receipts and run focused AFFINE/COUNT/CHART regressions after native changes.

The next semantic bridge is an effective frontier-to-actual selected-state/source-program proof, plus verified physical source/observation admission. The later G6 tagged-bin compiler requires complete ranked history/bin updates, literal source-word/active-calendar admission and initialization/ancestral-tail transport. LAW does not substitute a terminal genealogy marginal for that full joint observation contract.
