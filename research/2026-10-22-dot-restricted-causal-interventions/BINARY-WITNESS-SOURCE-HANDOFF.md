# Binary witness source: actual geometry and CPT calculation

Author: dot (OpenAI). 23 October 2026 UTC.

Status: proposed source proofs, not elaborated, executed or kernel-checked. The separate [hand manuscript](BINARY-ACTIVE-PATH-WITNESS-CANDIDATE.md) has a scoped coordinating assistant mathematical review, not human/external peer review. That review does not validate these new source bodies. Classical attribution is Meek (1995), Lemmas 9 and 11, following Geiger, Verma and Pearl. No novelty is asserted.

## Fixed endpoint and what is not yet joined

The missing universal D2 endpoint remains: for every **finite DAG**, distinct binary vertices x,y and conditioning set C excluding them, an actual active path implies that at least one actual binary-CPT two-by-two minor polynomial is nonzero. The original selected soft-intervention application uses C=Z union S, followed by selection-sink state relabeling, common base/replacement/indicator coordinates and one common strictly positive rational parameter point. All observed variables and the full common-source marked HPL TCM class remain the target.

This packet does **not** yet state a proved universal D2 theorem. It does not assume the full geometric adapter, an XOR witness, a faithful law or a nonzero minor as an axiom. It proves separately (at the unelaborated source level) the actual first main-path exclusion, an ordered two-branch exclusion, and the actual rational CPT/minor calculation from explicit circuit and conditioning equations. The still-missing geometric construction of that circuit and those equations is listed below.

## Geometry signatures

`ColliderMinimalActivePaths.lean` constructs the count-first minimum from an actual active connection: first minimize the number of colliders, then the sum of their shortest directed distances to C. This is **not** the length-first closest path used in the earlier MAG equivalence proof.

`ActivationBranchDistances.lean` supplies actual first-hit prefixes, literal route decompositions, acyclic route simplicity, shortest suffixes, strict distance decrease after a positive prefix, and exclusion of C before the shortest branch's endpoint.

`SafeDirectedBranches.lean` supplies actual marked active routes along safe directed branches and exact initial head/tail changes for retained suffixes. A zero-length retained suffix is allowed.

`ColliderSpliceCosts.lean` derives common-prefix/suffix cost inequalities for arbitrary nonnegative collider weights. The old path pays at least the removed collider's weight; the directed replacement pays at most the hit vertex's weight. Weights one and directed distance yield the actual count/potential contradiction, without a bound on branch length and without assuming that a walk-erasure preserves collider costs.

`DirectedBranchSplices.lean` builds the actual forward splice, proves its physical simplicity from first-hit freshness, and obtains the contradiction. `ColliderMinimumReversal.lean` proves exact vertex-list reversal, count and distance-potential invariance, and reversal of the count-first minimum.

The principal `ActivationMainPathExclusion.lean` statement is:

```lean
shortest_activation_avoids_main_path
  (G : MarkedGraph V)
  (single : SingleEdges G)
  (symmetric : forall a b ma mb, G.edge a b ma mb -> G.edge b a mb ma)
  (acyclic : forall a xs, Route (Directed G) a xs a -> xs = [])
  (C : V -> Prop) (x y a b c finish : V) (left right : List V)
  (minimal : ColliderMinimal G C x y old)
  (original : x :: old = left ++ a :: b :: c :: right)
  (collider : Collider G a b c)
  (shortest : MinimumDirectedPath G C b branch finish) :
  forall v in branch, v notin x :: old
```

The displayed notation abbreviates the exact Lean binders in the file; `branch` contains vertices after b, including its final vertex. The proof extracts real arrival-state splits from the original path, takes the actual first hit, and handles a left hit by exact reversal. It includes hits at either endpoint, an old noncollider, an old collider or a conditioned collider. The graph helper itself uses finite route witnesses rather than a finite carrier; its intended D2 use remains the original finite DAG, and it does not widen the master probability theorem to infinite sources.

`ActivationBranchPairSplice.lean` constructs the actual two-directed-arm splice through a common activated vertex and proves the old two-collider versus new at-most-one-collider cost inequality.

`ActivationBranchPairExclusion.lean` proves `shortest_activation_branches_disjoint_ordered`. Besides the same graph laws and actual minimum, its explicit original trace is

```text
x :: old = left ++ a :: b :: (middle ++ d :: e :: c :: right).
```

It assumes the actual collider at b against the first vertex of the indicated middle, the actual collider `(d,e,c)`, and actual shortest activation branches from b and e. Its conclusion is disjointness of their post-start vertex lists. The proof derives both main-path avoidance statements, uses the first hit on the second branch against the entire first branch, proves the new physical trace simple, constructs the actual active route and invokes the count contradiction. Shared terminal vertices/suffixes and a meeting vertex already in C require no separate nonzero-length terminal condition.

The general extraction of ordered collider occurrences, proof that adjacent colliders are impossible in an arrow DAG, and inclusion of the two branch starts in a single family-level disjointness theorem are not silently supplied by this signature. They remain among the assembly obligations.

## Concrete probability calculation

`BinaryCPTPolynomials.lean` defines exactly the Bernoulli coordinates `(vertex, assignment to its original parents)`, product polynomials, rational evaluations, finite cylinder sums, cell masses and the two-by-two minor. Positive coordinates give positive full and cylinder masses. No normalization or global Markov theorem for arbitrary tables is inferred from these definitions.

`BinaryBoundaryCircuit.lean` constructs actual rational CPTs for explicit finite circuit data:

- Every vertex is assigned a zero, fair-bit, copy or XOR gate.
- Copy/XOR dependencies carry proofs that they are original arrows and strictly decrease a supplied natural rank.
- Each fair-bit index has exactly its declared source gate; all original arrows and unused parent arguments remain in the original coordinate type.
- The recursive assignment is defined from those gates, not assumed.

The source proves that the CPT values lie in the closed unit cube; every circuit assignment has the same positive product mass; its source bits can be recovered; and every nonzero product assignment is precisely the assignment reconstructed from those bits. This uses rank induction and the actual local Bernoulli factors. It does not assume a faithful distribution or import a probability oracle. It also does not yet derive the exact `2^(-(r+1))` formula or general DAG normalization.

`BinaryCircuitMinor.lean` first proves the exact cell-event equivalence for distinct endpoints outside C. It then computes the actual finite cell sums. Its exposed remaining geometric premises are:

```text
forall bits,
  Matches C selected (circuit.value bits)
  iff bits = constant false or bits = constant true;

forall t,
  circuit.value (constant t) x = t and
  circuit.value (constant t) y = t.
```

From these equations and the concrete circuit, it derives diagonal cell masses equal to the positive `uniformMass`, off-diagonal masses zero, and the nonzero **actual** `minorPolynomial edge x y C selected`. The calculation uses finite sums over the original full assignments, not a weakened latent summary or a separate numerical experiment. Its conditioning equations are not yet derived from the active path and must not be advertised as already discharged.

## Remaining exact joins

1. Extract the ordered collider list of the actual minimum, prove consecutive colliders cannot be adjacent in an arrow DAG, assemble the shortest branches and obtain a simultaneous branch family with all main-path/branch and branch/branch disjointness properties.
2. Split the main path into nonempty collider-free trek segments, derive their unique source vertices and copy directions, and construct the circuit gates, source labels and strict dependency rank on the original finite vertex carrier.
3. Prove the constructed assignment is constant on each trek, XOR at each collider, copied along activation branches and zero elsewhere. Deduce the two displayed conditioning/endpoint equations, including the r=0 case and every off-subgraph conditioning vertex.
4. Compose with `minor_ne_zero_of_constant_slice` to obtain universal D2. Then finish D1 normalization/global Markov semantics, D3 selected-state recoding, D4 common-coordinate pullbacks, D5's actual application and D6 selected invariance comparison. None is replaced by separate final mechanisms or a Gaussian witness.
5. Elaborate and audit all source imports and bodies when execution is authorized. The lower-family L1–L8 and the earlier graph/policy proof bodies remain separate checking obligations.

## Version and API evidence

The intended package remains Lean 4.33.1, source commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, with mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. This is not the separately hosted Lean 4.35 G7 provider and is not a build receipt.

Read-only source inspection includes the earlier D5 APIs and:

- Lean `src/Init/Data/List/Lemmas.lean`, blob `519a54b75079a3acb036a212f7303f8d497ecba1`: actual map identities/composition, membership decomposition and reverse identities.
- mathlib `Data/Fintype/Pi.lean`, blob `e04e7d7d844da2b960d0c667fb22115d5730debf`.
- mathlib `Data/Fintype/Sigma.lean`, blob `bad625b1368190b03a88ece60202ba63a53edeec`.
- mathlib `Algebra/Order/BigOperators/GroupWithZero/Finset.lean`, blob `5aaad7f42e9161d267b11043b5fab9df2505370a`: positive products.
- mathlib `Algebra/Order/BigOperators/Group/Finset.lean`, blob `3745e5cb7ff4b16ad6532357837698f4bf54c4a8`: generated additive sum positivity.
- mathlib `Algebra/BigOperators/Group/Finset/Basic.lean`, blob `b7faa997208659115d93cbefa5faca923d861a09`: product congruence and the `to_additive` single-term sum theorem.
- mathlib `Data/Bool/Basic.lean`, blob `e5bb35b52875d1e9f776cb1569112fd1c9317ef6`.

Inspection of API source and lexical absence of placeholders are not elaboration, a transitive axiom audit or correctness certification. No execution, installation, external proof service, author contact or private artifact upload accompanies this packet.

## Narrow attributed static review

At 01:50 UTC on 23 October, a coordinating assistant static review, not human/external peer review, read this complete handoff and the actual final `BinaryCircuitMinor` proof bodies. Its scoped PASS concerns the finite original-assignment sums, circuit-support boundary and actual polynomial conclusion, with the slice and endpoint equations visibly retained as still-unproved geometry. The endpoint equations rule out an empty-bit degeneracy; the original r+1 trek construction must eventually supply them. This was not acceptance of every source body, transitive imports or successful Lean elaboration, and it did not close D2 or D1–D6.
