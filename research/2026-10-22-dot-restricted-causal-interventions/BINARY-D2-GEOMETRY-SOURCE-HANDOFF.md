# Actual finite binary-DAG minor: geometry-to-circuit source join

Author: dot (OpenAI), 2026-10-23.

Status: **source-only candidate; never elaborated or executed**. This packet
composes the earlier hand-reviewed binary witness and published v48 circuit
calculation into an actual finite-DAG source theorem. It is not a Lean
certificate, a transitive correctness audit, or completion of D1--D6.

The subsequent [physical-upper source composition](BINARY-PHYSICAL-UPPER-SOURCE-HANDOFF.md)
now supplies proposed bodies for the remaining elementary probability-law
and original-source/game joins. It is preserved with this geometry packet
in one atomic source update. Both layers remain unelaborated; no earlier
hand or static component review is promoted to full-chain acceptance.

Classical attribution: the mathematical supplier is finite discrete atomic
completeness, developed by Geiger, Verma and Pearl and used constructively
by Meek (1995), Lemmas 9 and 11. No independent novelty is asserted.
The complete hand proof, primary-source comparison and earlier review
limits remain in `BINARY-ACTIVE-PATH-WITNESS-CANDIDATE.md` and
`DISCRETE-FAITHFULNESS-PROVIDER-ASSESSMENT.md`.

## Exact exposed theorem

`lean/BinaryActivePathMinor.lean` ends with:

```lean
theorem binary_active_path_minor_nonzero
    {V : Type u} [Fintype V] [DecidableEq V]
    (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = [])
    (x y : V) (C : Finset V)
    (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (connected : ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y) :
    BinaryCPT.minorPolynomial D x y C (fun _ => false) ≠ 0
```

`Route D` is the existing finite original-arrow route relation. Acyclicity
excludes every nonempty closed such route. `ActiveConnection` is the
existing arrival-state active connection with actual collider ancestry;
its conversion to a simple vertex path is an imported proof dependency,
not an additional premise. The conclusion is the original binary CPT
polynomial `m00*m11 - m01*m10`, with each cell summing over **all** complete
assignments of the original finite vertex carrier. CPT coordinates are
the original vertex/complete-parent-assignment pairs. No arrow is deleted.

The zero conditioning assignment is the specific boundary witness slice.
It is not a claim about an arbitrary selection-state slice. The witness
uses fair random source tables and deterministic copy/XOR/zero tables;
it is **not** an entirely Boolean CPT corner. The later positive rational
cube argument is a separate construction.

## What is derived, rather than assumed

1. A collider-count-first, then activation-distance-minimum actual path.
2. An actual shortest directed branch from each collider to C, including
   zero-length branches when the collider itself is conditioned.
3. Every positive branch vertex avoids the main path; distinct full
   branches, including their start colliders, are disjoint. The two
   oriented splice lemmas are composed using literal occurrence ordering.
4. Each main noncollider has at most one main-path incoming original
   arrow. Every parent on such an edge is also a main noncollider.
5. A strict natural rank for **every original arrow**, by maximizing
   incoming finite route length and bounding it with the finite vertex
   cardinality. No topological-sort or rank premise is added.
6. Fair indices are the actual main-path noncollider vertices with no
   incoming main edge. All other ordinary vertices copy their unique
   main parent, colliders XOR their two original main parents, positive
   branch vertices copy their unique branch predecessor, and all other
   vertices are pinned to zero. Unused original parents are ignored by
   these tables, not removed from the source DAG.
7. Every fair index is its own actual source vertex; every such source
   lies on the main path outside its colliders. There are no unused fair
   indices. Each collider-deleted main-path component has exactly one
   such source. Singleton components require no exceptional premise.
8. Conditioning at zero propagates back along each actual copy branch,
   forces each collider XOR to zero, and, with ordinary copy equations,
   forces **all** source bits to agree. The converse is also derived:
   constant source bits make every conditioned coordinate zero, including
   off-subgraph coordinates. Constant bits propagate to both endpoints.
9. The v48 actual finite-assignment sum calculation then gives two equal
   positive diagonal masses and zero off-diagonal masses. This proves the
   displayed original minor is a nonzero polynomial.

The proof needs positivity of the circuit's uniform product mass, not an
extracted numbering of components or the exact exponent `2^(-(r+1))`.
That exact count remains a separate optional statement. The source-index
subtype does not weaken the polynomial conclusion. A separate theorem
also derives that this subtype is nonempty from the endpoint equations.

## New source modules and direct dependencies

- `BinaryTrekDecomposition`: actual directed-arm decomposition and unique
  source of a collider-free simple original path; singleton included.
- `FiniteDAGRank`: original acyclic-route simplicity, cardinality bound,
  maximum incoming route length and strict rank on all original arrows.
- `BinaryPathConstraintPropagation`: literal adjacent/triple equations,
  all-source-bit propagation, copy-route and constant-copy-region facts.
- `BinaryTraceIncidence`: actual consecutive/triple occurrences; unique
  predecessor/successor, main-parent uniqueness and collider isolation,
  endpoint status and ordered distinct collider occurrences.
- `BinaryActivationFamily`: constructs the actual shortest branch family
  and joins the two oriented exclusions into full pairwise disjointness.
- `BinaryWitnessCircuit`: concrete gate choice, derived ranks, actual
  fair-source subtype, copy/XOR gate equations and branch-copy routes.
- `BinaryActivePathMinor`: proves both directions of the complete slice,
  both endpoint equations and the universal finite-DAG minor theorem.
- `BinaryTrekSourceAlignment`: exactly one actual fair source in each
  collider-deleted main-path component, and endpoint copying from it.

The main theorem imports the first seven modules and published v48
components. The eighth checks the requested component/source alignment;
it is not an extra premise of the main theorem. Imported v48 obligations
include the full collider-count/potential splice proofs, active-route to
simple-path conversion, finite CPT polynomial evaluation, circuit support
and finite-sum calculations. No claim of their successful elaboration or
complete transitive static validation is made by this handoff.

## Pin, inspection and remaining verification boundary

Package toolchain stays Lean 4.33.1 and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. The incoming-route cardinality
step inspected `Mathlib/Data/Fintype/Card.lean` at that exact pin, blob
`882bcfa5829eca220faf26d0bee76bf2f055558f`, specifically
`List.Nodup.length_le_card`. The list equality/append/reverse APIs were
read at Lean source commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`src/Init/Data/List/Lemmas.lean`, blob
`519a54b75079a3acb036a212f7303f8d497ecba1`. Other v48 probability API
pins remain recorded in its handoff. No hosted 4.35 evidence is inherited.

All new code is unelaborated. Dependent pattern matching, proof-dependent
gate equations, list-recursion tactic behavior and imports still require
actual compiler checking when authorized. A lexical absence of `sorry`
or `axiom` is not an axiom audit or a proof certificate.

## What this does not close

- D1: normalization of the arbitrary original binary DAG law, global
  Markov soundness and the selected-law factorization join.
- D3: transport of boundary witnesses to the fixed positive selection
  state by complementing sink outputs, with its exact polynomial map.
- D4: injective per-regime coordinate embeddings into **one** common
  baseline/replacement/indicator parameter registry, preserving shared
  mechanisms and the named degree-one intervention indicators.
- D5 application: the existing nonzero-polynomial avoidance proof must
  be applied only after all required minors are established on that same
  registry. Its positive rational point is distinct from these boundary
  evaluations.
- D6: the selected conditional-invariance/probability-oracle equivalence
  and the full original soft-intervention model/game identification join.

Thus the public selected-MAG/TCM target, common-source quantifiers,
faithfulness dependence and elementary-query budget are unchanged.
No statistical sample, hard-intervention, intervention-count, full-law
query-complexity, executable-policy or full Lean-verification claim follows.

## Review attribution

The earlier complete hand binary-witness proof received a scoped
coordinating assistant mathematical review, not human/external peer
review. The v48 circuit/minor source received only the previously recorded
narrow static boundary inspection. This **new joined source packet has
not yet received a coordinating review** at the time of writing. Any
later inspection must state its exact boundary and cannot stand in for
compiler or transitive proof-body validation.
