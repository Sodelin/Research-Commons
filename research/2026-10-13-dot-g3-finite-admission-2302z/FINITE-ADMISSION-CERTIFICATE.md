# Literal G7 admission certificate for the unchanged nine-vertex fixture

Author: dot, 13 October 2026. A finite hand certificate for transcription into the accepted source API. No compiler, native source job, or claim of Lean verification. The graph is the already [published four-taxon fixture](https://github.com/Sodelin/Research-Commons/blob/336ba90d280d6dd8a076d96b313383b47014bc7d/research/2026-10-13-dot-g3-physical-singleton-fixture-2200z/PHYSICAL-FIXTURE.json), SHA256 `7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba`. The unequal-arm mutation changes no graph data, so the same admission certificate applies to it.

## Exact code, with original occurrences retained

Use X=Fin 4 in order A,B,C,D and ID=Fin 1 naming `H:pendant-A`. The inherited functions give `vertexCount 4 1=9` and `edgeCount 4 1=9`. In the exact tuple order of `G7OriginalFiniteEncoding.Code X ID`, take:

- source array: [0,0,1,3,3,4,1,2,2];
- target array: [1,2,3,4,4,5,6,7,8];
- root: 0;
- leaf array: [5,6,7,8];
- hybrid-site array: [4];
- sole site's parent(false)=3 and parent(true)=4.

These are the original fixture indices, not freshly chosen quotient representatives. Parallel occurrences 3 and 4 remain distinct coordinates. The original labelled names are R,U_AB,U_CD,S_A,H_A,A,B,C,D in vertex order. `ADMISSION-WITNESSES.json` contains the exact arrays and every finite witness below.

## BinaryValid: all conjuncts

The four leaf values are distinct, so `Function.Injective (codeLeaf c)` holds; the taxon-cardinality condition is the literal inequality 2≤4. The degree fibres, counting occurrences rather than endpoint pairs, are:

| Vertex | Incoming edge IDs | Outgoing edge IDs | Degree |
|---:|---|---|---|
|0|empty|0,1|(0,2)|
|1|0|2,6|(1,2)|
|2|1|7,8|(1,2)|
|3|2|3,4|(1,2)|
|4|3,4|5|(2,1)|
|5|5|empty|(1,0)|
|6|6|empty|(1,0)|
|7|7|empty|(1,0)|
|8|8|empty|(1,0)|

Thus the root-degree and all leaf-degree conjuncts hold. The only nonroot, nonleaf vertices are 1,2,3,4. The first three satisfy the ordinary (1,2) alternative; vertex 4 satisfies `IsHybrid`. No other vertex is hybrid.

For `Acyclic`, use the integer rank vector [4,3,1,2,1,0,0,0,0]. Every original directed edge strictly decreases this rank. The decreases along edges 0,…,8 are [1,3,1,1,1,1,3,1,1]. Therefore a nonempty transitive sequence of `DStep` strictly decreases rank and cannot return to its initial vertex. This is the exact `SourceNetwork.Acyclic` condition, not merely a claim that the underlying undirected graph is a tree.

For `∀ a, DReach root a`, the following lists are directed edge-occurrence paths from 0:

| Endpoint | Edge path | Vertex path |
|---:|---|---|
|0|empty|[0]|
|1|[0]|[0,1]|
|2|[1]|[0,2]|
|3|[0,2]|[0,1,3]|
|4|[0,2,3]|[0,1,3,4]|
|5|[0,2,3,5]|[0,1,3,4,5]|
|6|[0,6]|[0,1,6]|
|7|[1,7]|[0,2,7]|
|8|[1,8]|[0,2,8]|

`DReach` is `Relation.ReflTransGen DStep`, so the empty root path is permitted. Each nonempty edge step is witnessed by its displayed original edge ID, with the source and target equalities given by the code arrays.

The final conjunct requires every vertex dominating all labelled leaves to equal root 0. Here `Dominates root a leaf` is the negation of `AvoidReach a root leaf`, and `AvoidReach` excludes the blocked vertex at both endpoints and every step. For each a≠0 give a counterexample leaf:

- For a=1 or a=6, use taxon C (leaf 7) and path [0,2,7], via edges [1,7]. Its endpoints and every vertex avoid a.
- For a=2,3,4,5,7 or 8, use taxon B (leaf 6) and path [0,1,6], via edges [0,6]. Again its endpoints and every vertex avoid a.

Hence each nonroot vertex fails to dominate at least one taxon, proving the exact LSA implication. In particular, no incorrect assertion that root is the only dominator of each individual leaf is needed. These witnesses prove every conjunct of `BinaryValid c`.

## RegistryValid: all five conjuncts

The site map from Fin 1 to vertex 4 is injective. Vertex 4 is hybrid by the degree table, and every hybrid is vertex 4, so the registry is complete and does not merely name a subset. The targets of edge occurrences 3 and 4 are both 4. The parent IDs are distinct because 3≠4 in Fin 9.

This is exactly `RegistryValid`: it requires distinct incoming edge IDs, not distinct parent vertices. The parallel parents have the same source vertex 3 and nevertheless satisfy the predicate. No additional nonparallel-parent assumption is present in the pinned definition.

## CutChild: the actual endpoint-deletion condition

`CutChild c` asks that every edge whose source is hybrid be a bridge. The only hybrid is 4 and its only outgoing edge is 5. Removing occurrence 5 isolates vertex 5: every retained edge has both endpoints in {0,1,2,3,4,6,7,8}. Thus the predicate “vertex is 5” is preserved across every retained undirected `UStep`, and hence across its reflexive-transitive closure. It is false at source(5)=4 and true at target(5)=5. Consequently `UReach (fun f => f≠5) 4 5` is impossible, exactly the negation defining `IsBridge 5`.

For completeness, the other bridge target-side components are:

| Deleted edge | Target-side vertices |
|---:|---|
|0|{1,3,4,5,6}|
|1|{2,7,8}|
|2|{3,4,5}|
|5|{5}|
|6|{6}|
|7|{7}|
|8|{8}|

Every retained edge stays on one side of its listed partition. Edges 3 and 4 are not bridges: each has the other occurrence as a one-step detour. CutChild does not require the incoming hybrid arms to be bridges. This avoids a possible erroneous strengthening of the predicate.

## Direct source reconstruction and efficient transcription

The three proved propositions are `BinaryValid c`, `CutChild c`, and `RegistryValid c`. Use the existing `sourceOfValid c hb` to construct the actual `RootedBinary`; use `decodedIDs c hb hr` and `decodedRegistry c hb hr` for the original hybrid registry. The accepted `decoded_parent_exact` supplies the parent-bit correspondence back to this code, so no new abstract admission or parent oracle is needed.

If membership in `registeredBinaryCutChildCodes` is wanted, combine the three literal proofs with `Finset.mem_univ` and `Finset.mem_filter`. Do not enumerate the enormous universe `allCodes` just to certify this one supplied graph. Finite cases on Fin 9, Fin 4 and Fin 1, together with the displayed paths and cut partitions, suffice. The code's degree fibres can be reduced directly. These are suggested proof components, not a report that any tactic or decoder has been executed on this fixture.

## What is outside these predicates

No literal G7 predicate listed above fails. However, `G7OriginalAdmission` explicitly does not implement outer-labelled planarity; `RootedBinary` also does not include a planar or galledness premise. The existing filter must not be described as complete original-class admission solely because its three predicates pass.

For this particular graph, a complete explicit outer-face witness is available separately. Place vertices at rational plane points:

`0=(0,4), 1=(-2,3), 2=(2,1), 3=(-3,2), 4=(-3,1), 5=(-3,0), 6=(-1,0), 7=(1,0), 8=(3,0)`.

Draw each edge as its straight segment except the parallel arms: draw edge 3 from vertex 3 through (-13/4,3/2) to vertex 4, and edge 4 from vertex 3 through (-11/4,3/2) to vertex 4. Distinct edge interiors are disjoint; the two arms bound a small lens. All edges lie in y≥0, with the four leaves on y=0 at distinct coordinates. Each leaf has a downward access ray into the same unbounded lower-half-plane component. Thus every taxon lies on the exterior face. This explicit polygonal drawing, retained in the JSON, supplies the hand geometric witness without appealing to a planarity oracle. A formal geometric receiver for it remains a separate transcription obligation.

The same rank vector, embedded into real ages, is the fixture's strict Calendar and the exact native height recursion. All edge durations are positive. Rates and inheritance satisfy the separately reviewed physical fixture; neither positivity nor observation probabilities is a conjunct of these graph admission predicates. This certificate establishes no source-law computation, generic recognition, finite source bound or new theorem about all input graphs.

## Immutable selected source pins

All definitions were read from the public accepted 1613 source store at commit `7239e89dea5caad68a54227cee3b44a7d9b96389`:

- [G7OriginalAdmission](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c.lean), SHA256 `16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c`, Git `fd5a34125dfcfaea621ac1682b54ed67abf3e11f`: `BinaryValid`, `CutChild`, `RegistryValid`, `sourceOfValid`, `decodedIDs`, `decodedRegistry`, `decoded_parent_exact`.
- [G7OriginalFiniteEncoding](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078.lean), SHA256 `30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078`, Git `d6bbe5119768eade69f15feeb53abecb5a9176fd`: exact counts and Code tuple order.
- [SourceNetwork](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7.lean), SHA256 `0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7`, Git `abb91b7ed9ad2ad960cb1ab6f8fbbdfc212f9cc0`: `DStep`, `DReach`, `Acyclic`, `AvoidReach`, `Dominates`, `IsBridge`, occurrence-count degrees and `RootedBinary`.
