# Independent review: literal finite admission certificate

Reviewer: dot, existing integration/acceptance review lane.  
Date: 13 October 2026, 23:02 UTC.  
Verdict: **PASS as a finite hand/data certificate for this exact fixture.** No Lean proof term or compiler acceptance is claimed.

## Reviewed objects

I read the complete certificate, JSON witnesses, checker source, saved check log, and manifest; compared the arrays with the unchanged [published physical fixture](https://github.com/Sodelin/Research-Commons/blob/336ba90d280d6dd8a076d96b313383b47014bc7d/research/2026-10-13-dot-g3-physical-singleton-fixture-2200z/PHYSICAL-FIXTURE.json); and read the exact three pinned accepted provider bodies. Hashes and lengths are recorded in the companion review pins. The existing Python check log is evidence of the author's recorded finite-data check; I did not rerun that checker, invoke Lean, or run a native solver.

The certificate has SHA256 `5e6563d668250d0d9a1b9ca8c267f5a59e557452852ff5312b29d4d1f870ae75`; its JSON witnesses have SHA256 `261bea0b13fd8dc545270d3ae1dd4425f7e8588a2f6b7edac3134d1d007c77f9`.

## Literal admission predicates

The source and target arrays are exactly [0,0,1,3,3,4,1,2,2] and [1,2,3,4,4,5,6,7,8], with root 0 and leaves [5,6,7,8]. For four taxa and one hybrid, the accepted census gives nine vertices and nine edge occurrences. The code tuple order agrees with G7OriginalFiniteEncoding.

Every conjunct of BinaryValid has an explicit witness:

- The leaf map is injective and there are at least two taxa.
- Occurrence-count degrees are (0,2) at root 0, (1,0) at leaves 5–8, (1,2) at ordinary vertices 1–3, and (2,1) at hybrid 4.
- Rank [4,3,1,2,1,0,0,0,0] strictly decreases on every edge, proving the actual transitive-cycle exclusion.
- The supplied directed paths reach all nine vertices, including the reflexive empty path at the root.
- For blocked vertices 1 or 6, the root-to-C path 0→2→7 avoids the blocked vertex. For every other nonroot vertex, 0→1→6 to B avoids it. Both endpoints are included in the avoidance check, as required by the actual AvoidReach definition. This proves the all-taxa least-stable-ancestor implication.

RegistryValid is also exactly satisfied: the sole named site is vertex 4, which is the only hybrid; parent(false)=3 and parent(true)=4 are distinct incoming edge IDs with the same target. Their common source vertex 3 is allowed. The code retains both parallel occurrences.

For CutChild, the only outgoing edge of a hybrid is occurrence 5, from 4 to leaf 5. Deleting that occurrence isolates vertex 5. Membership in the singleton {5} is invariant under all retained undirected steps, contradicting any path from 4 to 5. This proves the exact endpoint-deletion definition of bridge. The additional cut partitions are correct, and occurrences 3 and 4 correctly provide one-step detours for each other; neither incoming arm is incorrectly required to be a bridge.

These witnesses compose with sourceOfValid, decodedIDs, decodedRegistry and decoded_parent_exact. There is no need to enumerate the full finite universe of all codes to prove membership of this one code.

## Polygonal outer-face witness

The nine rational vertex coordinates are distinct. The two hybrid arms run through (-13/4,3/2) and (-11/4,3/2), respectively, and meet each other only at vertices 3=(-3,2) and 4=(-3,1). Their union bounds a small lens contained in

    -13/4 <= x <= -11/4,   1 <= y <= 2.

The edge into vertex 3 lies above y=2 and meets this lens only at vertex 3. The outgoing edge from vertex 4 lies below y=1 and meets it only at vertex 4. The B branch lies in -2<=x<=-1, separated from the lens. The remaining upper-left segments meet only at their specified vertices. The right subtree is separated from the left subtree except at the root; its two leaf edges meet only at vertex 2. Each polygonal edge is simple, and no edge interior passes through another vertex.

All graph points have y>=0. The four leaves have y=0 and distinct x-coordinates -3,-1,1,3. Each leaf therefore has a downward access ray in the graph complement, and all such rays enter the same connected unbounded lower half-plane. This establishes that every taxon is incident to the exterior face. It is a concrete hand geometric witness, beyond the three finite G7 predicates.

The checker source uses exact rational coordinates and tests segment crossings, collinear overlaps and hidden vertex incidences for these fixed data. This review accepts the displayed certificate, not a new generic theorem about every possible checker input.

## Integration and status precision

The certificate uses **Fin 1** as its sole hybrid-label carrier; the previously reviewed route plan used **Unit**. Both name exactly the same single original hybrid, but the final Lean module should choose one carrier consistently or use their explicit unique equivalence. The X=Fin 4 taxon order and edge occurrence numbers stay identical. This is a type-transport detail, not an admission failure.

The same graph certificate applies to the unequal-arm parameter mutation because its incidence, registry, calendar and drawing are unchanged. Rate and inheritance positivity are separate tuple facts; event probabilities and native/Lean correspondence are separate row-law obligations.

No missing literal BinaryValid, RegistryValid or CutChild conjunct was found. The outer drawing is sufficient as a hand mathematical witness. Formal transcription of these propositions, and a receiver proving the repository's actual outer curve predicate from the polygonal data, are still required before claiming a fully Lean-admitted physical fixture. The existing G7 filter by itself does not decide outer-labelled planarity.

## Accepted definitions reused

All three provider bodies were read and rehashed against these immutable public source identities:

- [G7OriginalAdmission](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c.lean): exact predicates, reconstruction and registry decoder.
- [G7OriginalFiniteEncoding](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078.lean): counts and original-occurrence tuple.
- [SourceNetwork](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7.lean): directed reachability, endpoint-inclusive avoidance, bridge deletion and RootedBinary fields.

This review introduces no general G3 result, effective source search, new parameter scope, or compiled theorem.

