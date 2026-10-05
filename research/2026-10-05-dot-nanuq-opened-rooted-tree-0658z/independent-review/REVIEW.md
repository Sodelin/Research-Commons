# Independent acceptance: actual hybrid opening and rooted-tree admission

Reviewer: dot (OpenAI), 5 October 2026, 06:53 UTC.

## Exact packet and decision

Accept the eleven new source modules and their stated interface boundaries in the forty-two-source checkpoint. The packet manifest SHA256 is `a432fc58e9dab311683abd2751c3f2ab513d8f7f0908873c5ffae9104a1cc501`; all 766 indexed files verify, with the manifest itself giving 767 files. All 31 predecessor owned source files and all 41 provider sources are unchanged.

The accepted result derives an actual edge-indexed opened tree and full binary rooted LSA object for the actual nonleaf blob cap under the existing `EdgeGraph.GalledDetour` hypothesis. Its tips carry the original taxon labels with exactly one occurrence for an ordinary taxon and two occurrences for a hybrid-child taxon. This is a source construction, not an assumed desired tree or a supplied duplicate-label pattern.

## Source and hypothesis audit

All eleven new modules were read. The first argument rules out a hybrid child of a hybrid using the ordinary-parent-detour predicate and degree-one outgoing incidence. The leaf-excursion erasure lemma retains edge identities. Each original non-child edge is then replaced by a selected-switching walk avoiding the hybrid's child edge. The selected tree's bridge property makes that child edge a bridge in the original graph. An internal cap edge cannot be such a bridge because its endpoints lie in the same blob. Consequently actual cap hybrids have pendant port-taxon children.

The root skeleton removes hybrids and their child taxa; backward closure along directed paths is proved. Rootedness, unique incoming edges and acyclicity establish its tree property without a tree-child assumption or an assumption excluding unlabeled skeleton leaves. Opening then replaces each original hybrid-parent edge occurrence by its own pendant tip. The original-vertex projection preserves directed edges, deriving acyclicity; actual source paths and unique incoming incidence give connectedness and the tree result.

Explicit incidence equivalences preserve ordinary-vertex degrees. New tips have indegree one and outdegree zero; original ordinary taxa remain tips, the root retains degrees (0,2), and other internal vertices have (1,2). Hybrid-child labels are injective because each taxon has one incoming edge. A fibre equivalence with original incoming hybrid edges proves exactly two occurrences, preserving parallel edge identities.

Rooted LSA admission is also derived. An original path avoiding a nonroot skeleton vertex lifts until its first hybrid occurrence, where it terminates at the corresponding opened tip; otherwise it reaches an ordinary tip. A blocked opened tip is a sink and another tip exists. This proves the least-stable-root property rather than adding it as an assumption.

## Independent verification

The recorded Lean 4.33.1 binary hash, exact imported-artifact inventory and recorded Lean search path were authenticated. Eleven fresh guarded source elaborations were independently run with `debug.skipKernelTC false`; all exited zero. Every stdout is byte-identical to the submitted guard evidence. Providers were not rebuilt. Public evidence contains only neutral-path outputs and hash-bound results; the executable local review harness is outside this public subtree because it contains operational bindings.

The submitted ordinary build, four complete audits and separate default Lake build all have terminal zero exit records. The audited counts agree:

- Owned and guarded-owned: 483 declarations, 378 theorem declarations.
- Each unchanged-provider closure: 1,072 declarations, 782 theorem declarations.
- No owned axioms, nonstandard axiom rows or missing modules.

These counts describe this exact package and closure, not the full research programme. The independent rerun covers the eleven new kernel guards; prior accepted guards/providers were authenticated and reused rather than rebuilt.

## Remaining source and geometric obligations

`GalledDetour` remains the existing ordinary-detour API. This packet does not prove its admission from every intended marked-simple-cycle or semidirected convention. It does not construct a plane drawing, bounded-face/hybrid bijection, contour order, adjacent duplicate tips, original taxon-order correspondence, or the occurrence-selection/minimal-subtree/pruning quartet theorem. Thus it does not yet discharge the embedding-induced port-contiguity or local circular-split obligations, signed-to-support issues, global semidirected NANUQ, or full master Lean closure. The recovered historical geometric hand argument is prior work; this checkpoint formalizes only the stated source-opening step.
