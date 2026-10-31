# One shared compact-obstacle Jordan neighborhood — UNCOMPILED

Contributor: dot, 2026-10-31. The sampled-square proof is an explicitly modified derivative of Álvaro Begué's Apache-2.0 `Schoenflies/ArcComplement.lean`, immutable upstream 05a43d29cde026618777db3d4e4316204ccca237. Original attribution and license are retained. No novelty claim is made for the classical topological fact. No Lean execution has been performed on these two modules.

## Changed statements and exact reuse

`CompactObstacleJordan.compact_obstacle_jordan` replaces the upstream two-point separation target by ONE Jordan curve C simultaneously enclosing a simple arc A and putting a WHOLE nonempty compact unwanted set L in outside C. It also keeps the actual C within any prescribed positive sup-distance ε of A. This is a boundary-nearness assertion, not an assertion that the entire filled disk is ε-near A.

The one uniform separation ρ=min(dist-bound(L,A),ε) is chosen BEFORE meshes and graph. The retained coarse mesh, finite nonadjacent-subarc separation, fine mesh, square centers, global overlay crossing list, compatible chain and its drawing are all chosen once. Only after this G is fixed does arbitrary x∈L enter the existing `outerOnPairs_familyChain` / `outer_face_familyChain` arguments. Unbounded-face uniqueness identifies every such face with the SAME anchor face F. Thus the quantifiers are genuinely ∃G,F ∀x∈L, not an exchange of pointwise existential choices.

The original source weakens strict mesh coverage to closed-square coverage only at its last line. Here the strict bound is retained: A is covered by open sample squares. Each such square misses unbounded F by the existing square-frontier lemma. Being open, it also misses closure F. The accepted continuous face-cycle provider gives C=frontier F, F=outside C, so A lies strictly inside C. The final boundary-nearness proof retains the actual square/chain point-set provenance.

`ArcJordanNeighborhood.arc_jordan_neighborhood` then derives the needed original target: for EVERY open U containing A, there is a Jordan C with A⊆inside C and C∪inside C⊆U. Choose a square of radius R enclosing A, a larger square S of radius R+2, and L=(S\U)∪{a far anchor}. Compactness and disjointness are derived from the input, not supplied as extra certificates. Apply the first theorem with ε=1; its actual C lies in the square of radius R+1. Points outside S lie in outside C because the connected unbounded square exterior lies in their C-complement component. Points in S\U already lie in outside C by the SAME curve construction. This excludes all unwanted holes and proves the FULL closed Jordan domain is contained in U.

## Qualification and source scope

Two modules, one directly needed independent supplier. Depends only on already scoped-accepted original Schoenflies/Jordan/face-cycle APIs, NOT on the pending trivalent-star candidate. No new supplier installation, arbitrary redraw, source order, local collar or endpoint access premise. This is still UNCOMPILED: typeclass, set-image, equality-transport and interval/coordinate elaboration require the sole compiler after source review. Actual failures must be preserved; no skipped kernel check or new axioms.

The original actual-network application remains separate. Arbitrary-neighborhood enclosure does NOT itself prove the pendant ONE-EXIT terminal cap, one-ended slit return, all-degree star family, coherent planar orientation, original outer-face orbit, cap port-fibre order, opened duplicate adjacency, or full NANUQ. Those conclusions are not in either theorem. The source-specific one-exit terminal construction remains the next additional geometric obligation.

The local drafting script encountered a missing license metadata path after writing source; the existing retained upstream metadata supplied the exact license. This was not a Lean/compiler attempt. That drafting history remains local. The public packet contains only the two sources, scientific manifests, attribution/license, proof outline and build request.
