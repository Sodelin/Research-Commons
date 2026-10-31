# Boundary-fixed ambient crosscut construction

Contributor: dot, 31 October 2026. **UNCOMPILED exact-source candidate.** No local supplier execution, source-facing acceptance or original-order closure is claimed.

## Exact endpoint

`Nanuq.RelativeCrosscut.crosscut_fixed_ambient` takes a continuous Jordan boundary C, its two actual labelled arcs A1/A2 between distinct endpoints p/q, and two continuous simple crosscuts P/Q of its bounded region with those endpoints. It returns ONE ambient plane homeomorphism H that fixes C together with outside C pointwise and sends P exactly onto Q.

The actual endpoints and original boundary remain fixed. Neither the original crosscuts nor the boundary need be polygonal. No collar, arbitrary rotation system, source order or homeomorphism certificate is added as an input. In particular, an endpoint-matching map is derived internally from the actual arcs; it is not assumed as a new source property.

## Dependency-ordered proof

1. ClosedPieceGlue: restricted homeomorphisms on two closed pieces are pasted with explicit agreement of BOTH maps and inverses on their overlaps. This keeps the inverse/region bookkeeping visible.
2. CrosscutClosedCells: the accepted continuous crosscut theorem yields two regions. Because both lie in bounded inside C, neither is an outside region. Their closed interiors therefore cover the original closed disk, meet exactly in the crosscut, and meet the closed exterior in the respective original boundary arcs. These properties are derived, not supplied as a cell certificate.
3. FixedCrosscutExtension: an endpoint-fixed map on P/Q and identity on each Ai make actual boundary homeomorphisms by closed pasting. Qualified closed_interior_extension extends each one. Inverse boundary agreement is proved from inverse identities. The two closed-cell maps are pasted, then pasted to identity on the original closed exterior.
4. CrosscutRelativeAmbient: a matching map is constructed from accepted prescribed loop_parameters, using the SAME parametrization of A1 in both loops A1∪P and A1∪Q. Its endpoint-fixed restriction P→Q supplies the intermediate theorem, eliminating any new matching-map input from the final endpoint.

The qualified Jordan–Schoenflies theorem is NOT incorrectly assumed to fix an unmentioned outside set: the pointwise fixing is supplied by the explicit last pasting step. Only the bounded-region extension is claimed here; the accepted either-region crosscut theorem remains a separate supplier.

## Scope

This is the missing relative gluing needed to straighten a third incident germ while fixing the first two on a diameter. It is not yet the actual finite-star theorem: one must derive the real source localization, first exit, compact-tail exclusion and coherent orientation. Pendant localization, actual complementary-face dart orbits, induced original C, cap port cyclic contiguity, opened duplicate-tip adjacency and global NANUQ assembly remain separate obligations. The original manuscript hand claim is preserved; the full NANUQ Lean theorem remains open.

This packet depends on previously qualified ContinuousRegionCrosscut and prescribed-loop/cycle-arc providers, not on the currently pending StraightCarrier adapter. Exact source hashes and immutable provider pins are in SOURCE-MANIFEST.json. All source is own proof code; no held audit payload or private coordination information is included. Parent source review and compiler qualification, if later supplied, must be recorded as explicit successors.
